"""Certificates that the kernel backend finds for the word `V` over pairs, and that Lean checks (`pfarkas`).

A goal `L <= R` (or `<`) over pairs, with hypotheses, is closed by `pfarkas [c_1 * f_1, ...]`: the facts `f_j`, each
`0 <= F_j` (or `<`, or a tie `F_j = 0`), taken `c_j > 0` times, leave `R - L - sum c_j F_j` a polynomial with
nonnegative coefficients in the masses (a constant, most often). Lean checks that identity in the masses of the
components, which is one linear combination (`farkas`): the search is here, the check is not.

The pool of facts: the hypotheses; the bounds of the words read by relation (`a <= max(a, b)`, ...); the ties
(either way round), also times one atom; and the products of two inequalities. The multipliers come from an exact
LP (`qpp.simplex.lp_min`): nonnegative `c_j` and slack coefficients `s_M` on the monomials of the masses, one equation
per monomial, the least sum of the `c_j`.
"""
import re
import sys
from fractions import Fraction as F
from itertools import combinations_with_replacement
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
from .simplex import lp_min  # noqa: E402


# ---------------------------------------------------------------------------------------------------- polynomials

class Poly:
    """a polynomial over Q in named atoms: {monomial: coefficient}, a monomial a sorted tuple of (atom, exponent)"""

    def __init__(self, terms=None):
        self.t = {m: F(c) for m, c in (terms or {}).items() if c != 0}

    @staticmethod
    def const(c):
        return Poly({(): F(c)})

    @staticmethod
    def atom(a):
        return Poly({((a, 1),): F(1)})

    def __add__(self, o):
        t = dict(self.t)
        for m, c in o.t.items():
            t[m] = t.get(m, F(0)) + c
        return Poly(t)

    def __neg__(self):
        return Poly({m: -c for m, c in self.t.items()})

    def __sub__(self, o):
        return self + (-o)

    def scale(self, c):
        return Poly({m: c * v for m, v in self.t.items()})

    def __mul__(self, o):
        t = {}
        for m1, c1 in self.t.items():
            for m2, c2 in o.t.items():
                d = dict(m1)
                for a, e in m2:
                    d[a] = d.get(a, 0) + e
                m = tuple(sorted((a, e) for a, e in d.items() if e != 0))
                t[m] = t.get(m, F(0)) + c1 * c2
        return Poly(t)

    def pow(self, n):
        r = Poly.const(1)
        for _ in range(n):
            r = r * self
        return r

    def atoms(self):
        return {a for m in self.t for a, _ in m}

    def coeffs_in(self, a):
        """{k: the coefficient of a^k}, polynomials free of a"""
        out = {}
        for m, c in self.t.items():
            k = dict(m).get(a, 0)
            rest = tuple((x, e) for x, e in m if x != a)
            out.setdefault(k, Poly())
            out[k] = out[k] + Poly({rest: c})
        return out

    def subst(self, a, p):
        """the polynomial with the atom a replaced by the polynomial p, and the quotient q with
        self - result = (a - p) q"""
        res, q = Poly(), Poly()
        for k, fk in self.coeffs_in(a).items():
            res = res + fk * p.pow(k)
            # a^k - p^k = (a - p) sum_{i<k} a^i p^(k-1-i)
            for i in range(k):
                q = q + fk * Poly.atom(a).pow(i) * p.pow(k - 1 - i)
        return res, q

    def __repr__(self):
        return " + ".join(f"{c}*{'*'.join(f'{a}^{e}' for a, e in m) or '1'}" for m, c in self.t.items()) or "0"


# ---------------------------------------------------------------------------------------------------------- facts

class Fact:
    """`0 <= poly` (ge), `0 < poly` (gt) or `poly = 0` (eq), with the Lean term of its proof: an inequality
    `a <= b` or `a < b`, or a tie `a.Tie b`, of pairs, with poly = b - a in each case (farkas and qeq take a tie
    `a = b` the way they take `a <= b`; `.symm` the other way round)"""

    def __init__(self, poly, kind, lean, ineq_form=True, pair=True):
        self.poly, self.kind, self.lean, self.pair = poly, kind, lean, pair
        # the proof term proves `a <= b` (True) or `0 <= poly` as `level <= ...` (False): both feed farkas
        self.ineq_form = ineq_form

    def nonneg(self):
        """a Lean proof of `level <= P` with P of value poly"""
        if not self.ineq_form:
            return self.lean
        return f"(Bal.sub_nonneg{'_of_lt' if self.kind == 'gt' else ''} {self.lean})"


MASSES = set()  # the atoms that are masses (positive), in the search at hand


def mass_lean(c, m):
    """a Lean term of masses: c times the monomial m of mass atoms (exponents of either sign)"""
    num = [mass_num(F(c).numerator)] if F(c).numerator != 1 else []
    den = [str(F(c).denominator)] if F(c).denominator != 1 else []
    for a, e in m:
        (num if e > 0 else den).extend([a if " " not in a else f"({a})"] * abs(e))
    n = " * ".join(num) or "1"
    return f"({n} / ({' * '.join(den)}) : Mass)" if den else f"({n} : Mass)"


def poly_lean(p):
    """a Lean term of pairs with the value of p: the atoms are Lean terms of pairs, or masses (MASSES), which go
    into the coefficient"""
    def mono(m):
        fs = []
        for a, e in m:
            fs += [a if " " not in a else f"({a})"] * e
        return " * ".join(fs)
    parts = []
    for m, c in sorted(p.t.items()):
        mag = abs(c)
        ms = tuple((a, e) for a, e in m if a in MASSES)
        m = tuple((a, e) for a, e in m if a not in MASSES)
        coef = f"Bal.of {mass_lean(mag, ms) if ms else mass_num(mag)}"
        t = coef if not m else mono(m) if mag == 1 and not ms else f"{coef} * {mono(m)}"
        parts.append(t if c > 0 else f"Bal.swap ({t})")
    return " + ".join(parts) if parts else "Bal.level"


def eliminate(p, ties):
    """p with the definitions `c := t` substituted, the last one first, and {hypothesis: Q} with
    p - result = sum (c - t) Q over the definitions"""
    out = {}
    for h, a, t in reversed(ties):
        p, q = p.subst(a, t)
        if q.t:
            out[h] = q
    return p, out


def derived_ties(facts, defs):
    """the ties `P = 0` of two facts `0 <= P` and `0 <= -P`, named hd1, hd2, ...; defs[name]: the `have` that
    proves it (`Bal.tie_of_le_le`), to put before the lines that use it"""
    ineq = [f for f in facts if f.kind == "ge" and f.pair]
    out, seen = [], set()
    for i, f in enumerate(ineq):
        for g in ineq[i + 1:]:
            if (f.poly + g.poly).t:
                continue
            key = tuple(sorted(f.poly.t.items()))
            if key in seen:
                continue
            seen.add(key)
            # `P <= 0` from g (0 <= -P) and `0 <= P` from f: the tie of P and 0, as `Bal.Tie P level`
            pl = poly_lean(f.poly)
            name = f"hd{len(defs) + 1}"
            le = f"(by have hw := {g.nonneg()}; pfarkas [hw] : {pl} \u2264 Bal.level)"
            ge = f"(by have hw := {f.nonneg()}; pfarkas [hw] : Bal.level \u2264 {pl})"
            defs[name] = f"have {name} := Bal.tie_of_le_le {le} {ge}"
            out.append(Fact(-f.poly, "eq", name))
    return out


def with_defs(lines, defs):
    """the `have`s of the derived facts that the lines use (and those they use), in their order, then the lines"""
    need, text = set(), "\n".join(lines)
    for n in reversed(list(defs)):
        if re.search(rf"\b{n}\b", text) or any(re.search(rf"\b{n}\b", defs[m]) for m in need):
            need.add(n)
    out = []
    for n, d in defs.items():
        if n in need:
            out += d.split("\n")  # a have may span lines (its proof below it, indented)
    return out + lines


def products(facts, atoms):
    """the products of two inequalities, the squares of the atoms, and the ties times one or two pair atoms"""
    ineq = [f for f in facts if f.kind in ("ge", "gt") and f.pair]
    out = []
    for f, g in combinations_with_replacement(ineq, 2):
        out.append(Fact(f.poly * g.poly, "ge", f"(Bal.mul_nonneg {f.nonneg()} {g.nonneg()})", ineq_form=False))
    for a, lean_a in atoms:
        out.append(Fact(Poly.atom(a) * Poly.atom(a), "ge", f"(Bal.sq_nonneg {lean_a})", ineq_form=False))
    for f in [f for f in facts if f.kind == "eq" and f.pair]:
        for a, lean_a in atoms:
            fa = Fact(f.poly * Poly.atom(a), "eq", f"(Bal.tie_mul {f.lean} {lean_a})")
            out.append(fa)
            for b, lean_b in atoms:
                if b >= a:
                    out.append(Fact(fa.poly * Poly.atom(b), "eq", f"(Bal.tie_mul {fa.lean} {lean_b})"))
    return out


class Mult:
    """a multiplier: a positive rational times a monomial of masses (mono: a monomial, () for 1)"""

    def __init__(self, c, mono=()):
        self.c, self.mono = F(c), mono

    def poly(self):
        return Poly({self.mono: self.c})

    def lean(self):
        return mass_lean(self.c, self.mono) if self.mono else mass_num(self.c)

    def __eq__(self, o):
        return isinstance(o, (int, F)) and not self.mono and self.c == o or \
            isinstance(o, Mult) and (self.c, self.mono) == (o.c, o.mono)

    def __hash__(self):
        return hash((self.c, self.mono))


def scales(target, positive, facts=()):
    """the monomials of masses that may multiply a fact: 1, the mass parts of the monomials of the target, and each
    mass of the facts and its inverse"""
    out = {()}
    for m in target.t:
        ms = tuple((a, e) for a, e in m if a in positive)
        if ms:
            out.add(ms)
    for f in facts:
        for m in f.poly.t:
            for a, e in m:
                if a in positive:
                    out |= {((a, 1),), ((a, -1),)}
    return sorted(out)


def find(target, facts, positive, strict, exact=False):
    """multipliers [(Mult, fact, flipped)] with target - sum c * fact.poly a polynomial with nonnegative coefficients
    in the positive atoms (and positive constant part, or a strict fact used, if strict; zero if exact); a
    multiplier is a positive constant times a monomial of masses (scales); None if there are none"""
    cols = []  # (fact, sign, monomial of masses): sign -1 for a tie used the other way round
    for mu in scales(target, positive, [f for f in facts if f.ineq_form and f.kind != "eq" or f.kind == "eq"]):
        for f in facts:
            cols.append((f, 1, mu))
            if f.kind == "eq":
                cols.append((f, -1, mu))
    monos = set(target.t)
    for f, _, mu in cols:
        monos |= set((f.poly * Poly({mu: 1})).t)
    slack = [] if exact else sorted(m for m in monos if all(a in positive for a, _ in m))
    monos = sorted(monos)
    n = len(cols) + len(slack)
    eq_rows = []
    prods = [(f.poly * Poly({mu: 1})).t for f, _, mu in cols]
    for m in monos:
        row = [pt.get(m, F(0)) * s for pt, (f, s, mu) in zip(prods, cols)]
        row += [F(1) if m == sm else F(0) for sm in slack]
        eq_rows.append((row, target.t.get(m, F(0))))
    ge_rows = [([F(1) if i == j else F(0) for i in range(n)], F(0)) for j in range(n)]
    if strict:
        row = [F(1) if f.kind == "gt" else F(0) for f, _, _ in cols] + [F(1) if sm == () else F(0) for sm in slack]
        ge_rows.append((row, F(1)))
    cost = [F(1)] * len(cols) + [F(0)] * len(slack)
    res = lp_min(cost, ge=ge_rows, eq=eq_rows, k=n)
    if res.status != "optimal":
        return None
    out = []
    for (f, s, mu), c in zip(cols, res.x[:len(cols)]):
        if c != 0:
            out.append((Mult(c, mu), f, s < 0))
    return out


def mass_num(c):
    c = F(c)
    return f"({c.numerator} : Mass)" if c.denominator == 1 else f"({c.numerator} / {c.denominator} : Mass)"


def farkas_args(cert, haves):
    """the arguments of pfarkas for a certificate; the facts that are not hypotheses become `have`s"""
    args = []
    for c, f, flipped in cert:
        name = f.lean
        if not f.lean.isidentifier() or f.lean.startswith("("):
            name = f"hv{len(haves) + 1}"
            haves.append(f"have {name} := {f.lean}")
        if flipped:
            name = f"({name}).symm"
        c = c if isinstance(c, Mult) else Mult(c)
        args.append(name if c == 1 else f"{c.lean()} \u2022 {name}")
    return args
