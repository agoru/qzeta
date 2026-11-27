"""progcert: the exact arithmetic of the proof word `prog[PRICES; POINTS]` of the atom `prog(DECLS, ROWS : COST) = P`.

The data of a program are terms in its parameters: rational functions over Q in the names of the given, here
`RF` (a numerator and a denominator, polynomials of `qpp.cert.Poly`). The equalities `x = t` of the given are
substituted first, as the generated proof does (`subst`). The generator decides here, and Lean checks:

- the sign of a price or a reduced cost: zero (zero after the substitution), positive (a ratio of polynomials with
  positive coefficients in names of QQ>0, or such a ratio times the gap of a strict hypothesis of the given),
  nonnegative (the same with names of QQ>=0 or a non-strict hypothesis), or undecided;
- the rank of a matrix and its pivots, each pivot of a decided sign (so that Lean can divide by it);
- the inverse of a square matrix with such pivots.

Nothing here is trusted: each decision becomes a goal of the generated proof.
"""
from fractions import Fraction as F

from .cert import Poly
from . import texmath as T


class Undecided(Exception):
    """a sign the generator cannot decide from the given"""


class RF:
    """a rational function num / den over Q in named atoms"""

    def __init__(self, num, den=None):
        self.num = num
        self.den = den if den is not None else Poly.const(1)
        if not self.den.t:
            raise ZeroDivisionError("a denominator 0")
        self._norm()

    def _norm(self):
        # a constant denominator is moved into the numerator; a common factor of the numerator and the denominator
        # is cancelled (reduce), and the denominator is scaled by a positive number to the leading coefficient 1 or -1
        if not self.num.t:
            self.den = Poly.const(1)
            return
        if set(self.den.t) != {()} and set(self.num.t) != {()}:
            self.num, self.den = reduce(self.num, self.den)
        if set(self.den.t) == {()}:
            c = self.den.t[()]
            self.num = self.num.scale(1 / c)
            self.den = Poly.const(1)
            return
        c = abs(_monic_coef(self.den))
        if c != 1:
            self.num, self.den = self.num.scale(1 / c), self.den.scale(1 / c)

    @staticmethod
    def const(c):
        return RF(Poly.const(F(c)))

    @staticmethod
    def atom(a):
        return RF(Poly.atom(a))

    def __add__(self, o):
        if self.den.t == o.den.t:
            return RF(self.num + o.num, self.den)
        return RF(self.num * o.den + o.num * self.den, self.den * o.den)

    def __neg__(self):
        return RF(-self.num, self.den)

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        return RF(self.num * o.num, self.den * o.den)

    def inv(self):
        if not self.num.t:
            raise ZeroDivisionError("the inverse of 0")
        return RF(self.den, self.num)

    def __truediv__(self, o):
        return self * o.inv()

    def is_zero(self):
        return not self.num.t

    def is_const(self):
        return set(self.num.t) <= {()} and set(self.den.t) == {()}

    def value(self):
        return self.num.t.get((), F(0)) / self.den.t[()]

    def atoms(self):
        return self.num.atoms() | self.den.atoms()

    def subst(self, a, v):
        """the function with the atom a replaced by the function v"""
        return _subst_poly(self.num, a, v) / _subst_poly(self.den, a, v)

    def __repr__(self):
        return f"({self.num}) / ({self.den})"


def _subst_poly(p, a, v):
    out = RF.const(0)
    for k, fk in p.coeffs_in(a).items():
        term = RF(fk)
        for _ in range(k):
            term = term * v
        out = out + term
    return out


def _deg(p, x):
    return max((dict(m).get(x, 0) for m in p.t), default=0)


def _lead(p, x):
    """(degree, coefficient) of p as a polynomial in x, the coefficient free of x"""
    cs = p.coeffs_in(x)
    d = max(cs)
    return d, cs[d]


def _prem(a, b, x):
    """the pseudo-remainder of a by b in x: lc(b)^k a - q b of degree below that of b in x"""
    db, lb = _lead(b, x)
    xb = {}
    r = a
    while r.t and x in r.atoms() and _deg(r, x) >= db:
        dr, lr = _lead(r, x)
        if dr - db not in xb:
            xb[dr - db] = Poly.atom(x).pow(dr - db) * b
        r = r * lb - lr * xb[dr - db]
    if db == 0 and r.t:
        # b free of x divides every term up to its leading coefficient: the remainder is 0
        r = Poly()
    return r


def _monic_coef(p):
    """the coefficient of p at its greatest monomial, in the lexicographic order of the sorted atoms"""
    names = sorted(p.atoms())
    return p.t[max(p.t, key=lambda m: tuple(dict(m).get(v, 0) for v in names))]


def _monic(p):
    """p scaled so that its coefficient at the greatest monomial (in the order of the sorted atoms) is 1"""
    return p.scale(1 / _monic_coef(p))


def _content(p, x):
    """the gcd of the coefficients of p as a polynomial in x"""
    g = Poly()
    for c in p.coeffs_in(x).values():
        g = pgcd(g, c)
        if set(g.t) == {()}:
            break
    return g


def pgcd(a, b):
    """the greatest common divisor of two polynomials over Q, monic in the order of _monic (0 for two zeros), by
    the primitive remainder sequence in the first atom, recursively in the others"""
    if not a.t:
        return _monic(b) if b.t else Poly()
    if not b.t:
        return _monic(a)
    names = sorted(a.atoms() | b.atoms())
    if not names or set(a.t) == {()} or set(b.t) == {()}:
        return Poly.const(1)
    x = names[0]
    if x not in a.atoms():
        return pgcd(a, _content(b, x))
    if x not in b.atoms():
        return pgcd(_content(a, x), b)
    ca, cb = _content(a, x), _content(b, x)
    c = pgcd(ca, cb)
    pa, pb = pdiv(a, ca), pdiv(b, cb)
    if _deg(pa, x) < _deg(pb, x):
        pa, pb = pb, pa
    while pb.t:
        r = _prem(pa, pb, x)
        if r.t:
            r = pdiv(r, _content(r, x))
        pa, pb = pb, r
    return _monic(c * pa)


def _one_signed(p):
    return len({v > 0 for v in p.t.values()}) == 1


def reduce(num, den):
    """(num, den) with their gcd cancelled; kept as they are when the cancellation would give a numerator or a
    denominator coefficients of both signs that it did not have (the signs are decided on the coefficients, Signs)"""
    g = pgcd(num, den)
    if set(g.t) == {()}:
        return num, den
    n2, d2 = pdiv(num, g), pdiv(den, g)
    if n2 is None or d2 is None:
        return num, den
    if all(v < 0 for v in d2.t.values()) and not all(v < 0 for v in den.t.values()):
        n2, d2 = -n2, -d2
    if (_one_signed(num) and not _one_signed(n2)) or (_one_signed(den) and not _one_signed(d2)):
        return num, den
    return n2, d2


def pdiv(a, b):
    """the exact quotient a / b of two polynomials (lexicographic division), or None if b does not divide a"""
    if not b.t:
        return None
    names = sorted(a.atoms() | b.atoms())

    def key(m):
        d = dict(m)
        return tuple(d.get(v, 0) for v in names)
    q, r = Poly(), a
    lb = max(b.t, key=key)
    db = dict(lb)
    while r.t:
        lr = max(r.t, key=key)
        dr = dict(lr)
        if any(dr.get(x, 0) < e for x, e in db.items()):
            return None
        m = tuple(sorted((x, dr[x] - db.get(x, 0)) for x in dr if dr[x] - db.get(x, 0) > 0))
        t = Poly({m: r.t[lr] / b.t[lb]})
        q = q + t
        r = r - t * b
    return q


def linear(f, scales):
    """(coefficients, constant) of a rational function affine in the scales, the coefficients and the constant free of
    them; ValueError if it is not affine in the scales"""
    if f.den.atoms() & set(scales):
        raise ValueError("a scale in a denominator")
    rest, coefs = f.num, []
    for s in scales:
        cs = rest.coeffs_in(s)
        if any(k > 1 for k in cs):
            raise ValueError(f"the power of the scale {s}")
        c1 = cs.get(1, Poly())
        if c1.atoms() & set(scales):
            raise ValueError(f"a product of the scale {s} with another scale")
        coefs.append(RF(c1, f.den))
        rest = cs.get(0, Poly())
    return coefs, RF(rest, f.den)


def ast_subst(x, m):
    """the Q++ term x with each name of m replaced by its term (in parentheses); x binds no name"""
    if isinstance(x, tuple) and len(x) == 2 and x[0] == "var" and x[1] in m:
        return ("paren", m[x[1]])
    if isinstance(x, tuple):
        return tuple(ast_subst(y, m) for y in x)
    return x


def from_ast(x):
    """the rational function of a Q++ term: numerals, names, + - * /, powers by a numeral"""
    k = x[0]
    if k == "num":
        return RF.const(F(x[1]))
    if k == "var":
        return RF.atom(x[1])
    if k == "paren":
        return from_ast(x[1])
    if k == "neg":
        return -from_ast(x[1])
    if k == "bin" and x[1] in ("+", "-", "*", "/"):
        a, b = from_ast(x[2]), from_ast(x[3])
        if x[1] == "/" and b.is_zero():
            raise ValueError(f"prog: {T.to_qpp(x)} divides by 0")
        return {"+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b, "/": lambda: a / b}[x[1]]()
    if k == "pow" and x[2][0] == "num" and x[2][1].isdigit():
        b, out = from_ast(x[1]), RF.const(1)
        for _ in range(int(x[2][1])):
            out = out * b
        return out
    raise ValueError(f"prog: {T.to_qpp(x)} is not a rational function of the parameters (numerals, names, + - * /, "
                     "powers by a numeral)")


# --------------------------------------------------------------------------------------------------------- signs

class Signs:
    """what the given says of the signs: the names in QQ>0 (strict) and in QQ>=0 or NN (nonnegative), and the gaps
    b - a of its hypotheses a < b (strict) and a <= b (nonnegative) on the parameters"""

    def __init__(self, strict_names, nonneg_names, strict_gaps, nonneg_gaps):
        self.strict_names, self.nonneg_names = set(strict_names), set(nonneg_names)
        self.strict_gaps, self.nonneg_gaps = list(strict_gaps), list(nonneg_gaps)

    def _poly_sign(self, p):
        """(direction, strict) of a polynomial at every point of the given, by the signs of its coefficients:
        direction 1 (every coefficient positive) or -1 (every one negative), strict when every name is in QQ>0 or
        the constant term is nonzero; None if the coefficients have both signs or a name has no sign"""
        if not p.t:
            return None
        pos = {c > 0 for c in p.t.values()}
        if len(pos) != 1:
            return None
        names = p.atoms()
        if not names <= self.strict_names | self.nonneg_names:
            return None
        return (1 if pos == {True} else -1), (names <= self.strict_names or () in p.t)

    def _direct(self, f):
        """(direction, strict) of a rational function, or None"""
        if f.is_zero():
            return None
        n, d = self._poly_sign(f.num), self._poly_sign(f.den)
        if n is None or d is None:
            return None
        if not d[1]:
            return None  # a denominator that may vanish
        return n[0] * d[0], n[1]

    def sign(self, f):
        """'zero', 'pos', 'nonneg', 'neg', 'nonpos' or None (undecided)"""
        if f.is_zero():
            return "zero"
        if f.is_const():
            return "pos" if f.value() > 0 else "neg"
        names = {(1, True): "pos", (1, False): "nonneg", (-1, True): "neg", (-1, False): "nonpos"}
        d = self._direct(f)
        if d is not None and d[1]:
            return names[d]
        if d is not None:
            # of one sign, not strictly: strict if it is a function of strict sign times a strict gap
            sg = self._strict_gap(f)
            return names[(sg[2], True)] if sg is not None else names[d]
        # a function of one sign times the gap of a hypothesis
        for gaps, strict in ((self.strict_gaps, True), (self.nonneg_gaps, False)):
            for g in gaps:
                qn = pdiv(f.num, g.num)
                d = self._direct(RF(qn * g.den, f.den) if qn is not None else f / g)
                if d is not None:
                    return names[(d[0], d[1] and strict)]
        return None

    def _strict_gap(self, f):
        """(gap, q, direction) with f = q * gap, the gap strict and q of strict sign; or None"""
        for g in self.strict_gaps:
            qn = pdiv(f.num, g.num)
            q = RF(qn * g.den, f.den) if qn is not None else f / g
            d = self._direct(q)
            if d is not None and d[1]:
                return g, q, d[0]
        return None

    def nonzero(self, f):
        return self.sign(f) in ("pos", "neg")

    def why(self, f):
        """the reason of a decided sign: ("zero",), ("const",), ("direct",), or ("gap", gap, q, strict) with
        f = q * gap, the gap one of the given (its RF and its data); None if undecided"""
        if f.is_zero():
            return ("zero",)
        if f.is_const():
            return ("const",)
        d = self._direct(f)
        if d is not None and not d[1]:
            # as sign: a strict gap first, when it makes the sign strict
            sg = self._strict_gap(f)
            if sg is not None:
                return ("gap", sg[0], sg[1], True)
        if d is not None:
            return ("direct",)
        for gaps, strict in ((self.strict_gaps, True), (self.nonneg_gaps, False)):
            for g in gaps:
                qn = pdiv(f.num, g.num)
                q = RF(qn * g.den, f.den) if qn is not None else f / g
                if self._direct(q) is not None:
                    return ("gap", g, q, strict)
        return None


# --------------------------------------------------------------------------------------------------- linear algebra

def echelon(rows, ncols, signs):
    """Gaussian elimination of a list of rows (lists of RF): (pivots, independent, undecided) with pivots[i] the pivot
    column of the i-th independent row, independent the indices of the rows that are independent, in order, and
    undecided the indices of the rows whose remaining entries are all of undecided sign (left out: their rank is not
    decided). A pivot is an entry of decided sign."""
    work = [list(r) for r in rows]
    pivots, independent, undecided, used = [], [], [], set()
    for i, r in enumerate(work):
        col = next((c for c in range(ncols) if c not in used and signs.nonzero(r[c])), None)
        if col is None:
            if any(not r[c].is_zero() for c in range(ncols)):
                undecided.append(i)
            continue
        used.add(col)
        pivots.append(col)
        independent.append(i)
        for r2 in work[i + 1:]:
            if not r2[col].is_zero():
                f = r2[col] / r[col]
                for c in range(ncols):
                    r2[c] = r2[c] - f * r[c]
    return pivots, independent, undecided


def inverse(m, signs):
    """the inverse of a square matrix of RF, by Gauss-Jordan with pivots of decided sign; None if none fits"""
    n = len(m)
    a = [list(r) + [RF.const(1 if i == j else 0) for j in range(n)] for i, r in enumerate(m)]
    for c in range(n):
        p = next((i for i in range(c, n) if signs.nonzero(a[i][c])), None)
        if p is None:
            return None
        a[c], a[p] = a[p], a[c]
        piv = a[c][c]
        a[c] = [x / piv for x in a[c]]
        for i in range(n):
            if i != c and not a[i][c].is_zero():
                f = a[i][c]
                a[i] = [x - f * y for x, y in zip(a[i], a[c])]
    return [r[n:] for r in a]


# ---------------------------------------------------------------------------------------------------------- Lean

def lean_poly(p, names):
    """the Lean term of a polynomial over Q in the atoms, names[a] the Lean name of the atom a"""
    if not p.t:
        return "0"
    parts = []
    for m, c in sorted(p.t.items(), key=lambda mc: (-sum(e for _, e in mc[0]), mc[0])):
        mono = " * ".join(names[a] if e == 1 else f"{names[a]} ^ {e}" for a, e in m)
        a = abs(c)
        coef = (str(a.numerator) if a.denominator == 1 else f"({a.numerator} / {a.denominator} : \u211a)")
        if mono:
            body = mono if a == 1 else f"{coef} * {mono}"
        else:
            body = coef if a.denominator != 1 else f"({a.numerator} : \u211a)"
        parts.append(("-" if c < 0 else "+", body))
    s = ("-" if parts[0][0] == "-" else "") + parts[0][1]
    for sg, b in parts[1:]:
        s += f" {sg} {b}"
    return s


def lean_poly_sign(p, names, atoms, strict):
    """a proof term of 0 < P (0 <= P when not strict) for the Lean term P = lean_poly(p, names) of a polynomial whose
    coefficients are all above zero, built on the structure of P: add_pos or add_nonneg over its monomials, mul_pos or
    mul_nonneg over the factors of a monomial, pow_pos or pow_nonneg over a power, a coefficient by norm_num, and the
    proof of each atom from atoms[a] = (proof of 0 < a or of 0 <= a, strict); None if a coefficient is not above zero,
    an atom has no proof, or the strict sign is not reached"""
    if not p.t or any(c <= 0 for c in p.t.values()) or not p.atoms() <= set(atoms):
        return None
    parts = []
    for m, c in sorted(p.t.items(), key=lambda mc: (-sum(e for _, e in mc[0]), mc[0])):
        st = all(atoms[a][1] for a, _ in m)
        facs = [] if (m and c == 1) else ["(by norm_num)"]
        for a, e in m:
            base = _le(*atoms[a], st)
            facs.append(base if e == 1 else f"({'pow_pos' if st else 'pow_nonneg'} {base} {e})")
        pr = facs[0]
        for f in facs[1:]:
            pr = f"({'mul_pos' if st else 'mul_nonneg'} {pr} {f})"
        parts.append((pr, st))
    pr, st = parts[0]
    for q, s2 in parts[1:]:
        if st and s2:
            pr = f"(add_pos {pr} {q})"
        elif st:
            pr = f"(add_pos_of_pos_of_nonneg {pr} {_le(q, s2, False)})"
        elif s2:
            pr = f"(add_pos_of_nonneg_of_pos {pr} {q})"
        else:
            pr = f"(add_nonneg {pr} {q})"
        st = st or s2
    if strict and not st:
        return None
    return _le(pr, st, strict)


def _le(proof, strict, want_strict):
    """a proof of 0 <= a from one of 0 < a when the strict sign is not wanted"""
    return f"{proof}.le" if strict and not want_strict and proof != "(by norm_num)" else proof


def lean_rf_sign(f, names, atoms, strict):
    """a proof term of 0 < F (0 <= F when not strict) for the Lean term F = lean_rf(f, names) of a rational function
    whose numerator and denominator have all their coefficients above zero (after lean_rf negates both when the
    denominator's are all below zero): div_pos or div_nonneg over lean_poly_sign; None if it does not apply"""
    if f.den.t and all(c < 0 for c in f.den.t.values()):
        f = RF(-f.num, -f.den)
    n = lean_poly_sign(f.num, names, atoms, strict)
    if n is None:
        return None
    if set(f.den.t) == {()} and f.den.t[()] == 1:
        return n
    d = lean_poly_sign(f.den, names, atoms, True)
    if d is None:
        return None
    return f"(div_pos {n} {d})" if strict else f"(div_nonneg {n} {d}.le)"


def lean_rf(f, names=None):
    """the Lean term of a rational function, in parentheses unless it is an atom or a numeral; a denominator whose
    coefficients are all below zero is negated, with the numerator"""
    names = names or {a: a for a in f.atoms()}
    if f.den.t and all(c < 0 for c in f.den.t.values()):
        f = RF(-f.num, -f.den)
    n = lean_poly(f.num, names)
    if set(f.den.t) == {()} and f.den.t[()] == 1:
        return n if _plain(n) else f"({n})"
    return f"(({n}) / ({lean_poly(f.den, names)}))"


def _plain(s):
    return all(ch.isalnum() or ch in "_.'" for ch in s) or (s.startswith("(") and s.endswith(")") and s.count("(") == 1)


def denominators(fs):
    """the denominators that are not numerals, without repetition"""
    out = []
    for f in fs:
        if not (set(f.den.t) == {()}) and all(repr(f.den) != repr(d) for d in out):
            out.append(f.den)
    return out
