"""Identities of rational functions over Q, checked by ring1 from the ties d * d^-1 = 1 (the field steps).

ring1 reads an inverse as an atom: the inverse of a numeral is a numeral, the inverse of a monomial the product of
the inverses of its atoms, and the inverse of a sum of several terms (in its normal form) one atom (Mathlib,
Tactic/Ring/Basic.lean, ExSum.evalInv). It never reads d * d^-1 as 1, which needs d != 0. So an identity L = R of
rational functions, read as ring1 reads it, is a polynomial F = L - R in the atoms x and the inverse atoms
y_i = d_i^-1. It holds as an identity of rational functions exactly when F lies in the ideal of the ties
d_i y_i - 1, since Q[x, y] / (d_i y_i - 1) is the localization of Q[x] at the d_i, a domain inside Q(x).

The cofactors c_i with F = sum_i c_i (d_i y_i - 1) are computed here, one inverse atom at a time, the last one first
(the denominator of an inverse atom reads only the inverse atoms before it). With u = d y, a = deg_y F and
F = sum_j f_j y^j:

    d^a F = F' + (u - 1) C,   F' = sum_j f_j d^(a - j),   C = sum_j f_j d^(a - j) (1 + u + ... + u^(j - 1)),
    F = (u - 1) (C y^a - F (1 + u + ... + u^(a - 1))) + y^a F',

and F' is free of y. The step is then `linear_combination sum_i c_i * mul_inv_cancel_0 h_i`, each h_i : d_i != 0 by
name, which ring1 checks: no discharger, no search. The certificate is computed from the texts of the two sides as
the generator writes them, read as ring1 reads them (numerals, casts and applications as atoms, powers by numerals
expanded, a power by a variable exponent split at the summands of its exponent).
"""
import re
from fractions import Fraction as F

from .cert import Poly

MAX_TERMS = 400  # the most terms of the cofactors written into one step (larger: no certificate)


class Unread(Exception):
    """a text that this reading does not cover"""


# ------------------------------------------------------------------------------------------------------- reading

OPS = "+-*/^,:"
INV = "\u207b\u00b9"  # the superscript -1 of Lean


def _close(s, i):
    """the index of the bracket that closes s[i]"""
    pairs = {"(": ")", "[": "]", "\u27e8": "\u27e9", "{": "}"}
    stack = [pairs[s[i]]]
    j = i + 1
    while j < len(s):
        ch = s[j]
        if ch in pairs:
            stack.append(pairs[ch])
        elif stack and ch == stack[-1]:
            stack.pop()
            if not stack:
                return j
        elif ch in ")]\u27e9}":
            raise Unread(f"unbalanced {s}")
        j += 1
    raise Unread(f"unbalanced {s}")


def _top(s, ch):
    """the indices of ch at depth 0 of s"""
    out, d = [], 0
    for i, c in enumerate(s):
        if c in "([\u27e8{":
            d += 1
        elif c in ")]\u27e9}":
            d -= 1
        elif c == ch and d == 0:
            out.append(i)
    return out


def canon(s):
    """a text with its spaces normalized and its outer parentheses removed"""
    s = re.sub(r"\s+", " ", s.strip())
    while s.startswith("(") and _close(s, 0) == len(s) - 1:
        s = s[1:-1].strip()
    return s


NUM = re.compile(r"\d+(?:\s*/\s*\d+)?")
IDENT = re.compile(r"[^\s()\[\]\u27e8\u27e9{}+\-*/^,:\u207b\u00b9]+")


class Parser:
    """a Lean term over Q as a tree: ("num", F), ("atom", text), ("add" | "sub" | "mul" | "div", a, b), ("neg", a),
    ("pow", a, n) with n a numeral, ("powv", a, exponent text), ("inv", a)"""

    def __init__(self, s):
        self.s, self.i = s, 0

    def ws(self):
        while self.i < len(self.s) and self.s[self.i].isspace():
            self.i += 1

    def peek(self, t):
        self.ws()
        return self.s.startswith(t, self.i)

    def expr(self):
        a = self.term()
        while True:
            if self.peek("+"):
                self.i += 1
                a = ("add", a, self.term())
            elif self.peek("-") and not self.peek("->"):
                self.i += 1
                a = ("sub", a, self.term())
            else:
                return a

    def term(self):
        a = self.unary()
        while True:
            if self.peek("*"):
                self.i += 1
                a = ("mul", a, self.unary())
            elif self.peek("/"):
                self.i += 1
                a = ("div", a, self.unary())
            else:
                return a

    def unary(self):
        if self.peek("-"):
            self.i += 1
            return ("neg", self.unary())
        return self.power()

    def power(self):
        a = self.postfix()
        if self.peek("^"):
            self.i += 1
            self.ws()
            st = self.i
            e = self.postfix()
            text = self.s[st:self.i]
            if e[0] == "num" and e[1].denominator == 1 and e[1] >= 0:
                return ("pow", a, int(e[1]))
            return ("powv", a, canon(text))
        return a

    def postfix(self):
        a = self.primary()
        while self.peek(INV):
            self.i += len(INV)
            a = ("inv", a)
        return a

    def primary(self):
        self.ws()
        s, i = self.s, self.i
        if i >= len(s):
            raise Unread("end of text")
        if s[i] == "(":
            j = _close(s, i)
            inner = s[i + 1:j]
            self.i = j + 1
            return read_paren(inner)
        m = NUM.match(s, i)
        if m and (m.end() == len(s) or not (s[m.end()].isalnum() or s[m.end()] in "_'.")):
            self.i = m.end()
            return ("num", F(re.sub(r"\s", "", m.group(0))))
        if s[i] in "\u2191":
            self.i += 1
            st = i
            self.primary_arg()
            return ("atom", canon(s[st:self.i]))
        m = IDENT.match(s, i)
        if not m:
            raise Unread(f"at {s[i:i + 20]!r}")
        word = m.group(0)
        if word in ("if", "then", "else", "fun", "\u2211", "\u220f", "by", "from", "show"):
            raise Unread(f"the word {word}")
        st = i
        self.i = m.end()
        # an application: the head and its arguments (names, numerals, bracketed terms)
        while True:
            self.ws()
            if self.i >= len(s):
                break
            c = s[self.i]
            if c in "([\u27e8{":
                self.i = _close(s, self.i) + 1
                continue
            m2 = IDENT.match(s, self.i)
            if m2 and m2.group(0) not in ("if", "then", "else"):
                self.i = m2.end()
                continue
            break
        return ("atom", canon(s[st:self.i]))

    def primary_arg(self):
        self.ws()
        s = self.s
        if self.i < len(s) and s[self.i] in "([\u27e8{":
            self.i = _close(s, self.i) + 1
            return
        m = IDENT.match(s, self.i)
        if not m:
            raise Unread("a cast of nothing")
        self.i = m.end()


def read_paren(inner):
    """the tree of `(inner)`: an ascription `(e : Q)` (a numeral, or a cast: one atom), a bracketed term, or an atom
    (a sum, a conditional, an ascription to another type)"""
    t = inner.strip()
    if not t:
        raise Unread("()")
    if t[0] in "\u2211\u220f" or t.startswith("if ") or _top(t, ","):
        return ("atom", canon(t))
    cs = _top(t, ":")
    if cs:
        e, ty = t[:cs[-1]].strip(), t[cs[-1] + 1:].strip()
        if ty in ("\u211a", "\u2115") and NUM.fullmatch(e):
            return ("num", F(re.sub(r"\s", "", e)))
        m = re.fullmatch(r"\(\s*(" + IDENT.pattern + r")\s*:\s*\u2115\s*\)", e)
        if ty == "\u211a" and m:
            # ((n : N) : Q) is the cast of the count n, the same term as (n : Q)
            return ("atom", canon(f"{m.group(1)} : \u211a"))
        if ty == "\u211a" and e.startswith("(") and _close(e, 0) == len(e) - 1:
            # ((f x : N) : Q), the cast of an application with no operation at its top, is the term (f x : Q)
            cn = _top(e[1:-1], ":")
            if cn and e[1:-1][cn[-1] + 1:].strip() == "\u2115":
                x = canon(e[1:-1][:cn[-1]])
                if x and not NUM.fullmatch(x) and x[0] not in "\u2211\u220f\u2191" and not x.startswith("if ") \
                        and not any(_top(x, o) for o in ("+", "-", "*", "/", "^", ",", ":")):
                    return read_paren(f"{x} : \u211a")
        if ty == "\u211a" and not IDENT.fullmatch(e) and not e.startswith("(") and "\u2191" not in e:
            # a compound term elaborated at Q: ring1 reads its operations (an atom would hide a sum)
            try:
                return parse(e)
            except Unread:
                pass
        return ("atom", canon(t))
    return parse(t)


def split_rel(t, op):
    """the two sides of the relation t at its one top-level op, or None"""
    d, idx = 0, []
    for i, c in enumerate(t):
        if c in "([\u27e8{":
            d += 1
        elif c in ")]\u27e9}":
            d -= 1
        elif d == 0 and t.startswith(op, i):
            idx.append(i)
    if len(idx) != 1:
        return None
    return t[:idx[0]].strip(), t[idx[0] + len(op):].strip()


def parse(s):
    p = Parser(s)
    x = p.expr()
    p.ws()
    if p.i != len(s):
        raise Unread(f"left over: {s[p.i:p.i + 30]!r}")
    return x


# ----------------------------------------------------------------------------------------------- ring1's reading

class Model:
    """the polynomials of terms read as ring1 reads them: atoms are canonical texts, the inverse of an atom or of a
    sum one more atom; self.inv[atom] = (its base, a Poly, in the order the atoms were made); self.text[atom] the
    Lean text of an atom"""

    def __init__(self, expand=False):
        self.inv, self.text, self.order = {}, {}, []
        # the second reading (tie_terms, where the first leaves the identity out of the ideal): a power with a
        # variable exponent distributed over the factors of its base and its exponent expanded into monomials,
        # (q * 2^A)^(k + 1) = q^k * q * (2^(A * k)) * 2^A, as ring1 reads it
        self.expand = expand
        self.numpow = {}  # an atom c ^ e (c a numeral other than 0, e not a numeral): (c, the Lean text of e)
        # an atom (p / q) ^ e (p / q a positive numeral, q > 1): (the Lean text of e, p, q). ring1 reads it apart from
        # p ^ e * (q ^ e)^-1, and the equation div_pow (one_div_pow at p = 1) gives the one for the other
        self.fracpow = {}

    def atom(self, text):
        a = canon(text)
        self.text.setdefault(a, text if _plain(text) else f"({canon(text)})")
        return Poly.atom(a)

    def poly(self, x):
        k = x[0]
        if k == "num":
            return Poly.const(x[1])
        if k == "atom":
            return self.atom(x[1])
        if k in ("add", "sub", "mul"):
            a, b = self.poly(x[1]), self.poly(x[2])
            return a + b if k == "add" else a - b if k == "sub" else a * b
        if k == "neg":
            return -self.poly(x[1])
        if k == "div":
            return self.poly(x[1]) * self.inverse(self.poly(x[2]))
        if k == "inv":
            return self.inverse(self.poly(x[1]))
        if k == "pow":
            return self.poly(x[1]).pow(x[2])
        if k == "powv":
            return self.powv(x[1], x[2])
        raise Unread(k)

    def powv(self, base, e):
        """b ^ e with e not a numeral: b an atom or a numeral, e split at its summands (b ^ (n + 1) is b ^ n * b, as
        ring1 reads it); one atom otherwise"""
        if self.expand:
            out = self.powv_expanded(base, e)
            if out is not None:
                return out
        if base[0] not in ("num", "atom"):
            return self.atom(f"({lean_of(base)}) ^ ({e})")
        bt = lean_of(base)
        out = Poly.const(1)
        try:
            summands = sum_parts(parse(e))
        except Unread:
            summands = [("atom", e)]
        for s in summands:
            if s[0] == "num" and s[1].denominator == 1 and s[1] >= 0:
                out = out * self.poly(base).pow(int(s[1]))
            else:
                a = self.atom(f"{bt} ^ {wrap(lean_of(s))}")
                if base[0] == "num" and base[1] != 0:
                    self.numpow[next(iter(a.atoms()))] = (base[1], lean_of(s))
                if base[0] == "num" and base[1] > 0 and base[1].denominator > 1:
                    self.fracpow[next(iter(a.atoms()))] = (lean_of(s), base[1].numerator, base[1].denominator)
                out = out * a
        return out

    def powv_expanded(self, base, e):
        """b ^ e in the second reading: 1 ^ e is 1, (x * y) ^ e is x ^ e * y ^ e, (x / y) ^ e and x^-1 ^ e through
        the inverse, (b ^ n) ^ e is (b ^ e) ^ n, (b ^ c) ^ e is b ^ (c * e); a numeral or an atom b to the exponent
        expanded into monomials m with coefficients c, the product of (b ^ m) ^ c; None where the exponent is not a
        polynomial with coefficients in N (a difference: the first reading)"""
        k = base[0]
        if k == "num" and base[1] == 1:
            return Poly.const(1)
        if k in ("div", "inv") and not _has_atom(base):
            # a quotient of numerals: ring1 reads (1 / 2) ^ k as one constant to the power, the first reading
            return None
        if k == "mul":
            return self.powv(base[1], e) * self.powv(base[2], e)
        if k == "div":
            return self.powv(base[1], e) * self.inverse(self.powv(base[2], e))
        if k == "inv":
            return self.inverse(self.powv(base[1], e))
        if k == "pow":
            return self.powv(base[1], e).pow(base[2])
        if k == "powv":
            return self.powv(base[1], f"({base[2]}) * ({e})")
        if k not in ("num", "atom"):
            return None
        try:
            monos = exp_poly(parse(e))
        except Unread:
            return None
        bt = lean_of(base)
        out = Poly.const(1)
        for m, c in sorted(monos.items()):
            if not m:
                out = out * self.poly(base).pow(c)
                continue
            mt = " * ".join(m)
            a = self.atom(f"{bt} ^ {wrap(mt)}")
            if base[0] == "num" and base[1] != 0:
                self.numpow[next(iter(a.atoms()))] = (base[1], mt)
            if base[0] == "num" and base[1] > 0 and base[1].denominator > 1:
                self.fracpow[next(iter(a.atoms()))] = (mt, base[1].numerator, base[1].denominator)
            out = out * a.pow(c)
        return out

    def inverse(self, p):
        if not p.t:
            return Poly()
        if len(p.t) == 1:
            (m, c), = p.t.items()
            out = Poly.const(1 / c)
            for a, e in m:
                if a in self.inv:
                    raise Unread("the inverse of an inverse")
                out = out * self.inv_atom(Poly.atom(a)).pow(e)
            return out
        return self.inv_atom(p)

    def inv_atom(self, base):
        key = "inv#" + repr(sorted(base.t.items()))
        if key not in self.inv:
            self.inv[key] = base
            self.order.append(key)
            self.text[key] = f"({poly_text(base, self.text)})\u207b\u00b9"
        return Poly.atom(key)

    def of_text(self, s):
        return self.poly(parse(s))


def _has_atom(x):
    """whether a tree of parse reads an atom or a power with a variable exponent (not a numeral of ring1)"""
    return x[0] in ("atom", "powv") or any(isinstance(y, tuple) and _has_atom(y) for y in x[1:])


def exp_poly(x):
    """an exponent as a polynomial with coefficients in N: {the sorted names of a monomial: its coefficient}; Unread
    where it is not one"""
    k = x[0]
    if k == "num":
        if x[1].denominator != 1 or x[1] < 0:
            raise Unread("an exponent numeral")
        return {(): int(x[1])} if x[1] else {}
    if k == "atom":
        return {(x[1],): 1}
    if k == "add":
        out = dict(exp_poly(x[1]))
        for m, c in exp_poly(x[2]).items():
            out[m] = out.get(m, 0) + c
        return out
    if k == "mul":
        return _exp_mul(exp_poly(x[1]), exp_poly(x[2]))
    if k == "pow":
        out, b = {(): 1}, exp_poly(x[1])
        for _ in range(x[2]):
            out = _exp_mul(out, b)
        return out
    raise Unread(f"an exponent {k}")


def _exp_mul(a, b):
    """the product of two exponents of exp_poly"""
    out = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(sorted(m1 + m2))
            out[m] = out.get(m, 0) + c1 * c2
    return out


def sum_parts(x):
    """the summands of a tree of sums (a difference: no split)"""
    if x[0] == "add":
        return sum_parts(x[1]) + sum_parts(x[2])
    return [x]


def lean_of(x):
    """a Lean text of a tree (for the base and the summands of a variable power)"""
    k = x[0]
    if k == "num":
        return num_text(x[1])
    if k == "atom":
        return x[1] if _plain(x[1]) else f"({x[1]})"
    if k == "add":
        return f"{lean_of(x[1])} + {lean_of(x[2])}"
    if k == "sub":
        # a gap b - a (as the denominator k * (k + s - 1) under 1 < k + s)
        return f"{lean_of(x[1])} - {wrap(lean_of(x[2]))}"
    if k == "mul":
        return f"{wrap(lean_of(x[1]))} * {wrap(lean_of(x[2]))}"
    if k == "pow":
        return f"{wrap(lean_of(x[1]))} ^ {x[2]}"
    if k == "powv":
        return f"{wrap(lean_of(x[1]))} ^ {wrap(x[2])}"
    raise Unread(k)


def _plain(s):
    return bool(re.fullmatch(r"[\w.'\u2080-\u2089]+", s)) or (s.startswith("(") and _close(s, 0) == len(s) - 1)


def wrap(s):
    return s if _plain(s) else f"({s})"


def num_text(c):
    c = F(c)
    if c.denominator == 1:
        return f"({c.numerator} : \u211a)" if c >= 0 else f"(-{-c.numerator} : \u211a)"
    return f"({c.numerator} / {c.denominator} : \u211a)" if c > 0 else f"(-({-c.numerator} / {c.denominator} : \u211a))"


def poly_text(p, text):
    """the Lean text over Q of a polynomial of the model"""
    if not p.t:
        return "(0 : \u211a)"
    parts = []
    for m, c in sorted(p.t.items(), key=lambda mc: repr(mc[0])):
        fs = []
        for a, e in m:
            t = wrap(text[a])
            fs.append(t if e == 1 else f"{t} ^ {e}")
        a = abs(c)
        if fs and a == 1:
            body = " * ".join(fs)
        elif fs:
            body = " * ".join([num_text(a)] + fs)
        else:
            body = num_text(a)
        parts.append(("-" if c < 0 else "+", body))
    s = ("-" if parts[0][0] == "-" else "") + parts[0][1]
    for sg, b in parts[1:]:
        s += f" {sg} {b}"
    return s


# ------------------------------------------------------------------------------------------------- the cofactors

def _geom(u, n):
    """1 + u + ... + u^(n - 1)"""
    out, t = Poly(), Poly.const(1)
    for _ in range(n):
        out = out + t
        t = t * u
    return out


def cofactors(f, model, keys):
    """{inverse atom: c} with f = sum c (d y - 1) over the inverse atoms keys (in the order they were made), or
    None if f is not in the ideal of their ties"""
    if not f.t:
        return {}
    if not keys:
        return None
    y = keys[-1]
    d = model.inv[y]
    cs = f.coeffs_in(y)
    a = max(cs)
    if a == 0:
        return cofactors(f, model, keys[:-1])
    yp = Poly.atom(y)
    u = d * yp
    fp, c = Poly(), Poly()
    for j, fj in cs.items():
        dj = fj * d.pow(a - j)
        fp = fp + dj
        c = c + dj * _geom(u, j)
    rest = cofactors(fp, model, keys[:-1])
    if rest is None:
        return None
    ya = yp.pow(a)
    out = {k: v * ya for k, v in rest.items()}
    cy = c * ya - f * _geom(u, a)
    if cy.t:
        out[y] = cy
    return out


# ------------------------------------------------------------------------------------------------------ the step

def ties(model, nonzero):
    """{inverse atom: the Lean proof of d * d^-1 = 1} from nonzero, pairs (Lean text of d, proof of d != 0): a sum
    gives the tie of its inverse, an atom the tie of its own; a product or a power by a numeral gives those of its
    factors, each factor not 0 by left_ne_zero_of_mul, right_ne_zero_of_mul or ne_zero_pow"""
    out = {}

    def go(x, pf):
        p = model.poly(x)
        if len(p.t) > 1:
            out.setdefault("inv#" + repr(sorted(p.t.items())), f"mul_inv_cancel\u2080 {pf}")
            return
        if x[0] == "mul":
            go(x[1], f"(left_ne_zero_of_mul {pf})")
            go(x[2], f"(right_ne_zero_of_mul {pf})")
            return
        if x[0] == "pow" and x[2] >= 1:
            go(x[1], f"(ne_zero_pow (by norm_num) {pf})")
            return
        if len(p.t) == 1:
            (m, c), = p.t.items()
            if c == 1 and len(m) == 1 and m[0][1] == 1 and m[0][0] not in model.inv:
                out.setdefault("inv#" + repr(sorted(Poly.atom(m[0][0]).t.items())), f"mul_inv_cancel\u2080 {pf}")

    for t, pf in nonzero:
        try:
            go(parse(t), pf)
        except (Unread, ZeroDivisionError):
            continue
    # a power c ^ e of a numeral c other than 0 is not 0 at every e: pow_ne_zero, the numeral by norm_num
    for a, (c, e) in model.numpow.items():
        key = "inv#" + repr(sorted(Poly.atom(a).t.items()))
        out.setdefault(key, f"mul_inv_cancel\u2080 (pow_ne_zero {wrap(e)} (show {num_text(c)} \u2260 0 by norm_num))")
    return out


def combination(diff, nonzero, model):
    """the terms `c * tie` with diff = sum c (d d^-1 - 1), or None; [] when diff is 0 as ring1 reads it"""
    if not diff.t:
        return []
    # the inverse atoms with a tie are eliminated; an inverse atom with none is one more atom of the ring
    need = {a for a in diff.atoms() if a in model.inv} | _deps(model, diff.atoms())
    tie = ties(model, nonzero)
    keys = [k for k in model.order if k in need and k in tie]
    cs = cofactors(diff, model, keys)
    if cs is None or sum(len(c.t) for c in cs.values()) > MAX_TERMS:
        return None
    out = []
    for k in keys:
        c = cs.get(k)
        if c is None or not c.t:
            continue
        out.append(f"({poly_text(c, model.text)}) * {tie[k]}")
    return out


def _deps(model, atoms):
    """the inverse atoms that the bases of the inverse atoms among atoms read, transitively"""
    out, todo = set(), [a for a in atoms if a in model.inv]
    while todo:
        a = todo.pop()
        for b in model.inv[a].atoms():
            if b in model.inv and b not in out:
                out.add(b)
                todo.append(b)
    return out


def tie_terms(lhs, rhs, nonzero, hyps=(), eqs=()):
    """the terms of tie_terms_in; where the first reading of the powers leaves the identity out of the ideal of the
    ties, the second (Model.expand)"""
    out = tie_terms_in(lhs, rhs, nonzero, hyps, eqs, False)
    return out if out is not None else tie_terms_in(lhs, rhs, nonzero, hyps, eqs, True)


def tie_terms_in(lhs, rhs, nonzero, hyps=(), eqs=(), expand=False):
    """the terms `c * mul_inv_cancel_0 h` that, added to the combination of the hypotheses hyps (pairs (coefficient
    text or None, (lhs, rhs) of the hypothesis)), close the identity lhs = rhs (Lean texts over Q) by ring1, from the
    ties of nonzero (pairs (Lean text of d, proof of d != 0)): [] when none is needed, None where the reading does not
    cover a text or the identity is not in the ideal of the ties"""
    model = Model(expand)
    try:
        diff = model.of_text(lhs) - model.of_text(rhs)
        for coef, (a, b) in hyps:
            k = model.of_text(coef) if coef is not None else Poly.const(1)
            diff = diff - k * (model.of_text(a) - model.of_text(b))
        subs = []
        for name, a, b in eqs:
            # an equation `x = t` with x one atom: x replaced by t, the quotient its multiplier
            pa = model.of_text(a)
            if len(pa.t) != 1 or list(pa.t.values())[0] != 1 or len(next(iter(pa.t))) != 1 or \
                    next(iter(pa.t))[0][1] != 1:
                continue
            x = next(iter(pa.t))[0][0]
            if x not in diff.atoms():
                continue
            diff, q = diff.subst(x, model.of_text(b))
            if q.t:
                subs.append(f"({poly_text(q, model.text)}) * {name}")
        for x, (e, p, q0) in list(model.fracpow.items()):
            # (p / q) ^ e = p ^ e / q ^ e by name: the power of a quotient of numerals read through its parts
            if x not in diff.atoms():
                continue
            num = model.powv(("num", F(p)), e) if p != 1 else Poly.const(1)
            rhs = num * model.inverse(model.powv(("num", F(q0)), e))
            name = (f"(one_div_pow ({q0} : \u211a) {wrap(e)})" if p == 1 else
                    f"(div_pow ({p} : \u211a) ({q0} : \u211a) {wrap(e)})")
            diff, qq = diff.subst(x, rhs)
            if qq.t:
                subs.append(f"({poly_text(qq, model.text)}) * {name}")
        rest = combination(diff, nonzero, model)
        return None if rest is None else subs + rest
    except (Unread, ZeroDivisionError, RecursionError):
        return None


def identity(lhs, rhs, nonzero, eqs=()):
    """the step of the identity lhs = rhs: "ring1" when the two sides are one polynomial as ring1 reads them, else
    `linear_combination` of the equations eqs and of the ties of nonzero; None as tie_terms"""
    rest = tie_terms(lhs, rhs, nonzero, eqs=eqs)
    if rest is None:
        return None
    return "linear_combination " + " + ".join(rest) if rest else "ring1"
