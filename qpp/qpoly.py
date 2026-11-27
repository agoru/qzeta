"""Exact polynomials over Q in a fixed number of variables (fact:res): arithmetic, derivatives, substitution,
exact division, greatest common divisors, squarefree parts, gcd-free bases (con:coprime) and Sylvester resultants
with their cofactors (eq:resbezout). No floating point anywhere.

A polynomial is a Poly: `nv` variables and a dict {exponent tuple: Fraction} without zero coefficients. The
variables of the algorithm are w_1, ..., w_n (indices 0..n-1), then t (index n, the eliminants N in t) and delta
(index n+1, the difference polynomials D in delta).
"""
from fractions import Fraction
from math import gcd, lcm

F = Fraction


class Poly:
    __slots__ = ('nv', 't')

    def __init__(self, nv, terms=None):
        self.nv = nv
        self.t = {} if terms is None else {e: F(c) for e, c in terms.items() if c}

    # ------------------------------------------------------------ construction
    @staticmethod
    def const(c, nv):
        return Poly(nv, {(0,) * nv: F(c)})

    @staticmethod
    def var(i, nv):
        e = [0] * nv
        e[i] = 1
        return Poly(nv, {tuple(e): F(1)})

    @staticmethod
    def from_dict(d, nv):
        """from {exponent tuple (possibly shorter than nv): coefficient}"""
        out = {}
        for e, c in d.items():
            e = tuple(e) + (0,) * (nv - len(e))
            out[e] = out.get(e, F(0)) + F(c)
        return Poly(nv, out)

    def copy(self):
        p = Poly(self.nv)
        p.t = dict(self.t)
        return p

    # ------------------------------------------------------------ predicates
    def is_zero(self):
        return not self.t

    def is_const(self):
        return all(not any(e) for e in self.t)

    def const_value(self):
        return self.t.get((0,) * self.nv, F(0))

    def __eq__(self, other):
        return isinstance(other, Poly) and self.nv == other.nv and self.t == other.t

    def __hash__(self):
        return hash(self.key())

    def key(self):
        return tuple(sorted(self.t.items()))

    # ------------------------------------------------------------ arithmetic
    def __add__(self, o):
        if not isinstance(o, Poly):
            o = Poly.const(o, self.nv)
        out = dict(self.t)
        for e, c in o.t.items():
            v = out.get(e, F(0)) + c
            if v:
                out[e] = v
            else:
                out.pop(e, None)
        p = Poly(self.nv)
        p.t = out
        return p

    __radd__ = __add__

    def __neg__(self):
        p = Poly(self.nv)
        p.t = {e: -c for e, c in self.t.items()}
        return p

    def __sub__(self, o):
        if not isinstance(o, Poly):
            o = Poly.const(o, self.nv)
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if not isinstance(o, Poly):
            o = F(o)
            if not o:
                return Poly(self.nv)
            p = Poly(self.nv)
            p.t = {e: c * o for e, c in self.t.items()}
            return p
        out = {}
        for e1, c1 in self.t.items():
            for e2, c2 in o.t.items():
                e = tuple(a + b for a, b in zip(e1, e2))
                out[e] = out.get(e, F(0)) + c1 * c2
        p = Poly(self.nv)
        p.t = {e: c for e, c in out.items() if c}
        return p

    __rmul__ = __mul__

    def __truediv__(self, c):
        return self * (1 / F(c))

    def __pow__(self, k):
        r = Poly.const(1, self.nv)
        b = self
        while k:
            if k & 1:
                r = r * b
            b = b * b
            k >>= 1
        return r

    # ------------------------------------------------------------ structure in one variable
    def deg(self, i=None):
        if not self.t:
            return -1
        if i is None:
            return max(sum(e) for e in self.t)
        return max(e[i] for e in self.t)

    def vars(self):
        return {i for e in self.t for i, a in enumerate(e) if a}

    def coeffs(self, i):
        """[c_0, ..., c_d] with self = sum c_k v_i^k, c_k free of v_i"""
        d = self.deg(i)
        out = [dict() for _ in range(d + 1)]
        for e, c in self.t.items():
            k = e[i]
            out[k][e[:i] + (0,) + e[i + 1:]] = c
        res = []
        for dct in out:
            p = Poly(self.nv)
            p.t = dct
            res.append(p)
        return res

    @staticmethod
    def from_coeffs(cs, i, nv):
        out = {}
        for k, c in enumerate(cs):
            for e, v in c.t.items():
                e2 = e[:i] + (e[i] + k,) + e[i + 1:]
                out[e2] = out.get(e2, F(0)) + v
        return Poly(nv, out)

    def lc(self, i):
        return self.coeffs(i)[-1]

    def diff(self, i, k=1):
        p = self
        for _ in range(k):
            out = {}
            for e, c in p.t.items():
                if e[i]:
                    e2 = e[:i] + (e[i] - 1,) + e[i + 1:]
                    out[e2] = out.get(e2, F(0)) + c * e[i]
            q = Poly(self.nv)
            q.t = {e: c for e, c in out.items() if c}
            p = q
        return p

    def subs(self, i, q):
        """self with the variable i replaced by the polynomial q"""
        cs = self.coeffs(i)
        r = Poly(self.nv)
        for c in reversed(cs):
            r = r * q + c
        return r

    def scale_var(self, i, s):
        """self(v_i := s v_i), s rational"""
        s = F(s)
        p = Poly(self.nv)
        p.t = {e: c * s ** e[i] for e, c in self.t.items()}
        return p

    def evaluate(self, assign):
        """partial evaluation: assign = {variable index: rational}"""
        out = {}
        for e, c in self.t.items():
            v = c
            e2 = list(e)
            for i, x in assign.items():
                if e[i]:
                    v *= F(x) ** e[i]
                    e2[i] = 0
            if v:
                e2 = tuple(e2)
                out[e2] = out.get(e2, F(0)) + v
        return Poly(self.nv, out)

    def value(self, point):
        """the value at a point given for all variables that occur (a sequence indexed by variable)"""
        fast = _dyadic_value(self, point, None)
        if fast is not None:
            return fast
        s = F(0)
        for e, c in self.t.items():
            v = c
            for i, a in enumerate(e):
                if a:
                    v *= F(point[i]) ** a
            s += v
        return s

    def univariate(self, i, point):
        """the coefficients (low first) in the variable i after substituting point[j] for every other variable j
        that occurs; point is indexed by variable"""
        d = self.deg(i)
        fast = _dyadic_value(self, point, i)
        if fast is not None:
            out = fast + [F(0)] * (d + 1 - len(fast))
        else:
            out = [F(0)] * (d + 1)
            for e, c in self.t.items():
                v = c
                for j, a in enumerate(e):
                    if a and j != i:
                        v *= F(point[j]) ** a
                out[e[i]] += v
        while out and out[-1] == 0:
            out.pop()
        return out

    # ------------------------------------------------------------ normal forms
    def leading_term(self):
        e = max(self.t)
        return e, self.t[e]

    def int_primitive(self):
        """the integer primitive associate with a positive leading coefficient (lex order)"""
        if not self.t:
            return self
        den = 1
        for c in self.t.values():
            den = lcm(den, c.denominator)
        g = 0
        for c in self.t.values():
            g = gcd(g, int(c * den))
        _, lcv = self.leading_term()
        s = 1 if lcv > 0 else -1
        return self * F(s * den, g)

    def monic_ratio(self, other):
        """r with self = r * other, if self and other are associates in Q^x, else None"""
        if set(self.t) != set(other.t):
            return None
        e, c = self.leading_term()
        r = c / other.t[e]
        return r if all(self.t[k] == r * other.t[k] for k in self.t) else None

    def __repr__(self):
        return 'Poly(%d, %r)' % (self.nv, dict(sorted(self.t.items())))

    def to_json(self):
        return [[str(c), list(e)] for e, c in sorted(self.t.items())]

    @staticmethod
    def from_json(L, nv):
        return Poly(nv, {tuple(e): F(c) for c, e in L})

    def show(self, names=None):
        names = names or ['x%d' % i for i in range(self.nv)]
        if not self.t:
            return '0'
        parts = []
        for e, c in sorted(self.t.items(), reverse=True):
            mono = '*'.join(names[i] + ('^%d' % a if a > 1 else '') for i, a in enumerate(e) if a)
            parts.append(('%s' % c) + ('*' + mono if mono else ''))
        return ' + '.join(parts)


def value_parts(p, point):
    """(num, den) integers with p(point) = num/den, den > 0, for a dyadic point (no gcd taken)"""
    r = _dyadic_value(p, point, None, parts=True)
    if r is None:
        v = p.value(point)
        return v.numerator, v.denominator
    return r


def _dyadic_value(p, point, keep, parts=False):
    """the value of p at a point with dyadic coordinates by integer arithmetic (one division at the end); with keep
    a variable index, the coefficients in that variable (a list, low first). None if a coordinate is not dyadic."""
    used = set()
    for e in p.t:
        for j, a in enumerate(e):
            if a and j != keep:
                used.add(j)
    nums, exps = {}, {}
    for j in used:
        x = F(point[j])
        q = x.denominator
        ej = q.bit_length() - 1
        if q != 1 << ej:
            return None
        nums[j], exps[j] = x.numerator, ej
    L = 1
    for c in p.t.values():
        L = lcm(L, c.denominator)
    pw = {}

    def power(j, a):
        key = (j, a)
        if key not in pw:
            pw[key] = nums[j] ** a
        return pw[key]
    terms = {}
    Emax = 0
    for e, c in p.t.items():
        E = sum(a * exps[j] for j, a in enumerate(e) if a and j != keep)
        Emax = max(Emax, E)
        terms[e] = E
    acc = {}
    for e, c in p.t.items():
        v = int(c * L)
        for j, a in enumerate(e):
            if a and j != keep:
                v *= power(j, a)
        v <<= Emax - terms[e]
        k = e[keep] if keep is not None else 0
        acc[k] = acc.get(k, 0) + v
    den = L << Emax if Emax >= 0 else L
    if keep is None:
        if parts:
            return acc.get(0, 0), den
        return F(acc.get(0, 0), den)
    d = max(acc) if acc else -1
    return [F(acc.get(k, 0), den) for k in range(d + 1)]


def zero(nv):
    return Poly(nv)


# ---------------------------------------------------------------- exact division (fact:res (3))

def divexact(a, b):
    """a / b if b divides a in Q[x], else None (division by leading terms in lex order)"""
    if b.is_zero():
        raise ZeroDivisionError
    if a.is_zero():
        return Poly(a.nv)
    eb, cb = b.leading_term()
    if b.is_const():
        return a * (1 / cb)
    r = a.copy()
    q = {}
    bt = list(b.t.items())
    while r.t:
        er, cr = r.leading_term()
        de = tuple(x - y for x, y in zip(er, eb))
        if min(de) < 0:
            return None
        c = cr / cb
        q[de] = q.get(de, F(0)) + c
        for e, v in bt:
            e2 = tuple(x + y for x, y in zip(e, de))
            nvl = r.t.get(e2, F(0)) - c * v
            if nvl:
                r.t[e2] = nvl
            else:
                r.t.pop(e2, None)
    return Poly(a.nv, q)


def prem(a, b, i):
    """the pseudo-remainder of a by b in the variable i: lc(b)^(deg a - deg b + 1) a mod b"""
    db = b.deg(i)
    lcb = b.lc(i)
    r = a
    k = a.deg(i) - db + 1
    if k <= 0:
        return a
    xi = Poly.var(i, a.nv)
    while not r.is_zero() and r.deg(i) >= db:
        dr = r.deg(i)
        lr = r.lc(i)
        r = r * lcb - b * lr * xi ** (dr - db)
        k -= 1
    return r * lcb ** k if k > 0 else r


# ---------------------------------------------------------------- greatest common divisors

def _main_var(*ps):
    vs = set()
    for p in ps:
        vs |= p.vars()
    return max(vs) if vs else None


def content(p, i):
    """the gcd of the coefficients of p in the variable i (a polynomial free of v_i), integer primitive"""
    g = Poly(p.nv)
    for c in p.coeffs(i):
        if not c.is_zero():
            g = poly_gcd(g, c)
            if g.is_const():
                return Poly.const(1, p.nv)
    return g


def primitive(p, i):
    if p.is_zero():
        return p
    c = content(p, i)
    q = divexact(p, c)
    return q.int_primitive()


def _uni_gcd(a, b, i):
    """the gcd of two univariate polynomials in the variable i (primitive PRS over Z)"""
    def ints(p):
        cs = [c.const_value() for c in p.coeffs(i)]
        den = 1
        for c in cs:
            den = lcm(den, c.denominator)
        v = [int(c * den) for c in cs]
        return _prim(v)

    def _prim(v):
        while v and v[-1] == 0:
            v.pop()
        g = 0
        for c in v:
            g = gcd(g, c)
        return [c // g for c in v] if g > 1 else v
    A, B = ints(a), ints(b)
    if len(A) < len(B):
        A, B = B, A
    while B:
        r = list(A)
        lb = B[-1]
        while len(r) >= len(B) and r:
            lr = r[-1]
            sh = len(r) - len(B)
            r = [c * lb for c in r]
            for j, c in enumerate(B):
                r[sh + j] -= lr * c
            r.pop()
            while r and r[-1] == 0:
                r.pop()
        A, B = B, _prim(r)
    return Poly.from_coeffs([Poly.const(c, a.nv) for c in A], i, a.nv).int_primitive()


_PRIME = (1 << 61) - 1


def _coprime_mod_p(a, b, i):
    """True if the univariate a, b are certainly coprime over Q: their gcd modulo a large prime p not dividing the
    leading coefficients and denominators is 1 (the degree of the gcd over Q is at most that modulo p); False means
    undecided"""
    p = _PRIME

    def red(q):
        cs = [c.const_value() for c in q.coeffs(i)]
        out = []
        for c in cs:
            if c.denominator % p == 0:
                return None
            out.append(c.numerator * pow(c.denominator, -1, p) % p)
        if out[-1] == 0:
            return None
        return out
    A, B = red(a), red(b)
    if A is None or B is None:
        return False
    while B:
        while B and B[-1] == 0:
            B.pop()
        if not B:
            break
        inv = pow(B[-1], -1, p)
        A = A[:]
        while len(A) >= len(B):
            q = A[-1] * inv % p
            sh = len(A) - len(B)
            for j, c in enumerate(B):
                A[sh + j] = (A[sh + j] - q * c) % p
            A.pop()
            while A and A[-1] == 0:
                A.pop()
        A, B = B, A
    return len(A) == 1


def _is_monomial(p):
    return len(p.t) == 1


def _mono_gcd(m, p):
    """gcd of a monomial m with p: the product of the variables to the least orders"""
    e = next(iter(m.t))
    out = [0] * m.nv
    for i, a in enumerate(e):
        if a:
            out[i] = min(a, min(f[i] for f in p.t))
    return Poly(m.nv, {tuple(out): F(1)})


def poly_gcd(a, b):
    """the gcd in Q[x], integer primitive with a positive leading coefficient (recursive primitive PRS; Euclid for
    one variable; monomials directly)"""
    if a.is_zero():
        return b.int_primitive()
    if b.is_zero():
        return a.int_primitive()
    if a.is_const() or b.is_const():
        return Poly.const(1, a.nv)
    if _is_monomial(a):
        return _mono_gcd(a, b)
    if _is_monomial(b):
        return _mono_gcd(b, a)
    va, vb = a.vars(), b.vars()
    if len(va | vb) == 1:
        i = next(iter(va | vb))
        if _coprime_mod_p(a, b, i):
            return Poly.const(1, a.nv)
        return _uni_gcd(a, b, i)
    i = _main_var(a, b)
    da, db = a.deg(i), b.deg(i)
    if da == 0:
        return poly_gcd(a, content(b, i))
    if db == 0:
        return poly_gcd(content(a, i), b)
    ca, cb = content(a, i), content(b, i)
    gc = poly_gcd(ca, cb)
    pa, pb = divexact(a, ca), divexact(b, cb)
    if pa.deg(i) < pb.deg(i):
        pa, pb = pb, pa
    while not pb.is_zero() and pb.deg(i) > 0:
        r = prem(pa, pb, i)
        pa = pb
        pb = Poly(a.nv) if r.is_zero() else primitive(r, i)
    g = pa if pb.is_zero() else Poly.const(1, a.nv)
    if g.deg(i) <= 0:
        g = Poly.const(1, a.nv)
    else:
        g = primitive(g, i)
    return (gc * g).int_primitive()


def squarefree_part(p):
    """the squarefree part (product of the distinct irreducible factors up to a unit), integer primitive"""
    if p.is_const():
        return Poly.const(1, p.nv)
    if _is_monomial(p):
        e = next(iter(p.t))
        return Poly(p.nv, {tuple(1 if a else 0 for a in e): F(1)})
    i = _main_var(p)
    c = content(p, i)
    pp = divexact(p, c)
    g = poly_gcd(pp, pp.diff(i))
    s = divexact(pp, g)
    return (squarefree_part(c) * s).int_primitive()


def gcd_free_basis(polys, var=None):
    """a gcd-free basis (fact:res (5), con:coprime): pairwise coprime squarefree integer-primitive polynomials, none
    constant, such that each input is a rational times a product of their powers. With var given, polynomials of
    degree 0 in var are dropped (the kinds, as primitive parts in var); else only constants are dropped. Computed
    by the gcd and squarefree moves, added one polynomial at a time; no factorization."""
    def dropped(p):
        return p.is_const() or (var is not None and p.deg(var) <= 0)

    basis = []
    for p in polys:
        if p.is_zero():
            continue
        if var is not None:
            if p.deg(var) <= 0:
                continue
            p = primitive(p, var)
        p = p.int_primitive()
        # the squarefree move, repeated: p = s_1 s_2 ..., s_(i+1) | s_i
        work = []
        while not dropped(p):
            s = squarefree_part(p)
            work.append(s)
            p = divexact(p, s)
        for q in work:
            new = []
            for b in basis:
                if dropped(q):
                    new.append(b)
                    continue
                g = poly_gcd(q, b)
                if dropped(g) or g.is_const():
                    new.append(b)
                    continue
                # the gcd move: b -> g, b/g; q -> q/g
                new.append(g)
                rest = divexact(b, g).int_primitive()
                if not rest.is_const():
                    new.append(rest)
                q = divexact(q, g).int_primitive()
            if not dropped(q):
                new.append(q)
            basis = [b for b in new if not dropped(b)]
    return sorted(basis, key=lambda p: (p.deg(), p.key()))


def factor_over(p, basis):
    """(r, [m_b]) with p = r * prod_b b^(m_b), or None if p is not of that form"""
    m = [0] * len(basis)
    q = p
    for k, b in enumerate(basis):
        while True:
            d = divexact(q, b)
            if d is None:
                break
            q = d
            m[k] += 1
    if not q.is_const():
        return None
    return q.const_value(), m


# ---------------------------------------------------------------- determinants and resultants (eq:resbezout)

def _imul(a, b):
    out = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            out[e] = out.get(e, 0) + c1 * c2
    return {e: c for e, c in out.items() if c}


def _isub(a, b):
    out = dict(a)
    for e, c in b.items():
        v = out.get(e, 0) - c
        if v:
            out[e] = v
        else:
            out.pop(e, None)
    return out


def _idiv(a, b):
    """a / b for integer polynomials when b divides a in Z[x] (Bareiss), else None"""
    if not a:
        return {}
    eb = max(b)
    cb = b[eb]
    r = dict(a)
    q = {}
    bt = list(b.items())
    while r:
        er = max(r)
        cr = r[er]
        de = tuple(x - y for x, y in zip(er, eb))
        if min(de) < 0 or cr % cb:
            return None
        c = cr // cb
        q[de] = c
        for e, v in bt:
            e2 = tuple(x + y for x, y in zip(e, de))
            nvl = r.get(e2, 0) - c * v
            if nvl:
                r[e2] = nvl
            else:
                r.pop(e2, None)
    return q


def det(M, nv):
    """the determinant of a square matrix of polynomials over Q: rows scaled to integer coefficients, then
    fraction-free Bareiss elimination over Z[x] (exact divisions)"""
    n = len(M)
    if n == 0:
        return Poly.const(1, nv)
    scale = F(1)
    A = []
    for row in M:
        row = [x if isinstance(x, Poly) else Poly.const(x, nv) for x in row]
        den = 1
        for x in row:
            for c in x.t.values():
                den = lcm(den, c.denominator)
        scale /= den
        A.append([{e: int(c * den) for e, c in x.t.items()} for x in row])
    sign = 1
    prev = {(0,) * nv: 1}
    for k in range(n - 1):
        if not A[k][k]:
            piv = next((r for r in range(k + 1, n) if A[r][k]), None)
            if piv is None:
                return Poly(nv)
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        akk = A[k][k]
        for i in range(k + 1, n):
            aik = A[i][k]
            for j in range(k + 1, n):
                num = _isub(_imul(A[i][j], akk), _imul(aik, A[k][j]))
                q = _idiv(num, prev)
                if q is None:
                    raise ArithmeticError('Bareiss division failed')
                A[i][j] = q
            A[i][k] = {}
        prev = akk
    out = A[n - 1][n - 1]
    return Poly(nv, {e: F(c) * scale * sign for e, c in out.items()})


def sylvester(a, b, i):
    """the Sylvester matrix of a, b in the variable i: rows v^(m-1) a, ..., a, v^(r-1) b, ..., b (r = deg a,
    m = deg b), columns v^(r+m-1), ..., v^0"""
    r, m = a.deg(i), b.deg(i)
    ca, cb = a.coeffs(i), b.coeffs(i)
    n = r + m
    nv = a.nv
    rows = []
    for s in range(m):
        row = [Poly(nv) for _ in range(n)]
        for k, c in enumerate(ca):
            row[n - 1 - (k + m - 1 - s)] = c
        rows.append(row)
    for s in range(r):
        row = [Poly(nv) for _ in range(n)]
        for k, c in enumerate(cb):
            row[n - 1 - (k + r - 1 - s)] = c
        rows.append(row)
    return rows


def resultant(a, b, i, cofactors=False):
    """Res_v(a, b) for v the variable i (fact:res), deg_v a >= 1; with cofactors, also (U, V) with
    Res = U a + V b, deg_v U <= deg b - 1, deg_v V <= deg a - 1, from the last column of the adjugate"""
    r, m = a.deg(i), b.deg(i)
    nv = a.nv
    if r < 1:
        raise ValueError('deg a >= 1')
    if m == 0:
        res = b ** r
        if cofactors:
            return res, Poly(nv), b ** (r - 1)
        return res
    S = sylvester(a, b, i)
    res = det(S, nv)
    if not cofactors:
        return res
    n = r + m
    xi = Poly.var(i, nv)
    U, V = Poly(nv), Poly(nv)
    for row in range(n):
        minor = [[S[rr][cc] for cc in range(n - 1)] for rr in range(n) if rr != row]
        cof = det(minor, nv) * (1 if (row + n - 1) % 2 == 0 else -1)
        if row < m:
            U = U + cof * xi ** (m - 1 - row)
        else:
            V = V + cof * xi ** (r - 1 - (row - m))
    return res, U, V


def cofactor_bound(a, b, i, ranges):
    """a bound on |U| and |V| of eq:resbezout on the box prod [-ranges, ranges], without computing them:
    each entry of the adjugate is a minor of the Sylvester matrix, at most the product of the l1 norms of its rows
    (Hadamard), and U = sum_r cof_r v^(m-1-r)"""
    S = sylvester(a, b, i)
    n = len(S)
    norms = [sum((abs_bound(x, ranges) for x in row), F(0)) for row in S]
    tot = F(1)
    for v in norms:
        tot *= max(v, F(1))
    R = max(F(ranges[i]), F(1))
    return tot * n * R ** n


def abs_bound(p, ranges):
    """a rational M >= |p| on the box prod_i [-ranges[i], ranges[i]] (sum of the moduli of the terms)"""
    s = F(0)
    for e, c in p.t.items():
        v = abs(c)
        for i, a in enumerate(e):
            if a:
                v *= F(ranges[i]) ** a
        s += v
    return s
