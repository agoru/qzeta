"""Pins: the Krawczyk test over Q, in exact rational arithmetic (the Python side of qpp/lean/QppKernel/Pin.lean).

A pin of a polynomial system f = (f_1..f_r) in pinned coordinates y (the others, z, fixed at rational values or
ranging over a rational box) is a centre c, a radius R and a rational matrix A such that N(y) = y - A f(y) passes
the test of Krawczyk (doi:10.1007/BF02234767) and Moore (doi:10.1137/0714040) on the box |y - c| <= R:
N(u) - N(v) = M(u, v)(u - v), |M_ij| <= m_ij, max_i sum_j m_ij <= q < 1, and |N(c) - c| + q R <= R. The rational
iterates y_L of N from c then move by at most q^L a and pin the locus (Pin.pin in Lean). The bounds m_ij come from
the exact divided differences of f, enclosed by interval arithmetic over the box.

Polynomials are dicts {exponent tuple: Fraction} in n variables.
"""

from fractions import Fraction as F
from itertools import product


# polynomials ---------------------------------------------------------------------------------------------------

def poly(terms):
    """{exponents: coefficient}, zero coefficients dropped"""
    return {tuple(e): F(c) for e, c in terms.items() if F(c) != 0}


def var(i, n):
    return {tuple(1 if k == i else 0 for k in range(n)): F(1)}


def const(c, n):
    return {(0,) * n: F(c)} if c else {}


def add(p, q):
    out = dict(p)
    for e, c in q.items():
        out[e] = out.get(e, F(0)) + c
    return {e: c for e, c in out.items() if c != 0}


def scale(p, c):
    return {e: F(c) * v for e, v in p.items() if F(c) * v != 0}


def mul(p, q):
    out = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(a + b for a, b in zip(e1, e2))
            out[e] = out.get(e, F(0)) + c1 * c2
    return {e: c for e, c in out.items() if c != 0}


def evaluate(p, x):
    total = F(0)
    for e, c in p.items():
        t = c
        for xi, k in zip(x, e):
            if k:
                t *= F(xi) ** k
        total += t
    return total


def deriv(p, i):
    out = {}
    for e, c in p.items():
        if e[i]:
            d = list(e)
            d[i] -= 1
            out[tuple(d)] = out.get(tuple(d), F(0)) + c * e[i]
    return {e: c for e, c in out.items() if c != 0}


# intervals: exact enclosures over a box --------------------------------------------------------------------------

def ipow(lo, hi, k):
    """the exact range of t^k on [lo, hi]"""
    if k == 0:
        return F(1), F(1)
    a, b = lo ** k, hi ** k
    if k % 2 == 0 and lo <= 0 <= hi:
        return F(0), max(a, b)
    return min(a, b), max(a, b)


def imul(a, b):
    ps = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(ps), max(ps)


def enclose(p, box):
    """an interval containing p on the box (a list of (lo, hi)), monomial by monomial"""
    lo = hi = F(0)
    for e, c in p.items():
        t = (F(1), F(1))
        for (a, b), k in zip(box, e):
            if k:
                t = imul(t, ipow(F(a), F(b), k))
        t = (c * t[0], c * t[1]) if c > 0 else (c * t[1], c * t[0])
        lo, hi = lo + t[0], hi + t[1]
    return lo, hi


def absmax(iv):
    return max(abs(iv[0]), abs(iv[1]))


# divided differences ---------------------------------------------------------------------------------------------

def divided(p, n, pinned):
    """the divided differences of p in the pinned coordinates, as polynomials in 2n variables (u, v):
    p(u) - p(v) = sum_j D_j(u, v) (u_j - v_j) when u and v agree off the pinned coordinates (the staircase: the
    j-th pinned coordinate moves from v_j to u_j, the earlier ones at u, the later ones at v)"""
    out = []
    for jj, j in enumerate(pinned):
        D = {}
        for e, c in p.items():
            k = e[j]
            if k == 0:
                continue
            # (u_j^k - v_j^k) / (u_j - v_j) = sum_{t<k} u_j^t v_j^(k-1-t); the other pinned coordinates of the
            # monomial at u (earlier ones) or v (later ones); the free coordinates at u (= v)
            for t in range(k):
                ue, ve = [0] * n, [0] * n
                for i in range(n):
                    if i == j:
                        ue[i], ve[i] = t, k - 1 - t
                    elif i in pinned and pinned.index(i) > jj:
                        ve[i] = e[i]
                    else:
                        ue[i] = e[i]
                key = tuple(ue) + tuple(ve)
                D[key] = D.get(key, F(0)) + c
        out.append({e: c for e, c in D.items() if c != 0})
    return out


# matrices --------------------------------------------------------------------------------------------------------

def inverse(Jm):
    """the exact inverse of a square rational matrix (Gauss-Jordan); None when singular"""
    r = len(Jm)
    a = [[F(x) for x in row] + [F(int(i == k)) for k in range(r)] for i, row in enumerate(Jm)]
    for col in range(r):
        piv = next((i for i in range(col, r) if a[i][col] != 0), None)
        if piv is None:
            return None
        a[col], a[piv] = a[piv], a[col]
        pv = a[col][col]
        a[col] = [x / pv for x in a[col]]
        for i in range(r):
            if i != col and a[i][col] != 0:
                f = a[i][col]
                a[i] = [x - f * y for x, y in zip(a[i], a[col])]
    return [row[r:] for row in a]


def dyadic(x, bits):
    """the nearest fraction with denominator 2^bits"""
    return F(round(F(x) * 2 ** bits), 2 ** bits)


# the test --------------------------------------------------------------------------------------------------------

def test(fs, pinned, centre, R, A, free_box=None):
    """the test of Krawczyk on the box |y - centre| <= R in the pinned coordinates (the free ones on free_box, a
    list of (lo, hi) per variable, ignored for pinned ones; or fixed at the centre's values). Returns the
    certificate {q, a, m, passes}: m_ij bounds |M_ij| = |delta_ij - sum_k A_ik D_kj| on the box twice over, q the
    largest row sum of m, a the largest |A f(centre)| over the free box"""
    n, r = len(centre), len(pinned)
    R = F(R)
    box = []
    for i in range(n):
        if i in pinned:
            box.append((F(centre[i]) - R, F(centre[i]) + R))
        elif free_box is not None:
            box.append(tuple(map(F, free_box[i])))
        else:
            box.append((F(centre[i]), F(centre[i])))
    D = [divided(f, n, pinned) for f in fs]  # D[k][j]: the divided difference of f_k in pinned coordinate j
    box2 = box + box
    m = []
    for i in range(r):
        row = []
        for j in range(r):
            Mij = const(int(i == j), 2 * n)
            for k in range(r):
                Mij = add(Mij, scale(D[k][j], -F(A[i][k])))
            row.append(absmax(enclose(Mij, box2)))
        m.append(row)
    q = max(sum(row) for row in m)
    cbox = [box[i] if i not in pinned else (F(centre[i]), F(centre[i])) for i in range(n)]
    Af = [{} for _ in range(r)]
    for i in range(r):
        for k in range(r):
            Af[i] = add(Af[i], scale(fs[k], F(A[i][k])))
    a = max(absmax(enclose(g, cbox)) for g in Af)
    return {"q": q, "a": a, "R": R, "m": m, "passes": q < 1 and a + q * R <= R}


def step(fs, pinned, A, y):
    """N(y) = y - A f(y) on the pinned coordinates"""
    fy = [evaluate(f, y) for f in fs]
    out = list(map(F, y))
    for ii, i in enumerate(pinned):
        out[i] = F(y[i]) - sum(F(A[ii][k]) * fy[k] for k in range(len(fs)))
    return out


def iterates(fs, pinned, A, centre, L):
    ys = [list(map(F, centre))]
    for _ in range(L):
        ys.append(step(fs, pinned, A, ys[-1]))
    return ys


def jacobian(fs, pinned, x):
    return [[evaluate(deriv(f, j), x) for j in pinned] for f in fs]


def find(fs, pinned, x0, bits=30, radii=None, free_box=None):
    """a pin about a rational approximation of a nondegenerate zero near x0: A the dyadic inverse of the Jacobian at
    the centre, R the first radius in radii (default 2^-1 ... 2^-40) that passes; None when none passes"""
    x = list(map(F, x0))
    for _ in range(8):  # rational Newton steps, rounded to keep the numbers small
        J = inverse(jacobian(fs, pinned, x))
        if J is None:
            return None
        x = [dyadic(v, bits) for v in step(fs, pinned, J, x)]
    J = inverse(jacobian(fs, pinned, x))
    if J is None:
        return None
    A = [[dyadic(v, bits) for v in row] for row in J]
    for R in radii or [F(1, 2 ** k) for k in range(1, 41)]:
        cert = test(fs, pinned, x, R, A, free_box)
        if cert["passes"]:
            return {"centre": x, "A": A, **cert}
    return None


def near(u, v, pinned):
    return max(abs(F(u[i]) - F(v[i])) for i in pinned)


def check_pin(fs, pinned, pin, L=6, samples=()):
    """the conclusions of Pin.pin at a pin, exactly: the iterates stay in the box and move by at most q^L a; at each
    sample u of the box (with |u - N u| = e), |u - y_L| <= (e + q^L a)/p + q^L 2R and
    |u - N u| <= (1 + q)|u - y_L| + q^L a. Returns the list of failures (empty when all hold)"""
    q, a, R, A, c = pin["q"], pin["a"], pin["R"], pin["A"], pin["centre"]
    p = 1 - q
    bad = []
    ys = iterates(fs, pinned, A, c, L + 1)
    for l in range(L + 1):
        if near(ys[l], c, pinned) > R:
            bad.append(("box", l))
        if near(ys[l], ys[l + 1], pinned) > q ** l * a:
            bad.append(("step", l))
    for u in samples:
        if near(u, c, pinned) > R:
            continue
        e = near(u, step(fs, pinned, A, u), pinned)
        for l in range(L + 1):
            d = near(u, ys[l], pinned)
            if d > (e + q ** l * a) / p + q ** l * 2 * R:
                bad.append(("below", l, u))
            if e > (1 + q) * d + q ** l * a:
                bad.append(("above", l, u))
    return bad


def check_chart(fs, pinned, pin, samples):
    """the chart of a pin (Pin.chart in Lean), exactly: for samples u, v of the box,
    (1 - q)|u - v| <= |A f(u) - A f(v)| <= (1 + q)|u - v|. Returns the failures"""
    q, A, R, c = pin["q"], pin["A"], pin["R"], pin["centre"]
    r = len(pinned)
    pts = [u for u in samples if near(u, c, pinned) <= R]

    def Af(u):
        fu = [evaluate(f, u) for f in fs]
        return [sum(F(A[i][k]) * fu[k] for k in range(len(fs))) for i in range(r)]

    vals = [Af(u) for u in pts]
    bad = []
    for a in range(len(pts)):
        for b in range(a + 1, len(pts)):
            d = near(pts[a], pts[b], pinned)
            w = max(abs(x - y) for x, y in zip(vals[a], vals[b]))
            if not (1 - q) * d <= w <= (1 + q) * d:
                bad.append((pts[a], pts[b]))
    return bad


def grid(centre, pinned, R, k):
    """the points of the box on a grid of k + 1 values per pinned coordinate"""
    axes = [[F(centre[i]) - R + 2 * R * F(t, k) for t in range(k + 1)] if i in pinned else [F(centre[i])]
            for i in range(len(centre))]
    return [list(x) for x in product(*axes)]
