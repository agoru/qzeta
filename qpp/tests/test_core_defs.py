"""The definitions D1-D7 of the kernel (qpp/lean/QppKernel), mirrored in exact arithmetic.

Each test names the Lean declarations it mirrors. Masses are positive Fractions; an absent value (no zero) is None.
"""
import itertools
import random
from fractions import Fraction

import pytest

RNG = random.Random(20261109)


def mass(rng=RNG, hi=9):
    return Fraction(rng.randint(1, hi), rng.randint(1, hi))


# D1: sums and products over counts (Sum.lean)


def test_sum_to_id():
    """`sumTo_id`: 2 * sum_{i <= n} i = n (n + 1), sums over the counts 1..n"""
    for n in range(1, 60):
        assert 2 * sum(range(1, n + 1)) == n * (n + 1)


def test_prod_to_mul():
    """`prodTo_mul`: products over 1..n of f g split"""
    for n in range(1, 12):
        f = [mass() for _ in range(n)]
        g = [mass() for _ in range(n)]
        pf = pg = pfg = Fraction(1)
        for a, b in zip(f, g):
            pf, pg, pfg = pf * a, pg * b, pfg * a * b
        assert pfg == pf * pg


# D2: finite supports (Poly.lean). A polynomial is a list of (exponents, mass); trailing zeros do not count.


def trim(m):
    m = list(m)
    while m and m[-1] == 0:
        m.pop()
    return tuple(m)


def coeff(p, m):
    """`Poly.coeff`: the sum of the coefficients of the terms with monomial m, None if there are none"""
    cs = [c for (e, c) in p if trim(e) == trim(m)]
    return sum(cs) if cs else None


def ev(p, x):
    """`Poly.eval`: None for the polynomial with no terms"""
    if not p:
        return None
    total = Fraction(0)
    for e, c in p:
        t = c
        for i, k in enumerate(e):
            t *= x[i] ** k
        total += t
    return total


def pmul(p, q):
    """`Poly.mul`: term by term, the exponents added (`Mon.mul`)"""
    out = []
    for e, c in p:
        for f, d in q:
            n = max(len(e), len(f))
            out.append((tuple((e[i] if i < len(e) else 0) + (f[i] if i < len(f) else 0) for i in range(n)), c * d))
    return out


def rand_poly(n=3, deg=3, terms=4):
    return [(tuple(RNG.randint(0, deg) for _ in range(RNG.randint(0, n))), mass()) for _ in range(terms)]


def test_poly_eval_mul_append():
    """`Poly.eval_mul`, `Poly.eval_append`, `Poly.coeff_append`"""
    for _ in range(200):
        p, q = rand_poly(), rand_poly()
        x = [mass() for _ in range(3)]
        assert ev(pmul(p, q), x) == ev(p, x) * ev(q, x)
        assert ev(p + q, x) == ev(p, x) + ev(q, x)
        for m in {trim(e) for e, _ in p + q}:
            a, b = coeff(p, m), coeff(q, m)
            assert coeff(p + q, m) == (a or 0) + (b or 0)


def test_trailing_zeros_do_not_count():
    """`Mon.trim`: x0 and x0 * x1^0 are one monomial"""
    assert coeff([((1, 0), Fraction(2)), ((1,), Fraction(3))], (1,)) == 5
    assert coeff([((1,), Fraction(1))], (2,)) is None


# D3: pairs with ties (Bal.lean). <l, r> stands for l - r; ties are l + r' = l' + r.


def tie(a, b):
    return a[0] + b[1] == b[0] + a[1]


def badd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def bmul(a, b):
    return (a[0] * b[0] + a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def test_pairs_are_the_rationals():
    """`Mass.bal_add_tie`, `bal_mul_tie`, `bal_of_add`, `bal_of_mul`, `bal_level_add`, `bal_trichotomy`"""
    val = lambda a: a[0] - a[1]
    of = lambda x: (x + 1, Fraction(1))
    level = (Fraction(1), Fraction(1))
    for _ in range(300):
        a, b, c = (mass(), mass()), (mass(), mass()), (mass(), mass())
        assert val(badd(a, b)) == val(a) + val(b)
        assert val(bmul(a, b)) == val(a) * val(b)
        assert tie(badd(level, a), a)
        assert tie(a, b) == (val(a) == val(b))
        # ties are congruences
        a2 = (a[0] + c[0], a[1] + c[0])
        assert tie(a, a2) and tie(bmul(a, b), bmul(a2, b)) and tie(badd(a, b), badd(a2, b))
        x, y = mass(), mass()
        assert tie(badd(of(x), of(y)), badd(of(x + y), level))
        assert val(bmul(of(x), of(y))) == x * y
        assert sum([val(a) < val(b), val(a) == val(b), val(b) < val(a)]) == 1


def test_counts_pairs_are_the_integers():
    """`Count.bal_*`: pairs of counts, with ties, are the integers"""
    for _ in range(300):
        a = (RNG.randint(1, 20), RNG.randint(1, 20))
        b = (RNG.randint(1, 20), RNG.randint(1, 20))
        assert (a[0] - a[1]) * (b[0] - b[1]) == bmul(a, b)[0] - bmul(a, b)[1]


# D4: least and greatest by relation (MinMax.lean)


def is_least(m, l, le=lambda a, b: a <= b):
    return m in l and all(le(m, x) for x in l)


def test_least_exists_and_is_unique():
    """`Mass.exists_isLeast`, `isLeast_unique`, `exists_isMin`, `isMin_unique`, `exists_isLeast_bal` (up to ties)"""
    for _ in range(200):
        l = [mass() for _ in range(RNG.randint(1, 8))]
        ms = [m for m in l if is_least(m, l)]
        assert ms and len(set(ms)) == 1
        pairs = [(mass(), mass()) for _ in range(RNG.randint(1, 8))]
        least = [m for m in pairs if all(m[0] - m[1] <= x[0] - x[1] for x in pairs)]
        assert least and all(tie(least[0], m) for m in least)


# D6: the two quantifier patterns (Patterns.lean)


def within(c, C, f, g, levels):
    return all(c * g(i) <= f(i) <= C * g(i) for i in levels)


def test_within_trans_symm():
    """`Within.trans` (constants multiply), `Within.symm` (1/C, 1/c), `Within.refl`"""
    levels = range(1, 40)
    f = lambda i: Fraction(3 * i + 1, 2)
    g = lambda i: Fraction(i)
    h = lambda i: Fraction(i, 5)
    assert within(Fraction(1), Fraction(1), f, f, levels)
    assert within(Fraction(3, 2), Fraction(2), f, g, levels)
    assert within(Fraction(5), Fraction(5), g, h, levels)
    assert within(Fraction(3, 2) * 5, Fraction(2) * 5, f, h, levels)
    assert within(1 / Fraction(2), 1 / Fraction(3, 2), g, f, levels)


def test_asymp_unif_not():
    """`asympUnif_not`: n is comparable to 1 for each n, with C = n, but no C works for every n (`Mass.arch`)"""
    for C in [Fraction(7, 3), Fraction(100), Fraction(10 ** 6, 7)]:
        n = int(C) + 1
        assert not n <= C * 1
    assert all(n <= n * 1 and n * 1 <= n for n in range(1, 50))


# D7: the integral of a law (Law.lean)


def integral_term(u, v, k, c):
    """`Poly.integralTerm`: c (v^(k+1) - u^(k+1)) / (k+1)"""
    return c * (v ** (k + 1) - u ** (k + 1)) / (k + 1)


def integral(u, v, p):
    """`Poly.integral` on a polynomial in x0: the sum of its terms"""
    return sum((integral_term(u, v, (e[0] if e else 0), c) for e, c in p), Fraction(0))


def test_integral_split():
    """`Poly.integralTerm_split`, `Poly.integral_split`, `Poly.integral_append`"""
    for _ in range(200):
        p = [((RNG.randint(0, 5),), mass()) for _ in range(RNG.randint(1, 5))]
        q = [((RNG.randint(0, 5),), mass()) for _ in range(RNG.randint(1, 5))]
        u, v, w = sorted(mass() for _ in range(3))
        assert integral(u, v, p) + integral(v, w, p) == integral(u, w, p)
        assert integral(u, v, p + q) == integral(u, v, p) + integral(u, v, q)


def test_integral_is_the_antiderivative():
    """`Poly.integralTerm`: the integral of x^k on [0, 1] is 1/(k+1)"""
    for k in range(6):
        assert integral(Fraction(0), Fraction(1), [((k,), Fraction(1))]) == Fraction(1, k + 1)


def test_uniform_mean():
    """`Law.uniform_mean`: the mean of the uniform law on [0, 1] is 1/2"""
    assert integral(Fraction(0), Fraction(1), [((1,), Fraction(1))]) == Fraction(1, 2)


def test_law_with_atoms():
    """`Law.integral`: an atom of mass 1/3 at 2 and a cell [0, 1] with density 2x, integrating g = x"""
    atoms = [(Fraction(2), Fraction(1, 3))]
    cells = [(Fraction(0), Fraction(1), [((1,), Fraction(2))])]
    g = [((1,), Fraction(1))]
    total = sum(pi * ev(g, [x]) for x, pi in atoms)
    for u, v, dens in cells:
        total += integral(u, v, pmul(g, dens))
    assert total == Fraction(2, 3) + Fraction(2, 3)


# The cited fact (Cite.lean): Polya's theorem, checked on a fixture


def test_polya_fixture():
    """`polya`: x^2 - x y + y^2 is positive on the simplex; times (x + y)^3 every monomial of degree 5 is present"""
    pos = {(2, 0): 1, (0, 2): 1}
    neg = {(1, 1): 1}
    def times_sum(p):
        out = {}
        for (a, b), c in p.items():
            for e in [(a + 1, b), (a, b + 1)]:
                out[e] = out.get(e, 0) + c
        return out
    for _ in range(3):
        pos, neg = times_sum(pos), times_sum(neg)
    diff = {e: pos.get(e, 0) - neg.get(e, 0) for e in set(pos) | set(neg)}
    assert all(diff.get((a, 5 - a), 0) > 0 for a in range(6))
    # and N = 2 is not enough: the coefficient of x^2 y^2 is absent
    pos, neg = {(2, 0): 1, (0, 2): 1}, {(1, 1): 1}
    for _ in range(2):
        pos, neg = times_sum(pos), times_sum(neg)
    assert pos.get((2, 2), 0) - neg.get((2, 2), 0) == 0
    # positive on every face: at (1, 0), (0, 1) and inside
    for x, y in [(1, 0), (0, 1)] + [(mass(), mass()) for _ in range(50)]:
        assert x * x - x * y + y * y > 0
