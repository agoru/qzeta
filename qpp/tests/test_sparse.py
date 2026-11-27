"""The sparse check of the kernel (qpp/lean/QppKernel/Sparse.lean), mirrored in Python.

A monomial prod x_i^e_i is packed into the key sum e_i W^i; a normal form is the list of (key, coefficient) by
increasing key. With W above the total degree of both sides the exponents are the base-W digits of the key, and
the product of two monomials is the sum of their keys with no carry (`SPoly.valid_add`), so equal normal forms mean
equal polynomials (`CExpr.eq_of_scheck`). The tactic takes W = max(deg a, deg b) + 1 (`chooseCheck`).
"""
import random
from collections import Counter

RNG = random.Random(9)


def rand_expr(n, depth):
    """an expression: ('var', i) | ('num', k) | ('add', a, b) | ('mul', a, b) | ('pow', a, k)"""
    if depth == 0 or RNG.random() < 0.25:
        return ('var', RNG.randrange(n)) if RNG.random() < 0.7 else ('num', RNG.randint(1, 4))
    op = RNG.choice(['add', 'add', 'mul', 'pow'])
    if op == 'pow':
        return ('pow', rand_expr(n, depth - 1), RNG.randint(0, 3))
    return (op, rand_expr(n, depth - 1), rand_expr(n, depth - 1))


def deg(e):
    """`CExpr.deg`"""
    t = e[0]
    if t == 'var':
        return 1
    if t == 'num':
        return 0
    if t == 'add':
        return max(deg(e[1]), deg(e[2]))
    if t == 'mul':
        return deg(e[1]) + deg(e[2])
    return e[2] * deg(e[1])


def expand(e, n):
    """the polynomial, a Counter from exponent tuples to coefficients"""
    t = e[0]
    if t == 'var':
        m = [0] * n
        m[e[1]] = 1
        return Counter({tuple(m): 1})
    if t == 'num':
        return Counter({(0,) * n: e[1]})
    if t == 'add':
        return expand(e[1], n) + expand(e[2], n)
    if t == 'mul':
        return _mul(expand(e[1], n), expand(e[2], n))
    out = Counter({(0,) * n: 1})
    for _ in range(e[2]):
        out = _mul(out, expand(e[1], n))
    return out


def _mul(p, q):
    out = Counter()
    for a, c in p.items():
        for b, d in q.items():
            out[tuple(x + y for x, y in zip(a, b))] += c * d
    return out


def nf(e, W):
    """`CExpr.nf`: the normal form with packed keys, sorted by key"""
    t = e[0]
    if t == 'var':
        return Counter({W ** e[1]: 1})
    if t == 'num':
        return Counter({0: e[1]})
    if t == 'add':
        return nf(e[1], W) + nf(e[2], W)
    if t == 'mul':
        p, q = nf(e[1], W), nf(e[2], W)
        out = Counter()
        for a, c in p.items():
            for b, d in q.items():
                out[a + b] += c * d
        return out
    out = Counter({0: 1})
    p = nf(e[1], W)
    for _ in range(e[2]):
        new = Counter()
        for a, c in out.items():
            for b, d in p.items():
                new[a + b] += c * d
        out = new
    return out


def key(m, W):
    return sum(x * W ** i for i, x in enumerate(m))


def test_keys_are_the_monomials():
    """`SPoly.valid_var`, `valid_add`, `CExpr.nf_spec`: with W > deg, the normal form is the expansion, key by key"""
    for _ in range(300):
        n = RNG.randint(1, 6)
        e = rand_expr(n, 4)
        W = deg(e) + 1
        packed = nf(e, W)
        expanded = expand(e, n)
        assert packed == Counter({key(m, W): c for m, c in expanded.items()})
        # the digits of each key are the exponents
        for m in expanded:
            k = key(m, W)
            assert [k // W ** i % W for i in range(n)] == list(m)


def test_the_degree_bound_is_needed():
    """with W at the degree, two monomials share a key: x0^2 and x1 for W = 2"""
    a = ('pow', ('var', 0), 2)
    b = ('var', 1)
    assert nf(a, 2) == nf(b, 2)
    assert nf(a, deg(a) + 1) != nf(b, deg(a) + 1)


def test_equal_forms_iff_identity():
    """`CExpr.scheck`: (x + y)^2 against x^2 + 2xy + y^2 passes, and fails with one coefficient off"""
    x, y = ('var', 0), ('var', 1)
    lhs = ('pow', ('add', x, y), 2)
    rhs = ('add', ('add', ('pow', x, 2), ('mul', ('num', 2), ('mul', x, y))), ('pow', y, 2))
    W = max(deg(lhs), deg(rhs)) + 1
    assert nf(lhs, W) == nf(rhs, W)
    off = ('add', ('add', ('pow', x, 2), ('mul', ('num', 3), ('mul', x, y))), ('pow', y, 2))
    assert nf(lhs, W) != nf(off, W)


def test_linear_cost():
    """the normal form of a linear identity in 400 variables has 400 terms (the dense size would be 2^400)"""
    n = 400
    e = ('var', 0)
    for i in range(1, n):
        e = ('add', e, ('mul', ('num', i + 1), ('var', i)))
    assert len(nf(e, 2)) == n
