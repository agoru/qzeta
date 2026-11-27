"""The identity check of the kernel (qpp/lean/QppKernel/Identity.lean), mirrored in Python.

`CExpr.check Rs a b`, with n = len(Rs) and the points pi_i (x_k = Rs[k] for k < i, x_k = 1 for k >= i): both sides
are below Rs[i] at pi_i for each i < n, and they agree at pi_n. `IsPol.eq_of_points` says that then the two sides
are the same polynomial with coefficients in the counts. The tactic `qeq` takes Rs[i] the least power of 2 above
both sides at pi_i (`radices` in Tactic.lean). On masses, `qeq` checks num(a) den(b) = num(b) den(a), the variable
i read as the numerator x(i+1) over the denominator x0 common to all (`MExpr.numDen`, `MExpr.cross` in Mass.lean).

A polynomial here is a dict from exponent tuples to positive integers.
"""
import importlib.util
import itertools
import random
from fractions import Fraction
from pathlib import Path


def evaluate(p, x):
    total = 0
    for e, c in p.items():
        term = c
        for xi, k in zip(x, e):
            term *= xi ** k
        total += term
    return total


def point(Rs, i, n):
    return [Rs[k] if k < i else 1 for k in range(n)]


def check(Rs, f, g):
    """CExpr.check: the bounds at pi_0, ..., pi_{n-1} and the agreement at pi_n"""
    n = len(Rs)
    for i in range(n):
        x = point(Rs, i, n)
        if not (evaluate(f, x) < Rs[i] and evaluate(g, x) < Rs[i]):
            return False
    x = point(Rs, n, n)
    return evaluate(f, x) == evaluate(g, x)


def radices(n, f, g):
    """the radices of qeq: each the least power of 2 above both sides at its point"""
    Rs = []
    for i in range(n):
        x = point(Rs + [1] * (n - i), i, n)
        Rs.append(2 ** max(evaluate(f, x), evaluate(g, x)).bit_length())
    return Rs


def random_poly(rng, n, degree, terms, coeff):
    p = {}
    for _ in range(terms):
        e = tuple(rng.randint(0, degree) for _ in range(n))
        p[e] = p.get(e, 0) + rng.randint(1, coeff)
    return p


def mul(p, q):
    out = {}
    for (e, c), (f, d) in itertools.product(p.items(), q.items()):
        m = tuple(a + b for a, b in zip(e, f))
        out[m] = out.get(m, 0) + c * d
    return out


def add(p, q):
    out = dict(p)
    for e, c in q.items():
        out[e] = out.get(e, 0) + c
    return out


def test_radices_pass_on_identities():
    rng = random.Random(1)
    for _ in range(200):
        n = rng.randint(1, 3)
        p, q, r = (random_poly(rng, n, 3, rng.randint(1, 4), 9) for _ in range(3))
        f = mul(add(p, q), r)
        g = add(mul(r, q), mul(p, r))
        assert check(radices(n, f, g), f, g)


def test_radices_fail_on_one_monomial_off():
    rng = random.Random(2)
    for _ in range(200):
        n = rng.randint(1, 3)
        f = random_poly(rng, n, 3, rng.randint(1, 5), 9)
        g = add(f, {tuple(rng.randint(0, 3) for _ in range(n)): 1})
        assert not check(radices(n, f, g), f, g)


def test_no_radices_pass_a_non_identity():
    """IsPol.eq_of_points: whatever the radices, the check never passes on two different polynomials"""
    rng = random.Random(3)
    for _ in range(300):
        n = rng.randint(1, 2)
        f = random_poly(rng, n, 2, rng.randint(1, 3), 3)
        g = random_poly(rng, n, 2, rng.randint(1, 3), 3)
        if f == g:
            continue
        for Rs in itertools.product(range(2, 40), repeat=n):
            assert not check(list(Rs), f, g), (f, g, Rs)


def test_the_bounds_are_needed():
    """x0 and 4 agree at x0 = 4; the bound at pi_0 (x0 = 1) rejects the radix 4"""
    f, g = {(1,): 1}, {(0,): 4}
    assert evaluate(f, [4]) == evaluate(g, [4])
    assert not check([4], f, g)
    assert not check(radices(1, f, g), f, g)


def num_den(e, n):
    """MExpr.numDen over n + 1 count variables: ("var", i), ("num", c), ("add" | "mul" | "div", a, b)"""
    def mon(i):
        return {tuple(int(k == i) for k in range(n + 1)): 1}
    if e[0] == "var":
        return mon(e[1] + 1), mon(0)
    if e[0] == "num":
        return {(0,) * (n + 1): e[1]}, {(0,) * (n + 1): 1}
    (p, q), (r, s) = num_den(e[1], n), num_den(e[2], n)
    if e[0] == "add":
        return add(mul(p, s), mul(r, q)), mul(q, s)
    if e[0] == "mul":
        return mul(p, r), mul(q, s)
    return mul(p, s), mul(q, r)


def test_masses_by_cross_products():
    """Tarski's axiom x / (y / (z / (x / y))) = z passes, and a wrong identity fails, on the cross products"""
    x, y, z = ("var", 0), ("var", 1), ("var", 2)
    lhs = ("div", x, ("div", y, ("div", z, ("div", x, y))))
    for a, b, holds in [(lhs, z, True), (("add", ("div", x, y), ("num", 1)), ("div", ("add", x, y), x), False)]:
        (p, q), (r, s) = num_den(a, 3), num_den(b, 3)
        f, g = mul(p, s), mul(r, q)
        assert check(radices(4, f, g), f, g) == holds
    rng = random.Random(4)
    for _ in range(100):
        u, v, w = (Fraction(rng.randint(1, 50), rng.randint(1, 50)) for _ in range(3))
        assert u / (v / (w / (u / v))) == w


def test_generated_farkas_is_current():
    """QppTests/Farkas.lean is the output of QppTests/farkas.py (the exact simplex and the Bernstein splits)"""
    path = Path(__file__).resolve().parents[1] / "lean" / "QppTests" / "farkas.py"
    spec = importlib.util.spec_from_file_location("qpp_lean_farkas", path)
    gen = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gen)
    assert gen.OUT.read_text(encoding="utf-8") == gen.render()
