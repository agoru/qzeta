"""Tests of qpp/pin.py: the pins of qpp/lean/QppKernel/Pin.lean in exact arithmetic."""

from fractions import Fraction as F

from qpp import pin as P


def sq_minus_two():
    # y^2 - 2 in one variable
    return [P.poly({(2,): 1, (0,): -2})]


def test_the_pin_of_the_lean_example():
    """QppTests/Pin.lean: N y = y - (y^2 - 2)/3 on |y - 3/2| <= 1/10 passes with q = 1/15, a = 1/12"""
    cert = P.test(sq_minus_two(), [0], [F(3, 2)], F(1, 10), [[F(1, 3)]])
    assert cert["q"] == F(1, 15) and cert["a"] == F(1, 12) and cert["passes"]
    ys = P.iterates(sq_minus_two(), [0], [[F(1, 3)]], [F(3, 2)], 6)
    for L, y in enumerate(ys):
        assert abs(y[0] ** 2 - 2) <= 3 * F(1, 15) ** L * F(1, 12)  # sqrt_two_level


def test_a_wide_box_fails():
    cert = P.test(sq_minus_two(), [0], [F(3, 2)], F(2), [[F(1, 3)]])  # q = 4/3
    assert not cert["passes"]


def test_the_irrational_directions_of_two_moments():
    """the first two moments at (-4, 2, 3), p = 2, vanish together only at directions with
    delta_2/delta_3 = (3 +- sqrt 6)/2, the roots of t^2 - 3t + 3/4; each is pinned by a rational box"""
    f = [P.poly({(2,): 1, (1,): -3, (0,): F(3, 4)})]
    for x0 in (F(27, 10), F(3, 10)):
        pin = P.find(f, [0], [x0])
        assert pin is not None and pin["passes"]
        assert P.check_pin(f, [0], pin, L=5, samples=P.grid(pin["centre"], [0], pin["R"], 8)) == []


def test_a_pin_of_two_equations():
    """x^2 + y^2 = 5, x y = 2 pinned at (2, 1); the tangency of x^2 + y^2 = 2, x y = 1 at (1, 1) has no pin"""
    f = [P.poly({(2, 0): 1, (0, 2): 1, (0, 0): -5}), P.poly({(1, 1): 1, (0, 0): -2})]
    pin = P.find(f, [0, 1], [F(21, 10), F(9, 10)])
    assert pin is not None
    assert P.check_pin(f, [0, 1], pin, L=4, samples=P.grid(pin["centre"], [0, 1], pin["R"], 3)) == []
    # the singular point of x^2 + y^2 = 2, x y = 1 has no pin: its Jacobian is singular
    g = [P.poly({(2, 0): 1, (0, 2): 1, (0, 0): -2}), P.poly({(1, 1): 1, (0, 0): -1})]
    assert P.find(g, [0, 1], [F(1), F(1)]) is None


def test_a_pinned_curve_over_a_box_of_the_free_coordinate():
    """the circle x^2 + y^2 = 1, y pinned near 4/5 over x in [3/5 - 1/100, 3/5 + 1/100]: one test for every x"""
    f = [P.poly({(2, 0): 1, (0, 2): 1, (0, 0): -1})]
    box = [(F(59, 100), F(61, 100)), None]
    pin = P.find(f, [1], [F(3, 5), F(4, 5)], free_box=box)
    assert pin is not None
    for x in (F(59, 100), F(3, 5), F(61, 100)):
        c = [x, pin["centre"][1]]
        ys = P.iterates(f, [1], pin["A"], c, 6)
        for L in range(6):
            assert abs(ys[L][1] - ys[L + 1][1]) <= pin["q"] ** L * pin["a"]


def test_the_rank_form():
    """(2): on a pin, |A f(u)| = |u - N u| and |u - y_L| bound each other up to q^L (Pin.near_iter, Pin.near_step);
    so sum f_i^2 is comparable to |u - y_L|^2 there"""
    f = [P.poly({(2,): 1, (0,): -2})]
    pin = P.find(f, [0], [F(7, 5)])
    q, a = pin["q"], pin["a"]
    ys = P.iterates(f, [0], pin["A"], pin["centre"], 8)
    for u in P.grid(pin["centre"], [0], pin["R"], 10):
        e = abs(pin["A"][0][0] * P.evaluate(f[0], u))
        d = abs(u[0] - ys[8][0])
        assert d <= e / (1 - q) + q ** 8 * (a / (1 - q) + 2 * pin["R"])
        assert e <= (1 + q) * d + q ** 8 * a


def test_the_chart_of_a_pin():
    """(4): on a pin, u -> A f(u) changes distances by a factor between 1 - q and 1 + q (Pin.chart); the Lean
    example (QppTests/Pin.lean, sqrt_two_chart) and a pin of two equations"""
    f = sq_minus_two()
    pin = {"centre": [F(3, 2)], "A": [[F(1, 3)]], **P.test(f, [0], [F(3, 2)], F(1, 10), [[F(1, 3)]])}
    assert P.check_chart(f, [0], pin, P.grid(pin["centre"], [0], pin["R"], 12)) == []
    g = [P.poly({(2, 0): 1, (0, 2): 1, (0, 0): -5}), P.poly({(1, 1): 1, (0, 0): -2})]
    pin2 = P.find(g, [0, 1], [F(21, 10), F(9, 10)])
    assert P.check_chart(g, [0, 1], pin2, P.grid(pin2["centre"], [0, 1], pin2["R"], 3)) == []


def test_divided_differences_are_exact():
    f = P.poly({(3, 1): 2, (1, 2): -1, (0, 1): 5, (0, 0): 7})
    D = P.divided(f, 2, [0, 1])
    u, v = [F(3, 2), F(-2, 3)], [F(1, 5), F(7, 4)]
    lhs = P.evaluate(f, u) - P.evaluate(f, v)
    rhs = sum(P.evaluate(D[j], u + v) * (u[j] - v[j]) for j in range(2))
    assert lhs == rhs


def test_enclosures_contain_the_values():
    f = P.poly({(2, 1): 1, (0, 3): -2, (1, 0): 3})
    box = [(F(-1, 2), F(1)), (F(-1), F(1, 3))]
    lo, hi = P.enclose(f, box)
    for x in P.grid([F(1, 4), F(-1, 3)], [0, 1], F(2, 3), 6):
        if box[0][0] <= x[0] <= box[0][1] and box[1][0] <= x[1] <= box[1][1]:
            assert lo <= P.evaluate(f, x) <= hi
