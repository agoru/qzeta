"""The LP certificates of qpp/examples/programs.qpp: the kernel backend generates every row (the word LP, the row
at), the generated Lean reads the prices and the points as written, and qpp/lp.py checks the same certificates in
exact arithmetic at rational parameters; a wrong price or point is caught."""
from fractions import Fraction
from pathlib import Path

from qpp import kernel as K
from qpp import lp
from qpp import source as S
from qpp import texmath as T

ROOT = Path(__file__).resolve().parents[2]
EX = ROOT / "qpp" / "examples" / "programs.qpp"


def generated():
    return K.generate_all(S.read_file(EX), "QppGen.Programs", source="qpp/examples/programs.qpp")


def test_every_row_generates():
    g = generated()
    assert g.report and all(ok and why == "proved" for _, _, _, ok, why in g.report), \
        [r for r in g.report if not r[3]]
    labels = {(label, key) for label, key, _, _, _ in g.report}
    assert {("lem:typeone", "at"), ("lem:triangle", "at"), ("lem:twonodeA", "at"), ("lem:twonodeB", "at"),
            ("lem:silentprog", "at")} <= labels


def test_certificates_exact():
    progs = lp.programs(EX)
    assert {label for label, _, _ in progs} == {"lem:typeone", "lem:triangle", "lem:twonodeA", "lem:twonodeB",
                                                "lem:silentprog"}
    for label, P, data in progs:
        envs = list(P.samples())
        assert envs, label
        for env in envs:
            assert P.check(data, env) == [], (label, env)


def test_wrong_certificates_fail():
    progs = {label: (P, data) for label, P, data in lp.programs(EX)}
    P, _ = progs["lem:typeone"]
    assert P.check("1/2, 1/2, 1/4, 1/5", {}) == ["the coefficient of v_s in the slack is -1/5"]
    assert P.check("1/2, 1/2, 1/4, 1/7", {}) == ["the constant of the slack is -1/42"]
    P, data = progs["lem:twonodeA"]
    # without the price of the order row the slack of v_r is negative where eta K > 3
    assert P.check("1/2, 0, 1/2, (K + 1) / (3 + eta)", {"K": Fraction(3), "eta": Fraction(2)})
    P.points = [{"y": T.parse_qpp("1/2"), "v_r": T.parse_qpp("1/4"), "v_B": T.parse_qpp("1/4"),
                 "z": T.parse_qpp("1/4")}]
    assert any("leaves the row" in f or "the cost at" in f for f in P.check(data, {"K": Fraction(3),
                                                                                    "eta": Fraction(2)}))


def test_triangle_is_a_face_of_dimension_two():
    """m = 3: three affinely independent optimal points, and the two tight rows of rank two"""
    (P, _), = [(P, d) for label, P, d in lp.programs(EX) if label == "lem:triangle"]
    pts = [[lp.evaluate(pt[x], {}) for x in P.scales] for pt in P.points]
    d1 = [a - b for a, b in zip(pts[1], pts[0])]
    d2 = [a - b for a, b in zip(pts[2], pts[0])]
    assert any(d1[i] * d2[j] - d1[j] * d2[i] != 0 for i in range(4) for j in range(4))
    tight = [[1, 0, 0, 1], [0, 1, 1, 0]]  # v_s + v_y, v_x + v_t over (v_s, v_x, v_t, v_y)
    assert any(tight[0][i] * tight[1][j] - tight[0][j] * tight[1][i] != 0 for i in range(4) for j in range(4))
