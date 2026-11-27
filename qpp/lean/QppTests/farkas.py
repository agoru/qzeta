"""Writes QppTests/Farkas.lean: certificates replayed by `farkas`.

* `lp_cover`: a covering LP, min c.x over A x >= b and x >= 0, with A, b, c random positive rationals. The exact
  simplex (qpp.simplex.lp_min, fact:elim) gives the optimum v and its multipliers y; over the masses the statement is
  "from b_i < A_i x for every i, v < c x", and the certificate is the y_i of the rows A_i x >= b_i (the multipliers
  of x >= 0 are the slack, which `farkas` finds).
* `box_bernstein`: p(x) = (x - 1)^2 (x - 3/2)^2 + 1/64 > 0 on 1/2 < x < 2, written balanced (P- < P+). On each
  box where the Bernstein coefficients of p are all positive, `farkas` closes the goal in the weights of the ends
  (`Mass.box`); elsewhere the box splits at its midpoint (`Mass.split`).

Usage (from the root of the repository): python3 qpp/lean/QppTests/farkas.py
"""
import random
import sys
from fractions import Fraction as F
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from qpp.simplex import lp_min, check_optimal  # noqa: E402

OUT = Path(__file__).resolve().parent / "Farkas.lean"


def num(q):
    q = F(q)
    return str(q.numerator) if q.denominator == 1 else f"({q.numerator} / {q.denominator})"


def lin(row, xs):
    terms = [xs[j] if a == 1 else f"{num(a)} * {xs[j]}" for j, a in enumerate(row) if a]
    return " + ".join(terms)


def lp_cover(n=20, m=30, seed=7):
    rng = random.Random(seed)
    xs = [f"x{j}" for j in range(n)]
    A = []
    for _ in range(m):
        row = [rng.choice([0, 0, 0, 1, 2, 3, F(1, 2), F(2, 3)]) for _ in range(n)]
        if not any(row):
            row[rng.randrange(n)] = 1
        A.append(row)
    b = [F(rng.randint(2, 19), rng.randint(1, 3)) for _ in range(m)]
    c = [rng.randint(1, 9) for _ in range(n)]
    nonneg = [([int(i == j) for i in range(n)], 0) for j in range(n)]
    ge = list(zip(A, b)) + nonneg
    r = lp_min(c, ge, (), n)
    assert r.status == "optimal" and check_optimal(c, ge, (), r.x, r.y_ge, r.y_eq)
    y = r.y_ge[:m]
    hyps = "\n    ".join(f"({'h' if y[i] else '_h'}{i} : {num(b[i])} < {lin(A[i], xs)})" for i in range(m))
    cert = ", ".join(f"{num(v)} \u2022 h{i}" if v != 1 else f"h{i}" for i, v in enumerate(y) if v)
    used = sum(1 for v in y if v)
    doc = (f"A covering LP in {n} masses with {m} rows, solved by an exact simplex: optimum {r.value}, "
           f"{used} rows in the certificate.")
    return (f"/-- {doc} -/\ntheorem lp_cover ({' '.join(xs)} : Mass)\n    {hyps} :\n"
            f"    {num(r.value)} < {lin(c, xs)} := by\n  farkas [{cert}]\n")


def poly():
    """p = (x - 1)^2 (x - 3/2)^2 + 1/64 as a list of rational coefficients, constant first"""
    def mul(p, q):
        out = [F(0)] * (len(p) + len(q) - 1)
        for i, u in enumerate(p):
            for j, v in enumerate(q):
                out[i + j] += u * v
        return out
    p = mul(mul([F(-1), F(1)], [F(-1), F(1)]), mul([F(-3, 2), F(1)], [F(-3, 2), F(1)]))
    p[0] += F(1, 64)
    return p


def bernstein(p, lo, hi):
    """the Bernstein coefficients of p on [lo, hi]"""
    d = len(p) - 1
    # q(t) = p(lo + (hi - lo) t), then b_k = sum_{i <= k} C(k, i) / C(d, i) q_i
    q = [F(0)] * (d + 1)
    for i, a in enumerate(p):
        for j in range(i + 1):
            q[j] += a * comb(i, j) * lo ** (i - j) * (hi - lo) ** j
    return [sum(F(comb(k, i), comb(d, i)) * q[i] for i in range(k + 1)) for k in range(d + 1)]


def side(coeffs):
    terms = []
    for k, a in enumerate(coeffs):
        if a == 0:
            continue
        mon = "" if k == 0 else ("x" if k == 1 else f"x ^ {k}")
        terms.append(num(a) if not mon else (mon if a == 1 else f"{num(a)} * {mon}"))
    return " + ".join(terms)


def proof(p, lo, hi, indent, stats):
    if all(v > 0 for v in bernstein(p, lo, hi)):
        stats["leaves"] += 1
        return [f"{indent}obtain \u27e8c, c', rfl\u27e9 := Mass.box h1 h2", f"{indent}farkas"]
    mid = (lo + hi) / 2
    stats["splits"] += 1
    lines = [f"{indent}rcases Mass.split {num(mid)} h1 h2 with \u27e8h1, h2\u27e9 | rfl | \u27e8h1, h2\u27e9"]
    left = proof(p, lo, mid, indent + "  ", stats)
    right = proof(p, mid, hi, indent + "  ", stats)
    lines += [f"{indent}\u00b7 " + left[0].lstrip()] + left[1:]
    lines += [f"{indent}\u00b7 farkas"]
    lines += [f"{indent}\u00b7 " + right[0].lstrip()] + right[1:]
    return lines


def box_bernstein():
    p = poly()
    lo, hi = F(1, 2), F(2)
    pos = [a if a > 0 else F(0) for a in p]
    neg = [-a if a < 0 else F(0) for a in p]
    stats = {"leaves": 0, "splits": 0}
    body = "\n".join(proof(p, lo, hi, "  ", stats))
    doc = (f"(x - 1)^2 (x - 3/2)^2 + 1/64 > 0 on 1/2 < x < 2: {stats['splits']} splits, {stats['leaves']} boxes "
           f"with positive Bernstein coefficients.")
    return (f"/-- {doc} -/\ntheorem box_bernstein (x : Mass) (h1 : {num(lo)} < x) (h2 : x < {num(hi)}) :\n"
            f"    {side(neg)} < {side(pos)} := by\n{body}\n")


def render():
    body = "\n".join([lp_cover(), box_bernstein()])
    return (
        "module\n\npublic import QppKernel\n\n"
        "/-!\n# Certificates replayed by `farkas`\n\n"
        "Generated by `QppTests/farkas.py`: a covering LP solved by an exact simplex, and a positivity on a box "
        "by\nBernstein coefficients and splits. Do not edit.\n-/\n\n"
        "public section\n\nnamespace Qpp.Tests\n\n" + body + "\nend Qpp.Tests\n\nend\n")


def main():
    OUT.write_text(render(), encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)}: {len(OUT.read_text().splitlines())} lines")


if __name__ == "__main__":
    main()
