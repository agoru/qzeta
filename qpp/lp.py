"""lp: the exact check, in Python, of the LP certificates of a Q++ 0.2 source (the word `LP` and the row `at` of the
generator, qpp/kernel.py).

A program is an item whose given declares its scales in `QQ>=0` and its parameters in other sets; its rows are the
hypotheses of the given on the scales, the other hypotheses bound the parameters. Its first row `cost >= value`
is the lower bound, proved by `LP[p_1, ..., p_J; extra]`: the prices of the rows in order, then further data, each a
term times hypotheses `h_k` (a product of the hypothesis with the rest, as `V` reads it). Weak duality is the check
here: at values of the parameters that satisfy their hypotheses, the slack

    cost(v) - value - sum_j p_j (row_j(v) - rhs_j) - sum extra(v)

is affine in the scales with no negative coefficient and no negative constant. The row `at: x := t, ...; ...` gives
points: each satisfies the rows and attains the value. Values are checked exactly (fractions) at a grid of rational
parameters; Lean checks the same certificate for every value (the generated theorems).
"""
import itertools
import re
from fractions import Fraction

from . import source as S
from . import texmath as T

GRID = [Fraction(1, 3), Fraction(1, 2), Fraction(1), Fraction(3, 2), Fraction(2), Fraction(3), Fraction(5)]


def evaluate(x, env):
    """the value of a Q++ term at the values env (names to fractions; a hypothesis h_k to its gap)"""
    k = x[0]
    if k == "num":
        return Fraction(x[1])
    if k == "var":
        if x[1] not in env:
            raise KeyError(x[1])
        return env[x[1]]
    if k == "paren":
        return evaluate(x[1], env)
    if k == "neg":
        return -evaluate(x[1], env)
    if k == "bin":
        a, b = evaluate(x[2], env), evaluate(x[3], env)
        return {"+": a + b, "-": a - b, "*": a * b, "/": a / b if b else None}[x[1]]
    if k == "pow":
        return evaluate(x[1], env) ** int(evaluate(x[2], env))
    raise ValueError(f"cannot evaluate {T.to_qpp(x)}")


def gap(rel, env):
    """the gap of a relation `a >= b` (a - b), `a <= b` (b - a), `a = b` (a - b) at env"""
    op, (a, b) = rel[1][0], rel[2]
    va, vb = evaluate(a, env), evaluate(b, env)
    return vb - va if op in ("<=", "<") else va - vb


class Program:
    """the program of an item: scales, parameters, the hypotheses h_k of its given (numbered as the kernel
    backend numbers them: the guard of each scale, then each relation), its rows, its cost and value"""

    def __init__(self, it):
        clauses = [c for p in T.parse_qpp_item(it.row("given").text) for c in (p[1] if p[0] == "and" else [p])]
        self.scales, self.params, self.hyps = [], [], {}
        n = 0
        for c in clauses:
            if c[0] == "decl":
                names = [v[1] for v in c[1]]
                if c[2] == ("set", "QQ>=0"):
                    for v in names:
                        n += 1
                        self.scales.append(v)
                        self.hyps[f"h_{n}"] = ("rel", (">=",), (("var", v), ("num", "0")))
                else:
                    self.params += names
            elif c[0] == "rel":
                n += 1
                self.hyps[f"h_{n}"] = c
        sc = set(self.scales)
        self.rows = [(h, c) for h, c in self.hyps.items() if c[0] == "rel" and not h_is_guard(c, sc)
                     and T_free(c) & sc]
        self.bounds = [c for h, c in self.hyps.items() if not (T_free(c) & sc)]
        self.cost = self.value = None
        for r in it.stmt_rows():
            if r.key in ("given", "origin", "names", "at") or T.is_core(r.key) or "?{" in r.text:
                continue
            x = T.parse_qpp_item(r.text)
            if len(x) == 1 and x[0][0] == "rel" and x[0][1] == (">=",):
                self.cost, self.value = x[0][2]
                break
        at = it.row("at")
        self.points = []
        if at is not None:
            for piece in at.text.split(";"):
                defs = [c for p in T.parse_qpp_item(piece) for c in (p[1] if p[0] == "and" else [p])]
                self.points.append({c[1][1]: c[2] for c in defs})

    def samples(self):
        """the parameter values of the grid that satisfy the bounds on the parameters"""
        for vals in itertools.product(GRID, repeat=len(self.params)):
            env = dict(zip(self.params, vals))
            if all(gap(b, env) >= 0 for b in self.bounds):
                yield env

    def check(self, data, env):
        """the failures of the certificate `LP[data]` and of the points at the parameter values env"""
        out = []
        parts = [p.strip() for p in split_top(data, ";")]
        prices = split_top(parts[0], ",")
        extra = split_top(parts[1], ",") if len(parts) > 1 else []
        if len(prices) != len(self.rows):
            return [f"{len(prices)} prices for {len(self.rows)} rows"]

        def term_value(t, v):
            """a datum (a term times hypotheses) at the scales v"""
            e = dict(env, **v)
            e.update({h: gap(c, e) for h, c in self.hyps.items()})
            return evaluate(T.parse_qpp(t), e)

        def slack(v):
            e = dict(env, **v)
            s = evaluate(self.cost, e) - evaluate(self.value, e)
            for p, (h, c) in zip(prices, self.rows):
                if p != "0":
                    pe = dict(env)
                    pe.update({hh: gap(cc, dict(env, **{x: Fraction(0) for x in self.scales}))
                               for hh, cc in self.hyps.items() if not (T_free(cc) & set(self.scales))})
                    s -= evaluate(T.parse_qpp(p), pe) * gap(c, e)
            for t in extra:
                s -= term_value(t, v)
            return s

        zero = {x: Fraction(0) for x in self.scales}
        s0 = slack(zero)
        if s0 < 0:
            out.append(f"the constant of the slack is {s0}")
        for x in self.scales:
            r = slack(dict(zero, **{x: Fraction(1)})) - s0
            if r < 0:
                out.append(f"the coefficient of {x} in the slack is {r}")
        for pt in self.points:
            v = {x: evaluate(t, env) for x, t in pt.items()}
            e = dict(env, **v)
            for h, c in self.rows:
                if gap(c, e) < 0:
                    out.append(f"the point {pt} leaves the row {h}")
            if evaluate(self.cost, e) != evaluate(self.value, e):
                out.append(f"the cost at {pt} is {evaluate(self.cost, e)}, not {evaluate(self.value, e)}")
        return out


def h_is_guard(c, scales):
    return c[1] == (">=",) and c[2][0][0] == "var" and c[2][0][1] in scales and c[2][1] == ("num", "0")


def T_free(x, out=None):
    out = set() if out is None else out
    if isinstance(x, tuple):
        if len(x) == 2 and x[0] == "var" and isinstance(x[1], str):
            out.add(x[1])
        else:
            for y in x:
                T_free(y, out)
    return out


def split_top(text, sep):
    out, depth, cur = [], 0, ""
    for ch in text:
        depth += ch in "([{"
        depth -= ch in ")]}"
        if ch == sep and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    out.append(cur.strip())
    return out


WORD = re.compile(r"^LP\[(.*)\]$")


def programs(path):
    """[(label, Program, data of its LP word)] of a Q++ 0.2 source"""
    doc = S.read_file(path)
    proofs = doc.proofs()
    out = []
    for it in doc.items():
        pr = proofs.get(it.label)
        for ln in (pr.lines if pr else []):
            m = WORD.match(ln.text.strip())
            if m:
                out.append((it.label, Program(it), m.group(1)))
    return out
