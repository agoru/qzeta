"""ctxmodel: an exact model of the contexts of the pair, on which the cited rules over a context are evaluated.

A cited rule whose typed rows all apply a context (`coef(K, B, p)`, a relation that is a parameter of the statements)
has no concrete instance. The model gives it instances whose pair is computed exactly:

- a loss is a sum of monomials c * w^a with c a positive rational and even natural exponents a_i; in a fixture a list
  of blocks in separate variables, a block a monomial (a list of exponents, or {"c": "3/2", "exp": [2, 0]}) or a sum
  of monomials on the same variables, {"sum": [[2, 4], [4, 2]]};
- a region is a finite union of boxes prod [lo_i, hi_i] in the orthant with rational corners, lo_i < hi_i; in a
  fixture a list of boxes, a box a list of sides ["0", "2"];
- a weight is a tuple of positive naturals omega, the measure prod_i w_i^(omega_i) dw_i / w_i (1 without a
  weight, the content); a pair is "top" or [l, m];
- the pair of a loss on a box, at the corner where the variables that can be 0 (lo_i = 0) are 0, with b_j the
  exponents of its monomials there: top if some b_j = 0 (a monomial with no zero on the box), else the program of
  fact:readout(1), lambda = min <omega, v> over D = {v >= 0 : <b_j, v> >= 1} and m - 1 the dimension of the face of
  optimal v (Lin 2017, Theorems 4.8 and 4.10 with tau = omega - 1, by blocking duality); on a union of boxes the
  least (smaller l, at equal l larger m; Propositions 2.5 and 3.3), on the empty region top. For blocks of one
  monomial in separate variables this is (min omega_i / a_i, #argmin) per block, added.

The types of the vocabulary say what a name is: a type row of functions on points to QQ>=0 is a loss, set(...) a
region, (QQ>0)^n a tuple (a weight in a context), pair a pair. A context whose arguments are a loss, a region,
optionally a tuple, and a pair last is read as the graph of the model's pair. A fixture {"kind": "model", "rows":
[...]} gives in each row the names of the rule that are not pairs; a hypothesis coef(K, B, p) with p unbound binds p
(a family p_(j) by its quantified hypothesis). Each row holds, fails, is vacuous (a hypothesis is false) or
undecided; the fixture fails if a row fails or is undecided, or if none holds. A fixture {"kind": "witness", ...}
fails unless every row holds (the kind of the checker of the statements, carried as it is).

Usage: python3 -m qpp.ctxmodel SRC.qpp FIXDIR [--expect-fail]
  every fix line of a cited rule over a context of SRC, with the vocabulary of SRC only (qpp/modfix.py does the same
  for a module, with the vocabulary of the modules it uses); a cited rule over a context with no fix line fails. With
  --expect-fail (rules stated wrong) the run fails unless each fixture has a row that fails and none undecided.
A neqfix line `neqfix KEY ID` on a rule over a context names a fixture {"kind": "counterexample", "drop": [...], "rows":
[...]}: on every row the hypotheses kept hold, a dropped one fails and the conclusion fails (the hypothesis is needed).
An eqfix line `eqfix KEY ID` names a fixture {"kind": "values", "rows": [{..., "=": v}]}: on every row the hypotheses
hold and every side of the equation of the row is v.

A fixture may name a relation, {"graph": "coefficient", ...}: while it runs, that relation is read as the graph
of the model's pair, (K #coefficient lambda #multiplicity m #weight q #over B) when K has the pair (lambda, m), not
top, over B for the weight q, and the rule it checks is read on the model whatever its kind (a fact or a lemma of the
module). The name is refused unless the relation's parameters are a loss, a rational, a natural number, a tuple of
natural numbers and a region, in this order. Other relations keep their definition ((K #bdd B) by the least value of K
on B), so a row on top compares two computations. This tests the wording of a row, not the definition of the
coefficient: the definition is tied to the model's pair by lem:readoutlists(1), (2) and the rows unique and unique tie
of lem:pair, for a sum of monomials on a region between two cubes at the origin; on a box with a positive corner and on
a union of boxes the values are the classical ones cited above.

The rules on the coordinates of tuples and the lattice points of boxes are read on the model too: a tuple is a
list of rationals (of natural numbers for NN^n), `sum i, t` runs over its coordinates, `sum u <= b, t` over the points
of the box [0, b] by enumeration, `iverson(P)` is 1 or 0; such a rule needs no fix line. A quantifier over the
points of NN^n is read on the box that its clauses bound; with no such clause, at the one point s of a premise
F(u) = s, or, when its body is an identity of polynomials in the coordinates, on the grid {0..D}^n with D the
largest degree (which decides it); a quantifier over the points of a tuple type of QQ>=0 is read at the one point s
of a premise F(u) = s when s lies in the type, and holds (forall) or fails (exists) when it does not. Points are equal coordinate by coordinate. A function on points, a type row
Exponent(n) -> QQ>=0, Exponent(n) -> Exponent(r) or Exponent(n) -> Point(r), is a table {"table": [[point, value],
...]}; a point it does not list leaves the row undecided.
"""
import json
import re
from contextlib import contextmanager
from itertools import combinations, permutations, product
from math import comb
import sys
from fractions import Fraction as Fr
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    __package__ = "qpp"

from . import enumeration as EN
from . import source as S
from . import syntax as SY
from . import simplex as SX
from . import texmath as T
from .qpp2latex import vocab_tree

TOP = "top"


def is_table(a):
    """a square table of rationals: a tuple of n tuples of n rationals"""
    return isinstance(a, tuple) and all(isinstance(r, tuple) and len(r) == len(a) and all(isinstance(c, Fr) for c in r)
                                        for r in a)


def bidet(T, U):
    """the two halves (|(T, U)|^+, |(T, U)|^-) of the determinant of the couple of square tables (T, U), by Laplace's
    recursion along the first row as the kernel defines them (qpp/lean/QppKernel/Words.lean): (1, 0) on no rows; the
    halves of the minor of (1, j) exchanged at the even columns j, counted from 1. Each couple is checked against the
    sums over the permutations: |(T, U)|^+ - |(T, U)|^- = det(T - U) and |(T, U)|^+ + |(T, U)|^- = per(T + U)."""
    def rec(T, U):
        n = len(T)
        if n == 0:
            return Fr(1), Fr(0)
        P = M = Fr(0)
        for j in range(n):
            p, m = rec(tuple(tuple(r[b] for b in range(n) if b != j) for r in T[1:]),
                       tuple(tuple(r[b] for b in range(n) if b != j) for r in U[1:]))
            if j % 2:
                p, m = m, p
            P, M = P + T[0][j] * p + U[0][j] * m, M + T[0][j] * m + U[0][j] * p
        return P, M

    def perm_sums(A):
        n = len(A)
        EN.enumerating(f"the permutations of a table of {n} rows")
        even = odd = Fr(0)
        for s in permutations(range(n)):
            t = Fr(1)
            for i in range(n):
                t *= A[i][s[i]]
            inv = sum(1 for i in range(n) for j in range(i + 1, n) if s[i] > s[j])
            even, odd = (even + t, odd) if inv % 2 == 0 else (even, odd + t)
        return even, odd

    P, M = rec(T, U)
    n = len(T)
    de, do = perm_sums(tuple(tuple(T[i][j] - U[i][j] for j in range(n)) for i in range(n)))
    pe, po = perm_sums(tuple(tuple(T[i][j] + U[i][j] for j in range(n)) for i in range(n)))
    if P - M != de - do or P + M != pe + po:
        raise ValueError(f"the halves of the bideterminant of {T}, {U}: {P}, {M}, against det {de - do} and per "
                         f"{pe + po}")
    return P, M


class Undecided(Exception):
    """the model does not decide the row"""


class Coord:
    """a coordinate k (from 0) of the tuples of n coordinates, the value of an index bound over the coordinates
    (`sum i, t`, `forall i : P`): only an index, x_(i), never a number"""

    def __init__(self, k, n):
        self.k, self.n = k, n


# ---------------------------------------------------------------------------------------------------------
# values

class Loss:
    """a sum of blocks in separate variables, in the order of the variables; a block a sum of monomials c * w^a on its
    own variables (c a positive rational, a even natural exponents)"""

    def __init__(self, blocks):
        self.blocks = [[(Fr(c), tuple(a)) for c, a in b] for b in blocks]

    @property
    def n(self):
        return sum(len(b[0][1]) for b in self.blocks)

    @property
    def monos(self):
        """the monomials (c, a) of the loss, with their exponents on all its variables"""
        out, i = [], 0
        for b in self.blocks:
            k = len(b[0][1])
            out += [(c, (0,) * i + a + (0,) * (self.n - i - k)) for c, a in b]
            i += k
        return out

    def scaled(self, c):
        return Loss([[(c * d, a) for d, a in b] for b in self.blocks])


def rat(v):
    if isinstance(v, (float, bool)):
        raise Undecided(f"a rational is an int or a string such as \"3/2\" (a float is not exact): {v!r}")
    try:
        return Fr(str(v))
    except (ValueError, ZeroDivisionError):
        raise Undecided(f"not a rational: {v!r}")


def mono_of(m):
    c, a = (m.get("c", 1), m.get("exp")) if isinstance(m, dict) else (1, m)
    if not isinstance(a, list) or not a or any(not isinstance(x, int) or isinstance(x, bool) or x < 0 or x % 2
                                               for x in a):
        raise Undecided(f"a monomial has even natural exponents: {m!r}")
    if rat(c) <= 0:
        raise Undecided(f"a monomial has a positive coefficient: {m!r}")
    return rat(c), tuple(a)


def loss_of(v, n):
    if not isinstance(v, list) or not v:
        raise Undecided(f"a loss is a non-empty list of blocks: {v!r}")
    blocks = []
    for b in v:
        # a block: a monomial ([a_1, ...] or {"c": c, "exp": [...]}), or {"sum": [monomial, ...]} on the same variables
        ms = [mono_of(m) for m in b["sum"]] if isinstance(b, dict) and "sum" in b else [mono_of(b)]
        if not ms or len({len(a) for _, a in ms}) != 1:
            raise Undecided(f"the monomials of a block are on the same variables: {b!r}")
        blocks.append(ms)
    out = Loss(blocks)
    if n is not None and out.n != n:
        raise Undecided(f"a loss on {out.n} variables where the type has {n}")
    return out


def region_of(v, n):
    if not isinstance(v, list):
        raise Undecided(f"a region is a list of boxes: {v!r}")
    out = []
    for box in v:
        if not isinstance(box, list) or (n is not None and len(box) != n):
            raise Undecided(f"a box has {n} sides: {box!r}")
        sides = []
        for s in box:
            if not isinstance(s, list) or len(s) != 2:
                raise Undecided(f"a side is [lo, hi]: {s!r}")
            lo, hi = rat(s[0]), rat(s[1])
            if not 0 <= lo < hi:
                raise Undecided(f"a side of a box in the orthant has 0 <= lo < hi: {s!r}")
            sides.append((lo, hi))
        out.append(tuple(sides))
    return out


def tuple_of(v, n):
    if not isinstance(v, list) or (n is not None and len(v) != n):
        raise Undecided(f"a tuple of {n} coordinates: {v!r}")
    out = tuple(rat(x) for x in v)
    if any(x < 0 for x in out):
        raise Undecided(f"a tuple in the orthant: {v!r}")
    return out


class Table:
    """a function on points given by its values, {"table": [[point, value], ...]} in a fixture: a point of NN^n to a
    rational in QQ>=0 or to a point of NN^r; a point that the table does not list has no value (undecided)"""

    def __init__(self, rows):
        self.rows = rows

    def at(self, x):
        if not isinstance(x, tuple) or x not in self.rows:
            raise Undecided(f"the table has no value at {x!r}")
        return self.rows[x]


def table_of(v, n, out, points=False):
    """the Table of a fixture value {"table": [[point, value], ...]}, points of n coordinates, values rationals
    or (points) tuples of out coordinates (out None: any number)"""
    if not isinstance(v, dict) or not isinstance(v.get("table"), list):
        raise Undecided(f"a function on points is a table {{\"table\": [[point, value], ...]}}: {v!r}")
    rows = {}
    for r in v["table"]:
        if not isinstance(r, list) or len(r) != 2:
            raise Undecided(f"a row of a table is [point, value]: {r!r}")
        pt = tuple_of(r[0], n)
        val = tuple_of(r[1], out) if points else rat(r[1])
        if not isinstance(val, tuple) and val < 0:
            raise Undecided(f"a value in QQ>=0: {r!r}")
        rows[pt] = val
    return Table(rows)


class Line(Table):
    """a function on the counts given by its values: a list from 0, or {"table": [[u, value], ...]}; a count that it
    does not list has no value (undecided)"""

    def at(self, x):
        if not isinstance(x, Fr) or x.denominator != 1 or x < 0 or int(x) not in self.rows:
            raise Undecided(f"the function on the counts has no value at {x!r}")
        return self.rows[int(x)]


def line_of(v):
    """the Line of a fixture value: a list of values in QQ>=0 at 0, 1, ..., or {"table": [[u, value], ...]}"""
    pairs = list(enumerate(v)) if isinstance(v, list) else v.get("table") if isinstance(v, dict) else None
    if not isinstance(pairs, list):
        raise Undecided(f"a function on the counts is a list of values or a table {{\"table\": [[u, value], ...]}}: {v!r}")
    rows = {}
    for r in pairs:
        if not isinstance(r, (list, tuple)) or len(r) != 2 or not isinstance(r[0], int) or r[0] < 0:
            raise Undecided(f"a row of a function on the counts is [u, value]: {r!r}")
        val = rat(r[1])
        if val < 0:
            raise Undecided(f"a value in QQ>=0: {r!r}")
        rows[r[0]] = val
    return Line(rows)


def pair_of(v):
    if v == TOP:
        return TOP
    if isinstance(v, list) and len(v) == 2 and isinstance(v[1], int) and v[1] >= 1 and rat(v[0]) >= 0:
        return (rat(v[0]), v[1])
    raise Undecided(f"a pair is \"top\" or [l, m] with l >= 0, m >= 1: {v!r}")


# ---------------------------------------------------------------------------------------------------------
# the pair and the relations of the model

def padd(p, q):
    if p == TOP or q == TOP:
        return TOP
    return (p[0] + q[0], p[1] + q[1] - 1)


def pkey(p):
    return (1, 0, 0) if p == TOP else (0, p[0], -p[1])


def pmin(p, q):
    return p if pkey(p) <= pkey(q) else q


def solve(rows, rhs):
    """the unique solution of the square system rows * v = rhs over Q, or None"""
    d = len(rows)
    m = [list(r) + [b] for r, b in zip(rows, rhs)]
    for col in range(d):
        piv = next((r for r in range(col, d) if m[r][col] != 0), None)
        if piv is None:
            return None
        m[col], m[piv] = m[piv], m[col]
        for r in range(d):
            if r != col and m[r][col] != 0:
                f = m[r][col] / m[col][col]
                m[r] = [x - f * y for x, y in zip(m[r], m[col])]
    return tuple(m[r][d] / m[r][r] for r in range(d))


def rank(vs):
    m, r = [list(v) for v in vs], 0
    for col in range(len(m[0]) if m else 0):
        piv = next((i for i in range(r, len(m)) if m[i][col] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        for i in range(len(m)):
            if i != r and m[i][col] != 0:
                f = m[i][col] / m[r][col]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
        r += 1
    return r


def vertices(exps):
    """the vertices of D = {v >= 0 : <b, v> >= 1 for b in exps} in Q^d (exps non-zero vectors of naturals): d linearly
    independent constraints tight, by enumeration (the systems are small)"""
    d = len(exps[0])
    EN.enumerating(f"the vertices of a polyhedron, by the bases of {d} of its {len(exps) + d} constraints")
    cons = [(tuple(Fr(x) for x in b), Fr(1)) for b in exps] + \
           [(tuple(Fr(int(i == j)) for j in range(d)), Fr(0)) for i in range(d)]
    out = set()
    for S in combinations(cons, d):
        v = solve([r for r, _ in S], [b for _, b in S])
        if v is not None and all(sum(x * y for x, y in zip(r, v)) >= b for r, b in cons):
            out.add(v)
    return sorted(out)


def local_exps(K, box):
    """the exponents of the monomials of K on the variables that can be 0 on the box (lo_i = 0), with their indices;
    a monomial with none of them is bounded below on the box"""
    z = [i for i, s in enumerate(box) if s[0] == 0]
    return z, [tuple(a[i] for i in z) for _, a in K.monos]


def pair_box(K, box, omega):
    """the pair of K on a box, by the program of fact:readout(1) at the corner where the variables that can be 0 are 0:
    lambda = min <omega, v> over D = {v >= 0 : <a, v> >= 1 for the exponents a of K there}, m - 1 the dimension of
    the face of D where it is attained (Lin 2017, Theorems 4.8 and 4.10, Proposition 4.12); top when a monomial has
    no zero on the box (D empty)"""
    z, exps = local_exps(K, box)
    if not z or any(not any(a) for a in exps):
        return TOP
    w = [omega[i] for i in z]
    vs = vertices(exps)
    vals = [sum(x * y for x, y in zip(w, v)) for v in vs]
    lam = min(vals)
    best = [v for v, x in zip(vs, vals) if x == lam]
    return (lam, 1 + rank([tuple(x - y for x, y in zip(v, best[0])) for v in best[1:]]))


def pair(K, region, omega=None):
    """the pair of the loss K on the region with the weight omega (the measure prod w_i^(omega_i) dw_i / w_i; 1
    without a weight)"""
    omega = omega if omega is not None else (Fr(1),) * K.n
    if any(t.denominator != 1 or t < 1 for t in omega):
        raise Undecided(f"a weight of positive naturals (the model, Lin 2017 Proposition 2.1): {omega}")
    out = TOP
    for box in region:
        if len(box) != K.n or len(omega) != K.n:
            raise Undecided("a loss, a weight and a box on different numbers of variables")
        out = pmin(out, pair_box(K, box, omega))
    return out


_PROG = {}  # prog_value by its exact data: the same program met again is not solved again


def prog_value(rows, cost, d):
    """the pair of the program min <cost, v> over {v >= 0 : rows}, rows [(a, op, b)] read <a, v> op b with op
    >= or =: top if no point is feasible, else (L, dim + 1) with L the least value and dim the dimension of the face
    of the points of cost L. Exact, by the two-phase simplex of qpp.simplex: L is the optimum, and the face is
    the polyhedron cut by <cost, v> = L, whose dimension is d less the rank of its equations and of the inequalities
    that no point of the face makes strict (each tested by a maximum of its slack, unless a point already found makes
    it strict; phase one of the face is done once for all these maxima). Undecided when the cost has no least value
    or a least value below zero (no pair)"""
    key = (tuple(rows), tuple(cost), d)
    if key not in _PROG:
        try:
            _PROG[key] = _prog_value(rows, cost, d)
        except Undecided as e:
            _PROG[key] = e
    out = _PROG[key]
    if isinstance(out, Undecided):
        raise out
    return out


def _prog_value(rows, cost, d):
    unit = [tuple(Fr(int(i == j)) for j in range(d)) for i in range(d)]
    ineq = [(a, b) for a, op, b in rows if op == ">="] + [(u, Fr(0)) for u in unit]
    eq = [(a, b) for a, op, b in rows if op == "="]
    r = SX.lp_min(list(cost), ineq, eq, d)
    if r.status == "infeasible":
        return TOP
    if r.status == "unbounded":
        raise Undecided("prog: the cost has no least value")
    lam = r.value
    if lam < 0:
        raise Undecided("prog: a least value below zero gives no pair")
    face = eq + [(tuple(cost), lam)]
    pts, tight = [r.x], []
    on_face = SX.Polyhedron(ineq, face, d)
    for a, b in ineq:
        if any(SX.dot(a, p) > b for p in pts):
            continue  # strict at a point of the face
        m = on_face.maximize(list(a))
        if m.status == "optimal" and m.value == b:
            tight.append(a)
        elif m.status == "optimal":
            pts.append(m.x)
    return (lam, 1 + d - SX.rank([a for a, _ in face] + tight))

def least_value(K, region):
    """the least value of K on the region (at the lower corners: each block grows in each variable), None if empty"""
    vals = []
    for box in region:
        v = Fr(0)
        for c, a in K.monos:
            m = c
            for j, x in enumerate(a):
                m *= box[j][0] ** x
            v += m
        vals.append(v)
    return min(vals) if vals else None


def below(K1, K2, region):
    """whether K1 <= C * K2 on the region for some positive C, decided on each box at the corner where the variables
    that can be 0 are 0: it holds when K2 has a monomial with no zero on the box (K2 is bounded below); else K2 is 0
    at the corner, and it holds exactly when K1 has no such monomial and each exponent of K1 there lies in the Newton
    polyhedron conv(exponents of K2) + orthant, that is <a, v> >= 1 at every vertex v of D(K2) (blocking duality,
    Schrijver 1986, Section 9.2): weighted AM-GM gives the bound, and a curve w = s^v off the polyhedron refutes it"""
    if K1.n != K2.n:
        raise Undecided("losses on different numbers of variables")
    for box in region:
        _, e1 = local_exps(K1, box)
        _, e2 = local_exps(K2, box)
        if not e2[0] or any(not any(a) for a in e2):
            continue
        if any(not any(a) for a in e1):
            return False
        vs = vertices(e2)
        if any(sum(x * y for x, y in zip(a, v)) < 1 for a in e1 for v in vs):
            return False
    return True


def comparable(K2, K1, region):
    """whether c * K1 <= K2 <= C * K1 on the region for some positive c, C: below both ways"""
    return below(K2, K1, region) and below(K1, K2, region)


# ---------------------------------------------------------------------------------------------------------
# the vocabulary read by the model

class Model:
    """the types, contexts, typed words and relations of the vocabulary lines, as the model reads them"""

    def __init__(self, lines):
        self.types, self.contexts, self.words, self.defines, self.relations = {}, {}, {}, {}, {}
        # the relations read as the graph of the model's pair, while a fixture that names one by "graph" runs
        self.graphs = set()
        for _, raw in lines:
            head = raw.split()[0]
            if head not in ("type", "context", "word", "define", "relation"):
                continue
            try:
                v = vocab_tree(raw)
            except ValueError:
                continue
            if v[0] == "type":
                self.types[v[1]] = (v[2], v[3])
            elif v[0] == "context":
                self.contexts[v[1]] = decls(v[2])
            elif v[0] == "word" and len(v) == 4:
                self.words[v[1]] = (decls(v[2]), v[3])
            elif v[0] == "define" and len(v) == 5:
                self.defines[v[1]] = (v[2], v[3], v[4])
            elif v[0] == "relation":
                pat = v[1][0]
                if pat[0] == "textrel":
                    self.relations[pat[1]] = ([a[1] for a in pat[2]], flat(v[2]))
        T.CLAUSE_APPS.update(self.contexts)

    def graph_relation(self, name):
        """the relation that a fixture names by \"graph\": the one whose first word is name, refused unless its
        parameters are, in their order, a loss, a rational, a natural number, a tuple of natural numbers and a region
        (the coefficient of def:coef, (K #coefficient lambda #multiplicity m #weight q #over B)), so that no other
        relation is read as the graph of the pair by accident"""
        keys = [k for k in self.relations if k[0] == name]
        if len(keys) != 1:
            raise ValueError(f"\"graph\": {name!r}: {len(keys)} relations whose first word is {name}, not one")
        params, clauses = self.relations[keys[0]]
        types = {v[1]: c[2] for c in clauses if c[0] == "decl" for v in c[1]}
        got = [self.param_kind(types.get(p)) for p in params]
        if got != ["loss", "rat", "nat", "nat tuple", "region"]:
            raise ValueError(f"\"graph\": {name!r}: the parameters of the relation are {', '.join(got)}, not a loss, "
                             f"a rational, a natural number, a tuple of natural numbers and a region")
        return keys[0]

    def param_kind(self, ty):
        """the kind of a parameter of a relation, as graph_relation reads it"""
        if ty is None:
            return "undeclared"
        while ty[0] == "paren":
            ty = ty[1]
        if ty[0] == "set":
            return "nat" if ty[1].startswith("NN") else "rat" if ty[1].startswith("QQ") else ty[1]
        if self.nat_tuple(ty):
            return "nat tuple"
        try:
            return self.kind(ty, {})[0]
        except Undecided:
            return T.to_qpp(ty)

    def nat_tuple(self, ty):
        """whether a type is a tuple of natural numbers, NN^n or a type row of it"""
        while ty[0] == "paren":
            ty = ty[1]
        if ty[0] == "pow":
            base = ty[1]
            while base[0] == "paren":
                base = base[1]
            return base[0] == "set" and base[1].startswith("NN")
        name = ty[1] if ty[0] == "var" else ty[1][1] if ty[0] == "app" and ty[1][0] == "var" else None
        if name in self.types and self.types[name][1] != "pair" and self.types[name][1][0] != "bundle":
            return self.nat_tuple(self.types[name][1])
        return False

    @contextmanager
    def reading(self, fixture):
        """the relation that the fixture (its JSON) names by \"graph\" read as the graph of the model's pair while
        it runs"""
        old, oldb = self.graphs, getattr(self, "bounds", {})
        name = fixture.get("graph")
        self.graphs = {self.graph_relation(name)} if name else set()
        # the bounds of the fixture ("bounds": {"J": 8}): a quantifier over NN that no clause bounds is checked up to
        # its bound, as the checker of the statements reads it
        self.bounds = {k: v for k, v in fixture.get("bounds", {}).items() if isinstance(v, int)}
        try:
            yield
        finally:
            self.graphs, self.bounds = old, oldb

    def kind(self, ty, env=None):
        """(kind, dimension) of a Q++ type: nat, rat, loss, region, tuple, pair, point"""
        if ty[0] == "paren":
            return self.kind(ty[1], env)
        if ty[0] == "set":
            return ("nat", None) if ty[1].startswith("NN") else ("rat", None)
        if ty[0] == "setlist" and all(m[0] == "num" for m in ty[1]):
            # a finite set of numerals, {0, 1}: a rational in the set
            return ("rat", None)
        if ty == "pair":
            return ("pair", None)
        if ty[0] == "pow":
            base = ty[1]
            while base[0] == "paren":
                base = base[1]
            if base[0] == "pow":
                # a tuple of tuples (X^n)^k: k rows of n coordinates
                return ("tuples", (self.num(ty[2], env), self.num(base[2], env)))
            return ("tuple", self.num(ty[2], env))
        if ty[0] == "fun":
            k = self.kind(ty[1], env)
            if k[0] == "nat" and ty[2] in (("set", "QQ>=0"), ("set", "QQ>0")):
                return ("line", None)  # a function on the counts, NN -> QQ>=0
            if k[0] == "tuple" and ty[2] in (("set", "QQ>=0"), ("set", "QQ>0")):
                return ("loss", k[1])
            if k[0] == "tuple" and self.kind(ty[2], env)[0] == "tuple":
                return ("table", (k[1], self.kind(ty[2], env)[1]))
            raise Undecided(f"the function type {T.to_qpp(ty)}")
        if ty[0] == "app" and ty[1] == ("var", "set") and len(ty[2]) == 1:
            k = self.kind(ty[2][0], env)
            if k[0] == "tuple":
                return ("region", k[1])
            raise Undecided(f"the set type {T.to_qpp(ty)}")
        name, args = (ty[1], ()) if ty[0] == "var" else (ty[1][1], ty[2]) if ty[0] == "app" else (None, ())
        if name in self.types:
            params, val = self.types[name]
            if val == "pair":
                return ("pair", None)
            inner = dict(env or {})
            for p, a in zip(params, args):
                inner[p] = self.num(a, env)
            if val[0] == "bundle":
                # a bundle: a JSON object, one value per part
                return ("bundle", {n: self.kind(t, inner) if t != ("set", "NN") else ("nat", None)
                                   for ns, t in val[1] for n in ns})
            return self.kind(val, inner)
        raise Undecided(f"the type {T.to_qpp(ty)}")

    def nat_dim(self, ty, env):
        """the number of coordinates of a type NN^n (a type row of it, applied), or None for any other type"""
        while ty[0] == "paren":
            ty = ty[1]
        if ty[0] == "pow":
            return self.num(ty[2], env) if ty[1] == ("set", "NN") else None
        name, args = (ty[1], ()) if ty[0] == "var" else (ty[1][1], ty[2]) if ty[0] == "app" else (None, ())
        if name in self.types and self.types[name][1] != "pair" and self.types[name][1][0] != "bundle":
            params, val = self.types[name]
            inner = dict(env or {})
            for p, a in zip(params, args):
                d = self.num(a, env)
                inner[p] = None if d is None else Fr(d)
            return self.nat_dim(val, inner)
        return None

    def tuple_dim(self, ty, env):
        """the number of coordinates of a tuple type X^n (NN^n, Point(n), a type row of it, applied), or None for any
        other type"""
        while ty[0] == "paren":
            ty = ty[1]
        if ty[0] == "pow":
            return self.num(ty[2], env) if ty[1][0] == "set" else None
        name, args = (ty[1], ()) if ty[0] == "var" else (ty[1][1], ty[2]) if ty[0] == "app" else (None, ())
        if name in self.types and self.types[name][1] != "pair" and self.types[name][1][0] != "bundle":
            params, val = self.types[name]
            inner = dict(env or {})
            for p, a in zip(params, args):
                d = self.num(a, env)
                inner[p] = None if d is None else Fr(d)
            return self.tuple_dim(val, inner)
        return None

    def tuple_member(self, ty, env, v):
        """whether the value v lies in the tuple type ty (NN^n, Point(n), a type row of it, applied): its length the
        dimension of the type, and each coordinate in the base set (NN, QQ>=0, QQ>0); None when the type is not
        such a tuple type"""
        while ty[0] == "paren":
            ty = ty[1]
        if ty[0] == "pow":
            base = ty[1]
            while base[0] == "paren":
                base = base[1]
            if base[0] != "set":
                return None
            d = self.num(ty[2], env)
            if d is None or not isinstance(v, tuple) or len(v) != d:
                return False
            xs = [Fr(x) for x in v]
            if base[1].startswith("NN"):
                return all(x.denominator == 1 and x >= 0 for x in xs)
            if base[1] == "QQ>0":
                return all(x > 0 for x in xs)
            if base[1] == "QQ>=0":
                return all(x >= 0 for x in xs)
            return True
        name, args = (ty[1], ()) if ty[0] == "var" else (ty[1][1], ty[2]) if ty[0] == "app" else (None, ())
        if name in self.types and self.types[name][1] != "pair" and self.types[name][1][0] != "bundle":
            params, val = self.types[name]
            inner = dict(env or {})
            for p, a in zip(params, args):
                d = self.num(a, env)
                inner[p] = None if d is None else Fr(d)
            return self.tuple_member(val, inner, v)
        return None

    def bind_dims(self, ty, v, env):
        """the parameters of a type that the shape of a value gives, bound in env when they are names not bound
        yet: n of Exponent(n) from the length of a point, k and n of Prog(k, n) from the rows of its parts (the
        implicit parameters of a relation row)"""
        while ty[0] == "paren":
            ty = ty[1]
        if ty[0] == "pow":
            if ty[2][0] == "var" and ty[2][1] not in env and isinstance(v, tuple):
                env[ty[2][1]] = Fr(len(v))
            if isinstance(v, tuple) and v:
                self.bind_dims(ty[1], v[0], env)
            return
        name, args = (ty[1], ()) if ty[0] == "var" else (ty[1][1], ty[2]) if ty[0] == "app" else (None, ())
        if name not in self.types or self.types[name][1] == "pair":
            return
        params, val = self.types[name]
        inner = {}
        if val[0] == "bundle":
            if isinstance(v, dict):
                for ns, t in val[1]:
                    for n_ in ns:
                        if n_ in v:
                            self.bind_dims(t, v[n_], inner)
        else:
            self.bind_dims(val, v, inner)
        for p_, a in zip(params, args):
            if a[0] == "var" and a[1] not in env and p_ in inner:
                env[a[1]] = inner[p_]

    def num(self, x, env):
        try:
            v = Ev(self, env or {}).val(x)
        except Undecided:
            return None
        return int(v) if isinstance(v, Fr) and v.denominator == 1 else None


def flat(c):
    """the clauses of a statement part"""
    if isinstance(c, list):
        return [y for x in c for y in flat(x)]
    if c[0] == "and":
        return [y for x in c[1] for y in flat(x)]
    if c[0] == "paren":
        return flat(c[1])
    return [c]


def decls(item):
    """[(name, type)] of the declarations of a signature"""
    out = []
    for c in flat(item):
        if c[0] == "decl":
            for v in c[1]:
                out.append((v[1], c[2]))
    return out


# ---------------------------------------------------------------------------------------------------------
# evaluation

_SITES = {}  # coord_sites by (id(body), i), with body kept so that its id stays its own


def coord_sites(body, i, boxes):
    """the places of body that decide the number of coordinates of the tuples that the index i indexes, in the order
    of a walk of body: ("dims", y, bx) a quantifier y over points, ("tuple", y, bx) a coordinate v_(i) of a name v,
    ("family", y, bx) a coordinate a_(j)_(i) of a member of a family, with bx the boxes [0, b] of the sums around y.
    They depend on the term alone, so they are found once per term (Ev.coord_length reads them at its values)"""
    key = (id(body), i)
    hit = _SITES.get(key) if not boxes else None
    if hit is not None and hit[0] is body:
        return hit[1]
    sites = []

    def walk(y, bx):
        if not isinstance(y, tuple) or not y:
            return
        if y[0] == "sum" and len(y) == 4 and y[2] is not None and y[2][0] == "le":
            bx = {**bx, y[1]: y[2][1]}
        if y[0] in ("forall", "exists") and len(y) == 4 and y[2] is not None \
                and all(v[0] == "var" for v in y[1]):
            sites.append(("dims", y, bx))
        if y[0] == "app" and len(y) == 4 and y[3] == "idx" and y[2] == (("var", i),) and y[1][0] == "var":
            sites.append(("tuple", y, bx))
        elif y[0] == "app" and len(y) == 4 and y[3] == "idx" and y[2] == (("var", i),) and y[1][0] == "app" \
                and y[1][3] == "idx" and y[1][1][0] == "var":
            sites.append(("family", y, bx))
        for z in y:
            walk(z, bx)
    walk(body, boxes)
    if not boxes:
        _SITES[key] = (body, sites)
    return sites


_PLANS = {}  # pair_plan by id(c), with c kept so that its id stays its own


def pair_plan(c):
    """how Ev.points_tied reads a universal c over several points of NN^n, or None: (names, the parts of the guard on
    one point [(k, part)] (a part on no point is read on the first), the ties [(k, k2, part, i, C)] of coord_tie, the
    conclusion, and point_reads of the conclusion). Found once per clause"""
    hit = _PLANS.get(id(c))
    if hit is not None and hit[0] is c:
        return hit[1]
    plan = _pair_plan(c)
    _PLANS[id(c)] = (c, plan)
    return plan


def _pair_plan(c):
    names = [v[1] for v in c[1]]
    body = c[3]
    while body[0] == "paren":
        body = body[1]
    if c[0] != "forall" or body[0] != "imp" or len(names) < 2 or len(set(names)) < len(names):
        return None
    parts = []

    def conj(g):
        # the parts of the guard, in the order that holds reads them
        while g[0] == "paren":
            g = g[1]
        if g[0] == "and":
            for y in g[1]:
                conj(y)
        else:
            parts.append(g)
    conj(body[1])
    ones, ties = [], []
    for g in parts:
        on = [k for k, name in enumerate(names) if ("var", name) in walk(g)]
        if len(on) <= 1:
            ones.append((on[0] if on else 0, g))
            continue
        tie = coord_tie(g, names)
        if tie is None:
            return None
        ties.append(tie)
    return names, ones, ties, body[2], point_reads(body[2], names)


def coord_tie(g, names):
    """(k, k2, g, i, C) of a part g = `forall i : C(i) => u_(i) = w_(i)` of a guard (or `forall i : u_(i) = w_(i)`, C
    None), with C free of the points: it ties the points u and w (places k < k2 in names) at the coordinates where C
    holds; None for any other part"""
    if not (g[0] == "forall" and len(g) == 4 and g[2] is None and len(g[1]) == 1 and g[1][0][0] == "var"):
        return None
    i = g[1][0][1]
    b = g[3]
    while b[0] == "paren":
        b = b[1]
    C, e = (b[1], b[2]) if b[0] == "imp" else (None, b)
    while e[0] == "paren":
        e = e[1]
    if i in names or e[0] != "rel" or e[1] != ("=",) or len(e[2]) != 2:
        return None
    ks = []
    for x in e[2]:
        if not (x[0] == "app" and len(x) == 4 and x[3] == "idx" and x[2] == (("var", i),) and x[1][0] == "var"
                and x[1][1] in names):
            return None
        ks.append(names.index(x[1][1]))
    if ks[0] == ks[1] or (C is not None and any(("var", name) in walk(C) for name in names)):
        return None
    return min(ks), max(ks), g, i, C


_PLAIN = ("paren", "num", "var", "tuple", "bin", "app", "iverson", "pow", "rel", "and", "imp", "iff", "textrel", "or",
          "not", "set", "range", "le")  # the constructs that bind no name


def point_reads(t, names):
    """[(k, term)]: the terms through which t reads the points names (k the place of the point), each F(u) with F a
    name or u_(j) with j a name, F and j not points and not bound inside t; None when t reads a point in another way,
    or holds a construct that binds names other than a quantifier, a sum, a product or a union over an index. The
    value of t at a tuple of points is then a function of the values of these terms there"""
    out = []

    def go(x, bound):
        if not isinstance(x, tuple):
            return True
        if not x or not isinstance(x[0], str):
            return all(go(y, bound) for y in x)
        if all(isinstance(y, str) for y in x):
            return not (x[0] == "var" and len(x) == 2 and x[1] in names and x[1] not in bound)
        tag = x[0]
        if tag == "app" and len(x) == 4 and x[1][0] == "var" and len(x[1]) == 2 and len(x[2]) == 1 \
                and x[2][0][0] == "var" and len(x[2][0]) == 2:
            f, a = x[1][1], x[2][0][1]
            if x[3] == "call" and a in names and a not in bound and f not in names and f not in bound:
                out.append((names.index(a), x))
                return True
            if x[3] == "idx" and f in names and f not in bound and a not in names and a not in bound:
                out.append((names.index(f), x))
                return True
        if tag in ("forall", "exists") and len(x) == 4:
            if not all(isinstance(v, tuple) and len(v) == 2 and v[0] == "var" for v in x[1]):
                return False
            return go(x[2], bound) and go(x[3], bound | {v[1] for v in x[1]})
        if tag in ("sum", "prod", "union", "inter", "oplus", "min") and len(x) == 4 and isinstance(x[1], str):
            return go(x[2], bound) and go(x[3], bound | {x[1]})
        if tag not in _PLAIN:
            return False
        return all(go(y, bound) for y in x[1:])

    return out if go(t, frozenset()) else None


def value_key(v):
    """a value with its type, as a key: two values with the same key are the same value (TypeError for a value that
    is no key, a list or a dict)"""
    if isinstance(v, tuple):
        return (tuple,) + tuple(value_key(y) for y in v)
    hash(v)
    return type(v), v


class Ev:
    def __init__(self, model, env):
        self.m, self.env = model, env

    def val(self, x):
        k = x[0]
        if k == "paren":
            return self.val(x[1])
        if k == "num":
            return rat(x[1])
        if k == "var":
            if x[1] == "top":
                return TOP
            if x[1] == "emptyset":
                return []
            if x[1] not in self.env or self.env[x[1]] is None:
                raise Undecided(f"no value for {x[1]}")
            return self.env[x[1]]
        if k == "tuple" and len(x[1]) == 2:
            l, m = self.val(x[1][0]), self.val(x[1][1])
            if not isinstance(l, Fr) or not isinstance(m, Fr) or m.denominator != 1 or m < 1 or l < 0:
                raise Undecided(f"the literal pair {T.to_qpp(x)}")
            return (l, int(m))
        if k == "bin":
            a, b = self.val(x[2]), self.val(x[3])
            op = x[1]
            # an index in a term is the count it is, from 1
            a, b = (Fr(y.k + 1) if isinstance(y, Coord) else y for y in (a, b))
            if op == "+" and (a == TOP or b == TOP or isinstance(a, tuple) and isinstance(b, tuple)):
                return padd(a, b)
            if isinstance(a, Fr) and isinstance(b, Fr) and op in ("+", "*", "/"):
                return a + b if op == "+" else a * b if op == "*" else a / b
            if isinstance(a, Fr) and isinstance(b, Fr) and op == "-":
                return a - b  # the deficit max(a - b, 0): a form of both signs is refused by the check, not here
            if op == "cup":
                return list(a) + list(b)
            if op == "times":
                return [ba + bb for ba in a for bb in b]
            if op == "cap":
                return self.cap(a, b)
            raise Undecided(f"the term {T.to_qpp(x)}")
        if k == "app" and x[3] == "idx" and isinstance(self.env.get(x[2][0][1]) if x[2][0][0] == "var" else None,
                                                      Coord):
            # a coordinate of a tuple, x_(i) with i bound over the coordinates
            tup, i = self.val(x[1]), self.env[x[2][0][1]]
            if not isinstance(tup, tuple) or len(tup) != i.n:
                raise Undecided(f"{T.to_qpp(x)}: {x[2][0][1]} runs over the coordinates of tuples of two lengths")
            return tup[i.k]
        if k == "iverson":
            return Fr(1) if self.holds(x[1]) else Fr(0)
        if k == "pow":
            a, e = self.val(x[1]), self.val(x[2])
            if not isinstance(a, Fr) or not isinstance(e, Fr) or e.denominator != 1 or e < 0:
                raise Undecided(f"the power {T.to_qpp(x)}")
            return a ** int(e)
        if k == "sum" and len(x) == 4 and x[2] is not None and x[2][0] == "le":
            split = self.fubini(x)
            if split is None:
                split = self.coordinate_sum(x)
            if split is not None:
                return split
        if k in ("sum", "prod") and len(x) == 4:
            vals = [Ev(self.m, {**self.env, x[1]: v}).val(x[3]) for v in self.index_values(x)]
            if any(not isinstance(v, Fr) for v in vals):
                raise Undecided(f"the terms of {T.to_qpp(x)}")
            out = Fr(0) if k == "sum" else Fr(1)
            for v in vals:
                out = out + v if k == "sum" else out * v
            return out
        if k == "app" and x[3] == "idx":
            fam = self.val(x[1])
            i = self.val(x[2][0])
            if not isinstance(fam, dict) or i not in fam or fam[i] is None:
                raise Undecided(f"no value for {T.to_qpp(x)}")
            return fam[i]
        if k == "app" and x[3] == "call" and x[1][0] == "var":
            f = x[1][1]
            args = [self.val(a) for a in x[2]]
            if f in ("min", "max") and all(isinstance(a, Fr) for a in args):
                return min(args) if f == "min" else max(args)
            if f == "binom" and len(args) == 2 and all(isinstance(a, Fr) and a.denominator == 1 and a >= 0
                                                       for a in args):
                return Fr(comb(int(args[0]), int(args[1])))  # 0 when k > n, as Nat.choose
            if f in ("bidetP", "bidetM") and len(args) in (1, 2) and all(is_table(a) for a in args):
                if len(args) == 1:
                    args.append(tuple(tuple(Fr(0) for _ in r) for r in args[0]))
                if len(args[1]) != len(args[0]):
                    raise Undecided(f"{T.to_qpp(x)}: two tables of two sizes")
                return bidet(args[0], args[1])[0 if f == "bidetP" else 1]
            if f in ("min", "max") and all(a == TOP or isinstance(a, tuple) and len(a) == 2 for a in args):
                out = args[0]
                for a in args[1:]:
                    out = pmin(out, a) if f == "min" else a if pmin(out, a) == out else out
                return out
            if f == "join":
                return tuple(y for a in args for y in a)
            if f in self.m.defines:
                return self.apply(f, x[2], args)
            if isinstance(self.env.get(f), Table) and len(args) == 1:
                return self.env[f].at(args[0])
            raise Undecided(f"the term {T.to_qpp(x)}")
        if k == "app" and x[3] == "call" and x[1][0] == "app" and len(x[2]) == 1:
            # a member of a family of functions read at a point, YP_(j)(u)
            f = self.val(x[1])
            if isinstance(f, Table):
                return f.at(self.val(x[2][0]))
            raise Undecided(f"the term {T.to_qpp(x)}")
        if k == "prog":
            return self.prog(x)
        if k in ("union", "inter", "oplus", "min") and len(x) == 4 and x[2] and x[2][0] == "range":
            lo, hi = (self.val(e) for e in x[2][1])
            vals = [Ev(self.m, {**self.env, x[1]: Fr(j)}).val(x[3]) for j in range(int(lo), int(hi) + 1)
                    if lo <= j <= hi]
            if k == "union":
                return [b for v in vals for b in v]
            if k == "inter":
                if not vals:
                    raise Undecided("an intersection over an empty range")
                out = vals[0]
                for v in vals[1:]:
                    out = self.cap(out, v)
                return out
            out = TOP
            for v in vals:
                out = pmin(out, v)
            return out
        raise Undecided(f"the term {T.to_qpp(x)}")

    def fubini(self, x):
        """a sum over a box of a sum over another box, `sum w <= b2, (sum u <= b1, F)`, whose summand F is a product of
        factors that each read one of the two points or neither, the inner box free of w: the double sum is the
        product of the sum of the factors of w over its box, the sum of the factors of u over its box and the factors
        that read neither (Fubini), and a sum of 1 over a box [0, b] is prod_i (b_i + 1). None when x is not such a
        sum"""
        def strip(t):
            while t[0] == "paren":
                t = t[1]
            return t

        inner = strip(x[3])
        if not (inner[0] == "sum" and len(inner) == 4 and isinstance(inner[1], str) and inner[2] is not None
                and inner[2][0] == "le" and inner[1] != x[1]):
            return None
        w, u = ("var", x[1]), ("var", inner[1])
        if w in walk(inner[2]):
            return None
        factors, stack = [], [inner[3]]
        while stack:
            t = strip(stack.pop())
            if t[0] == "bin" and t[1] == "*":
                stack += [t[3], t[2]]
            else:
                factors.append(t)
        sides = {"w": [], "u": [], "none": []}
        for f in factors:
            on = [w in walk(f), u in walk(f)]
            if all(on):
                return None
            sides["w" if on[0] else "u" if on[1] else "none"].append(f)

        def product_of(fs):
            out = None
            for f in fs:
                out = f if out is None else ("bin", "*", out, f)
            return out

        def over_box(name, dom, fs):
            if not fs:
                b = self.val(dom[1])
                if not isinstance(b, tuple) or any(c.denominator != 1 or c < 0 for c in b):
                    raise Undecided(f"a box [0, b] with b a tuple of natural numbers: {T.to_qpp(dom[1])}")
                out = Fr(1)
                for c in b:
                    out *= c + 1
                return out
            return self.val(("sum", name, dom, product_of(fs)))

        out = over_box(x[1], x[2], sides["w"]) * over_box(inner[1], inner[2], sides["u"])
        for f in sides["none"]:
            v = self.val(f)
            if not isinstance(v, Fr):
                raise Undecided(f"the terms of {T.to_qpp(x)}")
            out *= v
        return out

    def coordinate_sum(self, x):
        """a sum over a box, or sums over boxes nested one in the other, of a product over the coordinates,
        `sum v <= b, (sum w <= c, C * prod i, h)`, where h reads each point only by its coordinate i (v_(i), w_(i))
        and C reads none of them, the boxes free of the points: it is C * prod_i of the sum of h over the coordinate
        ranges 0..b_i, 0..c_i (Fubini). The innermost range is summed by range_sum, a geometric series in closed form
        where its terms are one. None when x is not such a sum"""
        def strip(t):
            while t[0] == "paren":
                t = t[1]
            return t

        points, body = [], x
        while True:
            body = strip(body)
            if not (body[0] == "sum" and len(body) == 4 and isinstance(body[1], str) and body[2] is not None
                    and body[2][0] == "le"):
                break
            if any(("var", q) in walk(body[2]) for q, _ in points) or body[1] in [q for q, _ in points]:
                return None
            points.append((body[1], body[2]))
            body = body[3]
        names = [("var", q) for q, _ in points]
        factors, stack = [], [body]
        while stack:
            t = strip(stack.pop())
            if t[0] == "bin" and t[1] == "*":
                stack += [t[3], t[2]]
            else:
                factors.append(t)
        reading = [f for f in factors if any(v in walk(f) for v in names)]
        if len(reading) != 1:
            return None
        prod = reading[0]
        if not (prod[0] == "prod" and len(prod) == 4 and isinstance(prod[1], str) and prod[2] is None):
            return None
        i = ("var", prod[1])
        ts = ["__t%d_%s" % (k, q) for k, (q, _) in enumerate(points)]
        at = {("app", v, (i,), "idx"): ("var", t) for v, t in zip(names, ts)}

        def sub(y):
            if y in at:
                return at[y]
            return tuple(sub(z) for z in y) if isinstance(y, tuple) else y

        h = sub(prod[3])
        if any(v in walk(h) for v in names) or any(("var", t) in walk(prod[3]) for t in ts):
            return None
        boxes = []
        for _, dom in points:
            b = self.val(dom[1])
            if not isinstance(b, tuple) or any(c.denominator != 1 or c < 0 for c in b):
                raise Undecided(f"{T.to_qpp(x)}: a box [0, b] with b a tuple of natural numbers")
            boxes.append(b)
        n = len(boxes[0])
        if any(len(b) != n for b in boxes):
            return None
        out = Fr(1)
        for k in range(n):
            env = {**self.env, prod[1]: Coord(k, n)}
            total = Fr(0)
            for outer in product(*(range(int(b[k]) + 1) for b in boxes[:-1])):
                inner = {**env, **{t: Fr(j) for t, j in zip(ts, outer)}}
                total += Ev(self.m, inner).range_sum(ts[-1], 0, int(boxes[-1][k]), h)
            out *= total
        for f in factors:
            if f is not prod:
                y = self.val(f)
                if not isinstance(y, Fr):
                    raise Undecided(f"the terms of {T.to_qpp(x)}")
                out *= y
        return out

    def range_sum(self, name, lo, hi, h):
        """sum name in lo..hi, h. A geometric term in closed form: h a product of indicators iverson(R) of relations
        affine in the number, of powers base^e with the base free of it and e affine in it (in a numerator or a
        denominator), and of factors free of it, is C * r^(t - p) on the interval p..q of the numbers of lo..hi that
        the relations leave (their slopes read from their values at 0 and 1), C and r read from its values at p and
        p + 1, and the sum is C * (1 - r^(q - p + 1)) / (1 - r) (C * (q - p + 1) at r = 1). Any other h is summed term
        by term"""
        if lo > hi:
            return Fr(0)
        me = ("var", name)
        items, stack = [], [(h, True)]  # (factor, whether it is in the numerator)
        while stack:
            t, up = stack.pop()
            while t[0] == "paren":
                t = t[1]
            if t[0] == "bin" and t[1] == "*":
                stack += [(t[3], up), (t[2], up)]
            elif t[0] == "bin" and t[1] == "/":
                stack += [(t[2], up), (t[3], not up)]
            else:
                items.append((t, up))
        conds, closed = [], True
        for t, up in items:
            if me not in walk(t):
                continue
            if t[0] == "iverson" and up:
                stack = [t[1]]
                while stack:
                    g = stack.pop()
                    while g[0] == "paren":
                        g = g[1]
                    if g[0] == "and":
                        stack += list(g[1])
                    elif g[0] == "rel" and all(op in ("<=", "<", ">=", ">", "=") for op in g[1]) \
                            and all(scalar_degree(y, me) in (0, 1) for y in g[2]):
                        conds.append(g)
                    else:
                        closed = False
            elif t[0] == "pow" and me not in walk(t[1]) and scalar_degree(t[2], me) == 1:
                # a geometric factor: a base that is not 0 and an exponent that does not fall (0^(5 - t) is no
                # geometric term, and a falling exponent leaves NN)
                e0 = Ev(self.m, {**self.env, name: Fr(0)}).val(t[2])
                e1 = Ev(self.m, {**self.env, name: Fr(1)}).val(t[2])
                base = self.val(t[1])
                if not (isinstance(e0, Fr) and isinstance(e1, Fr) and isinstance(base, Fr)) or base == 0 or e1 < e0:
                    closed = False
            else:
                closed = False
        if not closed:
            total = Fr(0)
            for j in range(lo, hi + 1):
                y = Ev(self.m, {**self.env, name: Fr(j)}).val(h)
                if not isinstance(y, Fr):
                    raise Undecided(f"the terms of sum {name} in {lo}..{hi}, {T.to_qpp(h)}")
                total += y
            return total
        p, q = Fr(lo), Fr(hi)
        at0, at1 = Ev(self.m, {**self.env, name: Fr(0)}), Ev(self.m, {**self.env, name: Fr(1)})
        for g in conds:
            for op, a, b in zip(g[1], g[2], g[2][1:]):
                rows = ([(b, a, op == "<")] if op in ("<=", "<", "=") else []) + \
                       ([(a, b, op == ">")] if op in (">=", ">", "=") else [])
                for big, small, strict in rows:
                    d = ("bin", "-", big, small)
                    v0, v1 = at0.val(d), at1.val(d)
                    if not (isinstance(v0, Fr) and isinstance(v1, Fr)):
                        raise Undecided(f"the relation {T.to_qpp(g)}")
                    slope = v1 - v0
                    if slope == 0:
                        if v0 < 0 or (strict and v0 == 0):
                            return Fr(0)
                        continue
                    bound = -v0 / slope
                    if slope > 0:
                        p = max(p, Fr(bound // 1 + 1 if strict else -((-bound) // 1)))
                    else:
                        q = min(q, Fr(-((-bound) // 1) - 1 if strict else bound // 1))
        if p > q:
            return Fr(0)
        rest = [(t, up) for t, up in items if not (t[0] == "iverson" and up and me in walk(t))]

        def value(ev):
            out = Fr(1)
            for t, up in rest:
                y = ev.val(t)
                if not isinstance(y, Fr) or (not up and y == 0):
                    raise Undecided(f"the factor {T.to_qpp(t)}")
                out = out * y if up else out / y
            return out

        # C r^(t - p) on p..q, read at the first two numbers of the interval (where the terms are defined)
        c0 = value(Ev(self.m, {**self.env, name: p}))
        if c0 == 0 or p == q:
            return c0
        r = value(Ev(self.m, {**self.env, name: p + 1})) / c0
        if r == 1:
            return c0 * (q - p + 1)
        return c0 * (1 - r ** int(q - p + 1)) / (1 - r)

    def index_values(self, x):
        """the values an index of a sum, a product or a quantifier runs over: a range lo..hi; the coordinates of the
        tuples it indexes (no range); the lattice points u <= b of the box [0, b], b a tuple of natural numbers"""
        d = x[2]
        if d is not None and d[0] == "range":
            lo, hi = (self.val(e) for e in d[1])
            if not all(isinstance(e, Fr) and e.denominator == 1 for e in (lo, hi)):
                raise Undecided(f"the range of {T.to_qpp(x)}")
            return [Fr(j) for j in range(int(lo), int(hi) + 1)]
        if d is not None and d[0] == "le" and x[0] == "sum":
            b = self.val(d[1])
            if not isinstance(b, tuple) or any(c.denominator != 1 or c < 0 for c in b):
                raise Undecided(f"{T.to_qpp(x)}: a box [0, b] with b a tuple of natural numbers")
            if not self.reads_data(x[3], [x[1]]):
                EN.enumerating(f"the lattice points of a box: {T.to_qpp(x)}")
            return [tuple(Fr(c) for c in u) for u in product(*(range(int(c) + 1) for c in b))]
        if d is None:
            n = self.coord_length(x[3], x[1], {})
            return [Coord(k, n) for k in range(n)]
        if d[0] == "cell":
            return self.cell_values(x)
        raise Undecided(f"the range of {T.to_qpp(x)}")

    def cell_values(self, x):
        """the points of a cell, `sum m in a..b : C_1, ..., C_J, t` or `sum i : C_1, ..., C_J, t`: the points of its
        holder (an index range, or the coordinates of the tuples the index reads) at which every clause holds, each
        read term by term. A cell over lattice points (a tuple type named in the binder, or a point read by its
        coordinates, u_(i)) visits the points of a box: an enumeration"""
        v, holder, clauses, body = x[1], x[2][1], tuple(x[2][2]), x[3]

        def reads_point(t):
            if isinstance(t, tuple) and t:
                if t[0] == "app" and len(t) > 3 and t[3] == "idx" and t[1] == ("var", v):
                    return True
                return any(reads_point(y) for y in (t[1:] if isinstance(t[0], str) else t) if isinstance(y, tuple))
            return False

        if (holder is not None and holder[0] != "range") or (holder is None and any(map(reads_point,
                                                                                         clauses + (body,)))):
            EN.enumerating(f"the lattice points of a box: {T.to_qpp(x)}")
            raise Undecided(f"a cell over lattice points: {T.to_qpp(x)}")
        if holder is None:
            n = self.coord_length(("tuple", clauses + (body,)), v, {})
            pts = [Coord(k, n) for k in range(n)]
        else:
            pts = self.index_values(("sum", v, holder, body))
        return [p for p in pts if all(Ev(self.m, {**self.env, v: p}).holds(c) for c in clauses)]

    def coord_length(self, body, i, boxes):
        """the number of coordinates of the tuples that the index i indexes in body (one length). The places of body
        that decide it (coord_sites) are found once per term; here they are read at the values of this evaluation, in
        the order of a walk of body"""
        found = set()
        dims = {}  # the points bound inside body by a quantifier over a tuple type (NN^n, Point(n)): their dimension n
        for kind, y, bx in coord_sites(body, i, boxes):
            if kind == "dims":
                n_ = self.m.tuple_dim(y[2], self.env)
                if n_ is not None:
                    dims.update({v[1]: n_ for v in y[1]})
            elif kind == "tuple":
                name = y[1][1]
                v = self.env.get(name)
                if v is None and name in bx:
                    v = self.val(bx[name])
                if v is None and name in dims:
                    found.add(dims[name])
                    continue
                if not isinstance(v, tuple):
                    raise Undecided(f"{T.to_qpp(y)}: no tuple {name}")
                found.add(len(v))
            else:
                # a_(j)_(i), f_(iota)_(i): a member of a family of tuples, a row of a tuple of tuples
                try:
                    rows = [self.val(y[1])]
                except Undecided:
                    whole = self.env.get(y[1][1][1])
                    rows = list(whole.values()) if isinstance(whole, dict) else list(whole or ())
                rows = [r for r in rows if r is not None]
                if not rows or not all(isinstance(r, tuple) for r in rows):
                    raise Undecided(f"{T.to_qpp(y)}: no tuple {T.to_qpp(y[1])}")
                found.update(len(r) for r in rows)
        if len(found) != 1:
            raise Undecided(f"{i} indexes {'no tuple' if not found else 'tuples of two lengths'}")
        return found.pop()

    def prog(self, x):
        """the pair of a program prog(DECLS, ROWS : COST) at the values of its parameters (prog_value)"""
        scales, out, cost, c0 = self.prog_lp(x)
        p = prog_value(out, tuple(cost), len(scales))
        return p if p == TOP else (p[0] + c0, p[1]) if p[0] + c0 >= 0 else self._nopair()

    def prog_lp(self, x):
        """the data of a program prog(DECLS, ROWS : COST) at the values of its parameters: (its scales, its rows
        [(a, op, b)] read <a, v> op b with op >= or =, its cost, the constant of the cost)"""
        from . import progcert as PC
        if any(c[0] == "decl" and any(v[0] == "family" for v in c[1]) for c in flat(x[1][1])):
            x = self.prog_expand(x)
        ctx = x[1]
        scales, rows = [], []
        for c in flat(ctx[1]):
            if c[0] == "decl" and c[2] == ("set", "QQ>=0") and all(v[0] == "var" for v in c[1]):
                scales += [v[1] for v in c[1]]
            elif c[0] == "rel" and len(c[1]) == 1 and c[1][0] in (">=", "<=", "="):
                rows.append(c)
            else:
                raise Undecided(f"prog: the clause {T.to_qpp(c)}")
        vals = {}

        def names(t):
            if isinstance(t, tuple) and len(t) == 2 and t[0] == "var":
                return {t[1]}
            return set().union(*[names(y) for y in t]) if isinstance(t, tuple) else set()
        for n in set().union(*[names(r) for r in rows], names(ctx[2])) - set(scales):
            v = self.env.get(n)
            if not isinstance(v, Fr):
                raise Undecided(f"prog: no number for {n}")
            vals[n] = ("num", str(v))

        def lin(t):
            try:
                a, c0 = PC.linear(PC.from_ast(PC.ast_subst(t, vals)), scales)
            except (ValueError, ZeroDivisionError) as e:
                raise Undecided(f"prog: {T.to_qpp(t)}: {e}")
            return [f.value() for f in a], c0.value()
        out = []
        for r in rows:
            op, (lhs, rhs) = r[1][0], r[2]
            big, small = (rhs, lhs) if op == "<=" else (lhs, rhs)
            (a1, c1), (a2, c2) = lin(big), lin(small)
            out.append((tuple(x - y for x, y in zip(a1, a2)), ">=" if op != "=" else "=", c2 - c1))
        cost, c0 = lin(ctx[2])
        return scales, out, cost, c0

    def prog_expand(self, x):
        """a program over families of scales at the values of its parameters, as a program over scales: each
        family v_(1..L) its scales v#1, ..., v#L, each universal row forall j in NN>=1 : j <= B => REL its instances,
        each sum its terms, each member of a family of the scope its value"""
        ctx = x[1]
        fams, decls, rest = {}, [], []
        for c in flat(ctx[1]):
            if c[0] != "decl":
                rest.append(c)
                continue
            vs = []
            for v in c[1]:
                if v[0] != "family":
                    vs.append(v)
                    continue
                lo, hi = self.val(v[2]), self.val(v[3])
                if not all(isinstance(e, Fr) and e.denominator == 1 for e in (lo, hi)):
                    raise Undecided(f"prog: the length of the family {v[1]}")
                fams[v[1]] = (int(lo), int(hi))
                vs += [("var", f"{v[1]}#{k}") for k in range(int(lo), int(hi) + 1)]
            if vs:
                decls.append(("decl", tuple(vs), c[2]))

        def sub(t, env):
            if not isinstance(t, tuple) or not t:
                return t
            ev = Ev(self.m, {**self.env, **env})
            if t[0] == "var" and len(t) == 2 and t[1] in env:
                return ("num", str(env[t[1]]))
            if t[0] == "app" and len(t) == 4 and t[3] == "idx" and t[1][0] == "var":
                if t[1][1] in fams:
                    k, (lo, hi) = ev.val(t[2][0]), fams[t[1][1]]
                    if not (isinstance(k, Fr) and k.denominator == 1 and lo <= k <= hi):
                        raise Undecided(f"prog: the member {T.to_qpp(t)} outside its family")
                    return ("var", f"{t[1][1]}#{int(k)}")
                v = ev.val(t)
                if not isinstance(v, Fr):
                    raise Undecided(f"prog: no number for {T.to_qpp(t)}")
                return ("num", str(v))
            if t[0] == "sum" and len(t) == 4:
                out = None
                for v in ev.index_values(t):
                    y = sub(t[3], {**env, t[1]: v})
                    out = y if out is None else ("bin", "+", out, y)
                return out or ("num", "0")
            return tuple(sub(y, env) for y in t)

        rows = []
        for c in rest:
            body = c[3] if c[0] == "forall" and len(c[1]) == 1 and c[2] == ("set", "NN>=1") else None
            j = c[1][0][1] if body is not None else None
            if body is not None and body[0] == "imp" and body[1][0] == "rel" and body[1][1] == ("<=",) and \
                    body[1][2][0] == ("var", j):
                b = Ev(self.m, self.env).val(sub(body[1][2][1], {}))
                if not (isinstance(b, Fr) and b.denominator == 1):
                    raise Undecided(f"prog: the bound of {T.to_qpp(c)}")
                rows += [sub(body[2], {j: Fr(k)}) for k in range(1, int(b) + 1)]
            else:
                rows.append(sub(c, {}))
        return ("prog", ("ctx", ("and", tuple(decls + rows)), sub(ctx[2], {})))

    @staticmethod
    def _nopair():
        raise Undecided("prog: a least value below zero gives no pair")

    @staticmethod
    def cap(a, b):
        out = []
        for ba in a:
            for bb in b:
                sides = tuple((max(s[0], t[0]), min(s[1], t[1])) for s, t in zip(ba, bb))
                if all(lo < hi for lo, hi in sides):
                    out.append(sides)
                elif all(lo <= hi for lo, hi in sides):
                    raise Undecided("an intersection of boxes on a face")
        return out

    def apply(self, f, terms, args):
        """a typed word whose body is a sum of positive multiples of its arguments at the parts of its point
        (sep(K, K')(x, y) := K(x) + K'(y)): the blocks of the arguments side by side, in the order of the parts"""
        names, points, body = self.m.defines[f]
        if len(names) != len(args) or not all(isinstance(a, Loss) for a in args):
            raise Undecided(f"the word {f}: its arguments are losses in the model")
        bind = {n[1]: a for n, a in zip(names, args)}
        at = {}
        for t in summands(body):
            c, app = Fr(1), t
            if t[0] == "bin" and t[1] == "*":
                c, app = Ev(self.m, {}).val(t[2]), t[3]
            if not (app[0] == "app" and app[3] == "call" and app[1][0] == "var" and app[1][1] in bind
                    and len(app[2]) == 1 and app[2][0][0] == "var" and isinstance(c, Fr) and c > 0):
                raise Undecided(f"the body of {f}: a sum of positive multiples of its arguments at its points")
            p = app[2][0][1]
            if p in at:
                raise Undecided(f"the body of {f}: a point used twice")
            at[p] = bind[app[1][1]].scaled(c)
        order = [p[1] for p in points]
        if sorted(at) != sorted(order):
            raise Undecided(f"the body of {f}: every point once")
        return Loss([b for p in order for b in at[p].blocks])

    def holds(self, c):
        k = c[0]
        if k == "paren":
            return self.holds(c[1])
        if k == "and":
            return all(self.holds(y) for y in c[1])
        if k == "imp":
            return (not self.holds(c[1])) or self.holds(c[2])
        if k == "iff":
            return self.holds(c[1]) == self.holds(c[2])
        if k == "rel":
            vals = [self.val(t) for t in c[2]]
            return all(self.compare(op, a, b) for op, a, b in zip(c[1], vals, vals[1:]))
        if k == "app" and x_is_context(self.m, c):
            p, want = self.context_pair(c)
            return pkey(p) == pkey(want)
        if k == "textrel":
            return self.graph(c) if c[1] in self.m.graphs else self.relation(c)
        if k == "decl":
            return True
        if k == "or":
            return self.holds(c[1]) or self.holds(c[2])
        if k == "not":
            return not self.holds(c[1])
        if k == "exists" and c[2] is not None and all(v[0] == "var" for v in c[1]) and self.witness(c):
            # the witness the row gives under the bound names, before any bounded reading of the type: a point of
            # NN^n with no clause that bounds it (the value of a word at a point, lem:wdepth(core dyad))
            return True
        if k in ("forall", "exists") and c[2] is not None and all(v[0] == "var" for v in c[1]):
            d = self.m.nat_dim(c[2], self.env)
            if d is not None:
                return self.bounded(c, d)
        if k in ("forall", "exists") and c[2] is not None and c[2][0] == "set" and len(c[1]) == 1 \
                and c[1][0][0] == "var" and re.fullmatch(r"NN(>=\d+)?", c[2][1]):
            # over NN, or over NN>=d from d
            return self.bounded_nat(c, int(c[2][1][4:] or 0))
        if k in ("forall", "exists") and c[2] is None and len(c[1]) == 1 and c[1][0][0] == "var":
            # over the coordinates of the tuples the index indexes
            i = c[1][0][1]
            n = self.coord_length(c[3], i, {})
            vals = (Ev(self.m, {**self.env, i: Coord(k_, n)}).holds(c[3]) for k_ in range(n))
            return all(vals) if k == "forall" else any(vals)
        if k in ("forall", "exists") and c[2] is not None and len(c[1]) == 1 and c[1][0][0] == "var":
            # a point of a tuple type of rationals that the premise names, `F(u) = y` with F(u) free of y: the clause
            # at that point, the one point that can meet the premise
            pt = self.named_point(c)
            if pt is not None:
                inside = self.m.tuple_member(c[2], self.env, pt)
                if inside is False:
                    # no point of the type meets the premise: the forall holds vacuously, the exists fails
                    return k == "forall"
                if inside:
                    return Ev(self.m, {**self.env, c[1][0][1]: pt}).holds(c[3])
        if k == "exists" and c[2] is not None and all(v[0] == "var" for v in c[1]):
            # the witness the row gives under the bound names: the body at it proves the clause; a witness that
            # fails the body proves nothing, so the clause stays undecided and the fixture fails
            row = getattr(self.m, "row", None) or {}
            if all(v[1] in row and v[1] not in self.env for v in c[1]):
                if self.witness(c):
                    return True
                raise Undecided(f"the witness of the row fails the clause {T.to_qpp(c)}")
        raise Undecided(f"the clause {T.to_qpp(c)}")

    def witness(self, c):
        """True when the row gives a witness of the existential c under its bound names and the body holds there"""
        row = getattr(self.m, "row", None) or {}
        if not all(v[1] in row and v[1] not in self.env for v in c[1]):
            return False
        env = dict(self.env)
        for v in c[1]:
            declare(self.m, env, v, c[2], row)
            if self.m.tuple_member(c[2], env, env[v[1]]) is False:
                # a witness outside its type (a coordinate of a point of NN^n that is no natural number, one of a
                # point of (QQ>0)^n that is zero) proves nothing
                return False
        return Ev(self.m, env).holds(c[3])

    def named_point(self, c):
        """the point that a premise (forall) or a part of the body (exists) names, `F(u) = y` with F(u) free of the
        bound y and its value a tuple; None when no part does"""
        name = c[1][0][1]
        body = c[3]
        while body[0] == "paren":
            body = body[1]
        guard = body[1] if c[0] == "forall" and body[0] == "imp" else body if c[0] == "exists" else None
        stack = [guard] if guard is not None else []
        while stack:
            g = stack.pop()
            while g[0] == "paren":
                g = g[1]
            if g[0] == "and":
                stack += list(g[1])
                continue
            if g[0] == "rel" and g[1] == ("=",) and ("var", name) in g[2]:
                other = g[2][0] if g[2][1] == ("var", name) else g[2][1]
                if ("var", name) in walk(other):
                    continue
                pt = self.val(other)
                if isinstance(pt, tuple):
                    return pt
        return None

    def reads_data(self, body, names):
        """whether one number or point `names` of a clause runs over the positions of data that the fixture gives: it
        occurs in body, by itself or shifted by a term free of it, as the index of a family (a_(j), a_(j + 1)) or as
        the argument of a function that the fixture gives by its values (a Table, or a family of them: P(x),
        P_(j)(x + 1), Y(u)). Its range, bounded by the clause, is then a range of positions of that data (a position
        outside it is no value, and the clause is undecided), and visiting it reads the data once: no enumeration,
        for a universal number as for an existential one, the negation of a universal over the same positions.
        A number or point bound inside body (by a quantifier or by a sum over a box) that reads data in turn is one
        more index of the same position when one entry of the data holds both (W_(p)(q), P_(j)(x): the entries of a
        family of families), and makes pairs of positions when none does (forall u : forall v : u < v => ...
        A_(u)_(i) ... A_(v)_(i)): an enumeration. Two names of one quantifier are pairs of positions too"""
        if len(names) != 1 or not self.reads_at(body, names[0]):
            return False
        entries = self.entries(body)
        for q in walk(body):
            if not isinstance(q, tuple) or len(q) != 4:
                continue
            if q[0] in ("forall", "exists") and q[2] is not None and len(q[1]) == 1 and q[1][0][0] == "var" \
                    and self.nat_type(q[2]) and self.reads_at(q[3], q[1][0][1]):
                inner = q[1][0][1]
            elif q[0] == "sum" and isinstance(q[1], str) and q[2] is not None and q[2][0] == "le" \
                    and self.reads_at(q[3], q[1]):
                inner = q[1]
            else:
                continue
            if not any({names[0], inner} <= e for e in entries):
                return False
        return True

    def entries(self, body):
        """the entries of data that body reads, each as the set of the numbers and points that index it, by themselves
        or shifted by a term free of them: a_(j)_(i) by {j, i}, W_(p)(q) by {p, q} when W_(p) is a function that the
        fixture gives by its values"""
        def base(t):
            while isinstance(t, tuple) and t and t[0] == "paren":
                t = t[1]
            if isinstance(t, tuple) and t and t[0] == "var":
                return t[1]
            if isinstance(t, tuple) and len(t) == 4 and t[0] == "bin" and t[1] in ("+", "-") and t[2][0] == "var" \
                    and t[2] not in walk(t[3]):
                return t[2][1]
            return None

        out = []
        for x in walk(body):
            names, y = set(), x
            while isinstance(y, tuple) and len(y) == 4 and y[0] == "app" and (
                    y[3] == "idx" or (y[3] == "call" and len(y[2]) == 1 and self.is_data(y[1]))):
                names |= {b for b in map(base, y[2]) if b is not None}
                y = y[1]
            if len(names) > 1:
                out.append(names)
        return out

    def is_data(self, head):
        """whether head names a function that the fixture gives by its values: a Table, or a family of Tables, read at
        its indices"""
        while head[0] == "app" and len(head) == 4 and head[3] == "idx":
            head = head[1]
        v = self.env.get(head[1]) if head[0] == "var" else None
        if isinstance(v, dict):
            v = tuple(v.values())  # a family of functions, by its indices
        return isinstance(v, Table) or (isinstance(v, tuple) and bool(v) and all(isinstance(e, Table) for e in v))

    def nat_type(self, ty):
        """whether a quantifier over ty is one over NN, NN>=d or NN^n, whose reading is guarded (or of a type the
        environment cannot size, taken as one)"""
        if ty[0] == "set" and isinstance(ty[1], str) and re.fullmatch(r"NN(>=\d+)?", ty[1]):
            return True
        try:
            return self.m.nat_dim(ty, self.env) is not None
        except Exception:
            return True

    def reads_at(self, body, name):
        """whether the number or point name occurs in body, by itself or shifted by a term free of it, as the index of
        a family or as the argument of a function that the fixture gives by its values (reads_data)"""
        me = ("var", name)

        def free(t):
            return me not in walk(t)

        def shift(t):
            while isinstance(t, tuple) and t and t[0] == "paren":
                t = t[1]
            return t == me or (isinstance(t, tuple) and len(t) == 4 and t[0] == "bin" and t[1] in ("+", "-")
                               and t[2] == me and free(t[3]))

        for x in walk(body):
            if len(x) == 4 and x[0] == "app" and x[3] == "idx" and any(shift(i) for i in x[2]):
                return True
            if len(x) == 4 and x[0] == "app" and x[3] == "call" and len(x[2]) == 1 and shift(x[2][0]) \
                    and self.is_data(x[1]):
                return True
        return False

    def bounded_nat(self, c, lo=0):
        """a quantifier over the natural numbers, read when the premise (forall) or the body (exists) bounds the
        number, `x <= t` (or `x < t`) with t free of x: the numbers up to the bound decide the clause (by
        enumeration)"""
        name = c[1][0][1]
        body = c[3]
        while body[0] == "paren":
            body = body[1]
        fixed = self.pinned(c, body, lo)
        if fixed is None:
            fixed = self.least_integer(c, body, lo)
        if fixed is not None:
            return fixed
        if c[0] == "forall":
            fixed = self.meeting(c, lo)
            if fixed is not None:
                return fixed
        if not self.reads_data(body, [name]):
            EN.enumerating(f"the numbers up to a bound: {T.to_qpp(c)}")
        guard = body[1] if c[0] == "forall" and body[0] == "imp" else body if c[0] == "exists" else None
        parts, stack = [], [guard] if guard is not None else []
        while stack:
            g = stack.pop()
            while g[0] == "paren":
                g = g[1]
            if g[0] == "and":
                stack += list(g[1])
            else:
                parts.append(g)
        for g in parts:
            if g[0] != "rel" or len(g[1]) != 1 or g[1][0] not in ("<=", "<"):
                continue
            x, t = g[2]
            if x != ("var", name) or ("var", name) in walk(t):
                continue
            h = self.val(t)
            if not isinstance(h, Fr):
                continue
            top = int(h // 1) if g[1][0] == "<=" else int(-((-h) // 1)) - 1
            vals = (Ev(self.m, {**self.env, name: Fr(x_)}).holds(c[3]) for x_ in range(lo, max(top, lo - 1) + 1))
            return all(vals) if c[0] == "forall" else any(vals)
        top = getattr(self.m, "bounds", {}).get(name)
        if top is not None:
            vals = (Ev(self.m, {**self.env, name: Fr(x_)}).holds(c[3]) for x_ in range(lo, max(top, lo - 1) + 1))
            return all(vals) if c[0] == "forall" else any(vals)
        raise Undecided(f"the clause {T.to_qpp(c)}: a quantifier over NN is read when a clause {name} <= t bounds "
                        "it, or the fixture gives its bound")

    def meeting(self, c, lo):
        """a clause over the pairs u < v of positions of a family of the row that meet, `1 <= (sum l, X * Y)` with X
        reading u and Y reading v at the coordinate l, natural numbers: the sum is at least 1 if and only if some
        coordinate l has X >= 1 and Y >= 1, so the pairs are read through the coordinates, each position once.
        (i) `forall u : P(u) => forall v : u < v => v <= t => Q(u), R(v), meet => C(v)`: it fails if and only if a
        position u with P and Q and a later v with R and not C share a coordinate; with last(l) the last such v whose
        Y at l is at least 1, it holds if and only if last(l) <= u at each coordinate l where X at u is at least 1.
        (ii) `forall u : P(u) => exists v : u < v, v <= t, Q(u), meet, R(v)` (P bounds u): it holds if and only if each
        u with P has Q and some coordinate l with X >= 1 and last(l) > u, last(l) the last v with R whose Y at l is at
        least 1.
        (iii) `forall u : forall v : u < v => v <= t => meet => forall i : F_(u)_(i) <= F_(v)_(i)` with X = F_(u)_(l)
        and Y = F_(v)_(l): each u is below the first later position w(u) that meets it if and only if each u is below
        every later position that meets it (downward on u: a later v that meets u meets w(u), since the support of
        F_(u) lies in that of F_(w(u)), and F_(w(u)) <= F_(v) by the clause at w(u)).
        None when the clause is not of these forms"""
        U, V = ("var", c[1][0][1]), None

        def strip(t):
            while isinstance(t, tuple) and t and t[0] == "paren":
                t = t[1]
            return t

        def split(t, out):
            t = strip(t)
            if t[0] == "and":
                for y in t[1]:
                    split(y, out)
            else:
                out.append(t)

        def chain(t, out):
            """the premises of an implication chain, its conjunctions split, and its conclusion"""
            t = strip(t)
            while t[0] == "imp":
                split(t[1], out)
                t = strip(t[2])
            return t

        def bound(g, x):
            """the largest number that `x <= t` or `x < t` (t free of u and v) allows, else None"""
            if not (g[0] == "rel" and len(g[1]) == 1 and g[1][0] in ("<=", "<") and strip(g[2][0]) == x
                    and U not in walk(g[2][1]) and (V is None or V not in walk(g[2][1]))):
                return None
            h = self.val(g[2][1])
            if not isinstance(h, Fr):
                return None
            return int(h // 1) if g[1][0] == "<=" else int(-((-h) // 1)) - 1

        pre = []
        q = chain(c[3], pre)
        if not (q[0] in ("forall", "exists") and len(q[1]) == 1 and q[1][0][0] == "var" and q[2] is not None
                and q[2][0] == "set" and isinstance(q[2][1], str) and re.fullmatch(r"NN(>=\d+)?", q[2][1])):
            return None
        V = ("var", q[1][0][1])
        if any(V in walk(g) for g in pre):
            return None
        parts = []
        concl = chain(q[3], parts) if q[0] == "forall" else split(q[3], parts)
        order, top, meet, on_u, on_v = False, None, None, [], []
        for g in parts:
            if g[0] == "rel" and g[1] == ("<",) and tuple(map(strip, g[2])) == (U, V):
                order = True
                continue
            b = bound(g, V)
            if b is not None:
                top = b if top is None else min(top, b)
                continue
            if U in walk(g) and V in walk(g):
                if meet is not None or not (g[0] == "rel" and g[1] == ("<=",) and strip(g[2][0]) == ("num", "1")):
                    return None
                s_ = strip(g[2][1])
                if not (s_[0] == "sum" and isinstance(s_[1], str) and s_[2] is None):
                    return None
                f_ = strip(s_[3])
                if not (f_[0] == "bin" and f_[1] == "*"):
                    return None
                x_, y_ = f_[2], f_[3]
                if U in walk(y_):
                    x_, y_ = y_, x_
                if V in walk(x_) or U in walk(y_) or U not in walk(x_) or V not in walk(y_):
                    return None
                meet = (s_[1], x_, y_)
                continue
            (on_v if V in walk(g) else on_u).append(g)
        if not order or top is None or meet is None:
            return None
        l, X, Y = meet
        if q[0] == "forall":
            if U in walk(concl):
                F = strip(X)
                ok = (not pre and not on_u and not on_v and concl[0] == "forall" and concl[2] is None
                      and len(concl[1]) == 1 and concl[1][0][0] == "var")
                if ok:
                    i = concl[1][0]
                    r = strip(concl[3])
                    ok = (F[0] == "app" and F[3] == "idx" and F[2] == (("var", l),) and strip(F[1])[0] == "app"
                          and strip(F[1])[3] == "idx" and strip(F[1])[2] == (U,)
                          and U not in walk(strip(F[1])[1]) and V not in walk(strip(F[1])[1])
                          and strip(Y) == ("app", ("app", strip(F[1])[1], (V,), "idx"), (("var", l),), "idx")
                          and r[0] == "rel" and r[1] == ("<=",)
                          and tuple(map(strip, r[2])) == (("app", strip(F[1]), (i,), "idx"),
                                                          ("app", ("app", strip(F[1])[1], (V,), "idx"), (i,), "idx")))
                if not ok:
                    return None
                form = "nested"
            else:
                form = "after"
            uhi = top - 1
        else:
            if U in walk(concl or ()):
                return None
            form = "exists"
            uhi = None
        for g in pre:
            b = bound(g, U)
            if b is not None:
                uhi = b if uhi is None else min(uhi, b)
        if uhi is None:
            return None
        v0 = max(int(q[2][1][4:] or 0), lo + 1)
        u_, v_ = U[1], V[1]

        def support(name, x, t):
            """the coordinates where t, read at the position x, is at least 1; None when a value is no natural
            number"""
            env = {**self.env, name: Fr(x)}
            n = Ev(self.m, env).coord_length(t, l, {})
            out = []
            for k_ in range(n):
                y = Ev(self.m, {**env, l: Coord(k_, n)}).val(t)
                if not isinstance(y, Fr) or y.denominator != 1 or y < 0:
                    return None
                if y >= 1:
                    out.append(k_)
            return out

        def holds(env, gs):
            ev = Ev(self.m, {**self.env, **env})
            return all(ev.holds(g) for g in gs)

        if form == "nested":
            nxt = {}  # each coordinate: the first later position whose F is at least 1 there
            for x in range(top, lo - 1, -1):
                if x <= uhi:
                    sx = support(u_, x, X)
                    if sx is None:
                        return None
                    w = min((nxt[j] for j in sx if j in nxt), default=None)
                    if w is not None and not holds({u_: Fr(x), v_: Fr(w)}, [concl]):
                        return False
                if x >= v0:
                    sy = support(v_, x, Y)
                    if sy is None:
                        return None
                    nxt.update((j, x) for j in sy)
            return True
        last = {}  # each coordinate: the last position v (with R and, in (i), not C) whose Y is at least 1 there
        for y in range(v0, top + 1):
            env = {v_: Fr(y)}
            if holds(env, on_v) and (form == "exists" or not holds(env, [concl])):
                sy = support(v_, y, Y)
                if sy is None:
                    return None
                last.update((j, y) for j in sy)
        for x in range(lo, uhi + 1):
            env = {u_: Fr(x)}
            if form == "after":
                if not holds(env, pre + on_u):
                    continue
                sx = support(u_, x, X)
                if sx is None:
                    return None
                if any(last.get(j, -1) > x for j in sx):
                    return False
            else:
                if not holds(env, pre):
                    continue
                if not holds(env, on_u):
                    return False
                sx = support(u_, x, X)
                if sx is None:
                    return None
                if not any(last.get(j, -1) > x for j in sx):
                    return False
        return True

    def pinned(self, c, body, lo):
        """a quantifier over NN>=lo whose number an equation of the premise (forall) or of the body (exists) fixes,
        `x = t` or `x + a = t` with t and a free of x: every other number fails that equation, so the clause is read
        at the one number val(t) - val(a); when that is not a number of NN>=lo, the forall holds and the exists fails.
        None when no such equation is there"""
        name = c[1][0][1]
        me = ("var", name)
        guard = body[1] if c[0] == "forall" and body[0] == "imp" else body if c[0] == "exists" else None
        parts, stack = [], [guard] if guard is not None else []
        while stack:
            g = stack.pop()
            while g[0] == "paren":
                g = g[1]
            if g[0] == "and":
                stack += list(g[1])
            else:
                parts.append(g)

        def strip(t):
            while t[0] == "paren":
                t = t[1]
            return t

        for g in parts:
            if g[0] != "rel" or g[1] != ("=",):
                continue
            for x, t in (g[2], g[2][::-1]):
                x = strip(x)
                if me in walk(t):
                    continue
                if x == me:
                    shift = None
                elif x[0] == "bin" and x[1] == "+" and me in (strip(x[2]), strip(x[3])):
                    shift = x[3] if strip(x[2]) == me else x[2]
                    if me in walk(shift):
                        continue
                else:
                    continue
                v = self.val(t)
                a = Fr(0) if shift is None else self.val(shift)
                if not (isinstance(v, Fr) and isinstance(a, Fr)):
                    continue
                v -= a
                if v.denominator != 1 or v < lo:
                    return c[0] == "forall"
                return Ev(self.m, {**self.env, name: v}).holds(c[3])
        return None

    def least_integer(self, c, body, lo):
        """an existential over NN>=lo whose body is a conjunction of relations affine in its number x: each relation
        is a + s * x >= 0 or > 0 with s read from its values at x = 0 and x = 1; the relations with s > 0 bound x
        from below, so the least number of NN>=lo above them (a ceiling) is the one number to read: if any number
        meets the body, this one does, since the other relations bound x from above. None when the body is not such
        a conjunction"""
        if c[0] != "exists":
            return None
        name = c[1][0][1]
        me = ("var", name)

        def degree(t):
            """the degree of t in x when t is a polynomial in x, else None"""
            while t[0] == "paren":
                t = t[1]
            if me not in walk(t):
                return 0
            if t == me:
                return 1
            if t[0] == "bin" and t[1] in ("+", "-"):
                a, b = degree(t[2]), degree(t[3])
                return None if a is None or b is None else max(a, b)
            if t[0] == "bin" and t[1] == "*":
                a, b = degree(t[2]), degree(t[3])
                return None if a is None or b is None else a + b
            if t[0] == "bin" and t[1] == "/" and me not in walk(t[3]):
                return degree(t[2])
            return None

        parts, stack = [], [body]
        while stack:
            g = stack.pop()
            while g[0] == "paren":
                g = g[1]
            if g[0] == "and":
                stack += list(g[1])
            else:
                parts.append(g)
        if not parts:
            return None
        rows = []  # (difference, strict): difference >= 0 or > 0
        for g in parts:
            if g[0] != "rel" or not all(op in ("<=", "<", ">=", ">", "=") for op in g[1]):
                return None
            if any(degree(t) not in (0, 1) for t in g[2]):
                return None
            for op, a, b in zip(g[1], g[2], g[2][1:]):
                if op in ("<=", "<", "="):
                    rows.append((("bin", "-", b, a), op == "<"))
                if op in (">=", ">", "="):
                    rows.append((("bin", "-", a, b), op == ">"))
        at0, at1 = Ev(self.m, {**self.env, name: Fr(0)}), Ev(self.m, {**self.env, name: Fr(1)})
        x = Fr(lo)
        for d, strict in rows:
            a, a1 = at0.val(d), at1.val(d)
            if not (isinstance(a, Fr) and isinstance(a1, Fr)):
                return None
            slope = a1 - a
            if slope > 0:
                bound = -a / slope
                least = bound // 1 + 1 if strict else -((-bound) // 1)
                x = max(x, Fr(least))
        return Ev(self.m, {**self.env, name: x}).holds(c[3])

    def separable(self, c, n):
        """`forall u, w in X : (box bounds on u and w) => forall i : L <= R` (or <) where each term of L and R, after
        a factor free of the points is spread over a sum, reads u, w or neither: the relation is g(u) + k <= h(w)
        with g the terms of u (those of L less those of R), h those of w, k those of neither, and it holds for every
        pair if and only if max over the box of g + k <= min over the box of h, each read over one point. None when
        the clause is not of this form"""
        u, w = (("var", v[1]) for v in c[1])
        body = c[3]
        while body[0] == "paren":
            body = body[1]
        if body[0] != "imp":
            return None
        boxes = {}
        parts, stack = [], [body[1]]
        while stack:
            g = stack.pop()
            while g[0] == "paren":
                g = g[1]
            if g[0] == "and":
                stack += list(g[1])
            else:
                parts.append(g)
        for g in parts:
            if not (g[0] == "forall" and g[2] is None and len(g[1]) == 1 and g[3][0] == "rel" and g[3][1] == ("<=",)):
                return None
            i, (x, t) = g[1][0], g[3][2]
            pt = next((p_ for p_ in (u, w) if x == ("app", p_, (i,), "idx")), None)
            if pt is None or u in walk(t) or w in walk(t) or pt[1] in boxes:
                return None
            hi = [Ev(self.m, {**self.env, i[1]: Coord(k_, n)}).val(t) for k_ in range(n)]
            if not all(isinstance(h_, Fr) for h_ in hi):
                return None
            boxes[pt[1]] = [tuple(Fr(x_) for x_ in q) for q in product(*(range(max(int(h_ // 1), -1) + 1) for h_ in hi))]
        if set(boxes) != {u[1], w[1]}:
            return None
        concl, coords = body[2], []
        while concl[0] == "paren":
            concl = concl[1]
        while concl[0] == "forall" and concl[2] is None and len(concl[1]) == 1 and concl[1][0][0] == "var":
            coords.append(concl[1][0][1])
            concl = concl[3]
            while concl[0] == "paren":
                concl = concl[1]
        if not (concl[0] == "rel" and len(concl[1]) == 1 and concl[1][0] in ("<=", "<")):
            return None

        def terms(t, out, sign):
            """the additive terms of t with their signs, a factor free of the points spread over a sum"""
            while t[0] == "paren":
                t = t[1]
            if t[0] == "bin" and t[1] in ("+", "-"):
                terms(t[2], out, sign)
                terms(t[3], out, sign if t[1] == "+" else -sign)
                return
            if t[0] == "bin" and t[1] == "*":
                for f, g in ((t[2], t[3]), (t[3], t[2])):
                    while g[0] == "paren":
                        g = g[1]
                    if u not in walk(f) and w not in walk(f) and g[0] == "bin" and g[1] in ("+", "-"):
                        inner = []
                        terms(g, inner, sign)
                        out += [(("bin", "*", f, y), sg) for y, sg in inner]
                        return
            out.append((t, sign))

        found = []
        terms(concl[2][0], found, 1)
        terms(concl[2][1], found, -1)  # L - R <= 0
        side = {"u": [], "w": [], "none": []}
        for t, sg in found:
            on = (u in walk(t), w in walk(t))
            if all(on):
                return None
            side["u" if on[0] else "w" if on[1] else "none"].append((t, sg))
        if not side["u"] or not side["w"]:
            return None

        def total(env, ts):
            out = Fr(0)
            for t, sg in ts:
                y = Ev(self.m, env).val(t)
                if not isinstance(y, Fr):
                    raise Undecided(f"the term {T.to_qpp(t)}")
                out += sg * y
            return out

        if not boxes[u[1]] or not boxes[w[1]]:
            return True  # an empty box: no pair
        at = Ev(self.m, {**self.env, u[1]: boxes[u[1]][0], w[1]: boxes[w[1]][0]})
        envs = [{}]
        for b in coords:
            m_ = at.coord_length(concl, b, {})
            envs = [{**x, b: Coord(k_, m_)} for x in envs for k_ in range(m_)]
        for name, ts in (("u", side["u"]), ("w", side["w"])):
            pt = u if name == "u" else w
            expr = None
            for t, _ in ts:
                expr = t if expr is None else ("bin", "+", expr, t)
            if not self.reads_data(expr, [pt[1]]):
                EN.enumerating(f"the lattice points of a box: {T.to_qpp(c)}")
        strict = concl[1][0] == "<"
        for x in envs:
            env = {**self.env, **x}
            # L - R = G(u) + H(w) + K <= 0 for all u, w iff max G + max H + K <= 0
            top_u = max(total({**env, u[1]: q}, side["u"]) for q in boxes[u[1]])
            top_w = max(total({**env, w[1]: q}, side["w"]) for q in boxes[w[1]])
            k = total(env, side["none"])
            v = top_u + top_w + k
            if v > 0 or (strict and v == 0):
                return False
        return True

    def injective(self, c, n):
        """`forall u, w in X : (box bounds on u and w), E => forall i : u_(i) = w_(i)` where E is a conjunction of
        equations (each under quantifiers over coordinates or not) linear in the two points and depending on them
        through u - w alone: E says D (u - w) = 0 for a matrix D read from the coefficients of the equations (their
        values at the unit points), and when D has rank n the clause holds, since D d = 0 has the only solution
        d = 0. None when the clause is not of this form or D has a smaller rank (the box then decides)"""
        u, w = (("var", v[1]) for v in c[1])
        body = c[3]
        while body[0] == "paren":
            body = body[1]
        if body[0] != "imp":
            return None
        concl = body[2]
        while concl[0] == "paren":
            concl = concl[1]
        if not (concl[0] == "forall" and concl[2] is None and len(concl[1]) == 1 and concl[3][0] == "rel"
                and concl[3][1] == ("=",)):
            return None
        i = concl[1][0]
        if {concl[3][2][0], concl[3][2][1]} != {("app", u, (i,), "idx"), ("app", w, (i,), "idx")}:
            return None
        parts, stack = [], [body[1]]
        while stack:
            g = stack.pop()
            while g[0] == "paren":
                g = g[1]
            if g[0] == "and":
                stack += list(g[1])
            else:
                parts.append(g)
        eqs = []
        for g in parts:
            binders, e = [], g
            while e[0] == "forall" and e[2] is None and len(e[1]) == 1 and e[1][0][0] == "var":
                binders.append(e[1][0][1])
                e = e[3]
                while e[0] == "paren":
                    e = e[1]
            if e[0] == "rel" and e[1] == ("<=",) and len(binders) == 1 and \
                    e[2][0] in (("app", u, (("var", binders[0]),), "idx"), ("app", w, (("var", binders[0]),), "idx")) \
                    and u not in walk(e[2][1]) and w not in walk(e[2][1]):
                continue  # a box bound
            if e[0] == "rel" and e[1] == ("=",) and all(poly_degree(t, {u[1], w[1]}) in (0, 1) for t in e[2]):
                eqs.append((binders, e))
                continue
            return None
        if not eqs:
            return None
        zero = tuple(Fr(0) for _ in range(n))
        unit = [tuple(Fr(int(a == j)) for a in range(n)) for j in range(n)]
        rows = []
        for binders, e in eqs:
            diff = ("bin", "-", e[2][0], e[2][1])
            envs = [{}]
            for b in binders:
                m_ = self.coord_length(e, b, {})
                envs = [{**x, b: Coord(k, m_)} for x in envs for k in range(m_)]
            for x in envs:
                def f(pu, pw):
                    y = Ev(self.m, {**self.env, **x, u[1]: pu, w[1]: pw}).val(diff)
                    if not isinstance(y, Fr):
                        raise Undecided(f"the equation {T.to_qpp(e)}")
                    return y
                f0 = f(zero, zero)
                row = [f(unit[j], zero) - f0 for j in range(n)]
                if f0 != 0 or any(f(zero, unit[j]) - f0 != -row[j] for j in range(n)):
                    return None
                rows.append(row)
        if SX.rank(rows) == n:
            return True
        return None

    def bounded(self, c, n):
        """a quantifier over the points of NN^n, read when the premise (forall) or the body (exists) bounds each
        point coordinatewise, `forall i : u_(i) <= t` with t free of the points: a point outside its box fails that
        clause, so the points of the boxes decide the clause (by enumeration; over several points, by points_tied
        where it applies, which reads the same tuples in the same order)"""
        names = [v[1] for v in c[1]]
        if c[0] == "forall" and len(names) == 2:
            held = self.injective(c, n)
            if held is None:
                held = self.separable(c, n)
            if held is not None:
                return held
        body = c[3]
        while body[0] == "paren":
            body = body[1]
        guard = body[1] if c[0] == "forall" and body[0] == "imp" else body if c[0] == "exists" else None
        parts = []
        stack = [guard] if guard is not None else []
        while stack:
            g = stack.pop()
            while g[0] == "paren":
                g = g[1]
            if g[0] == "and":
                stack += list(g[1])
            else:
                parts.append(g)
        boxes = []
        data = c[0] == "forall" and self.reads_data(body, names)
        for name in names:
            box = None
            for g in parts:
                if not (g[0] == "forall" and g[2] is None and len(g[1]) == 1 and g[3][0] == "rel"
                        and g[3][1] == ("<=",)):
                    continue
                i = g[1][0]
                x, t = g[3][2]
                if x != ("app", ("var", name), (i,), "idx") or any(("var", m) in walk(t) for m in names):
                    continue
                hi = [Ev(self.m, {**self.env, i[1]: Coord(k_, n)}).val(t) for k_ in range(n)]
                if not all(isinstance(h, Fr) for h in hi):
                    continue
                box = [range(max(int(h // 1), -1) + 1) for h in hi]
                break
            if box is None and len(names) == 1:
                # a point that the premise names, `F(u) = s` with F(u) free of s: the clause at that point
                for g in parts:
                    if g[0] == "rel" and g[1] == ("=",) and ("var", name) in g[2]:
                        other = g[2][0] if g[2][1] == ("var", name) else g[2][1]
                        if ("var", name) in walk(other):
                            continue
                        pt = self.val(other)
                        if isinstance(pt, tuple) and len(pt) == n:
                            return Ev(self.m, {**self.env, name: pt}).holds(c[3])
            if box is None:
                grid = self.identity_grid(c, names, n)
                if grid is not None:
                    return grid
                raise Undecided(f"the clause {T.to_qpp(c)}: a quantifier over NN^n is read when a clause "
                                f"forall i : {name}_(i) <= t bounds its points, or when it is an identity of "
                                "polynomials in them")
            if not data:
                EN.enumerating(f"the lattice points of a box: {T.to_qpp(c)}")
            boxes.append([tuple(Fr(x) for x in pt) for pt in product(*box)])
        if len(names) > 1:
            tied = self.points_tied(c, boxes)
            if tied is not None:
                return tied
        vals = (Ev(self.m, {**self.env, **dict(zip(names, pts))}).holds(c[3]) for pts in product(*boxes))
        return all(vals) if c[0] == "forall" else any(vals)

    def points_tied(self, c, boxes):
        """bounded for a universal c over several points of NN^n that has a pair_plan, on the points of their boxes:
        a part of the guard on one point is read once at each point, a tie by an index of the points by their tied
        coordinates, and the conclusion once per tuple of the values of the terms through which it reads the points
        (point_reads). The tuples of points that meet the guard are read in the order of the boxes, so the first one
        at which the conclusion fails or is undecided is the one that bounded reads first. None when a part of the
        guard is undecided at a point, or a box is empty: bounded then reads every tuple"""
        plan = pair_plan(c)
        if plan is None or not all(boxes):
            return None
        names, ones, ties, concl, reads = plan
        K = len(names)
        try:
            live = []
            for k, box in enumerate(boxes):
                mine = [g for kk, g in ones if kk == k]
                live.append([p for p in box
                             if all([Ev(self.m, {**self.env, names[k]: p}).holds(g) for g in mine])])
            sample = {**self.env, **{name: box[0] for name, box in zip(names, boxes)}}
            tied = {}
            for k, k2, g, i, C in ties:
                n = Ev(self.m, sample).coord_length(g[3], i, {})
                if any(len(p) != n for p in boxes[k] + boxes[k2]):
                    return None
                at = [x for x in range(n) if C is None or Ev(self.m, {**sample, i: Coord(x, n)}).holds(C)]
                tied.setdefault(k2, []).append((k, at))
        except Exception:
            return None
        # each live point with the number of the values through which the conclusion reads it (None: not read)
        ids = {}
        keyed = []
        for k in range(K):
            mine = None if reads is None else [t for kk, t in reads if kk == k]
            row = []
            for p in live[k]:
                kid = None
                if mine is not None:
                    try:
                        ev = Ev(self.m, {**self.env, names[k]: p})
                        kid = ids.setdefault((k, tuple(value_key(ev.val(t)) for t in mine)), len(ids))
                    except Exception:
                        kid = None
                row.append((p, kid))
            keyed.append(row)
        index = []
        for k in range(K):
            ts = tied.get(k)
            if not ts:
                index.append(None)
                continue
            d = {}
            for e in keyed[k]:
                d.setdefault(tuple(tuple(e[0][x] for x in at) for _, at in ts), []).append(e)
            index.append((ts, d))
        done = set()  # the tuples of numbers of values at which the conclusion holds

        def scan(k, chosen):
            ix = index[k]
            cands = keyed[k] if ix is None else \
                ix[1].get(tuple(tuple(chosen[k1][0][x] for x in at) for k1, at in ix[0]), ())
            if k + 1 < K:
                return all(scan(k + 1, chosen + (e,)) for e in cands)
            head = tuple(e[1] for e in chosen)
            for e in cands:
                key = head + (e[1],)
                if key in done:
                    continue
                pts = [q[0] for q in chosen] + [e[0]]
                if not Ev(self.m, {**self.env, **dict(zip(names, pts))}).holds(concl):
                    return False
                if None not in key:
                    done.add(key)
            return True
        return scan(0, ())

    def identity_grid(self, c, names, n):
        """a universal over the points of NN^n whose body is an equation of polynomials in their coordinates, of
        degree at most D in them: it holds at every point if and only if it holds on the grid {0, ..., D}^n of each
        point (a polynomial of degree at most D in each coordinate that vanishes there is zero); None when the clause
        is not one. At degree at most 1 the equation is read by its coefficients: f = L - R is affine,
        f(x) = f(0) + sum_j (f(e_j) - f(0)) x_j, so it vanishes at every point if and only if it vanishes at 0 and at
        each unit point e_j, one coordinate of one point set to 1; no point is visited"""
        body = c[3]
        while body[0] == "paren":
            body = body[1]
        if c[0] != "forall" or body[0] != "rel" or body[1] != ("=",):
            return None
        degs = [poly_degree(t, set(names)) for t in body[2]]
        if any(d is None for d in degs):
            return None
        D = max(degs)
        if D <= 1:
            zero = dict.fromkeys(names, tuple(Fr(0) for _ in range(n)))
            units = [{**zero, name: tuple(Fr(int(i == j)) for i in range(n))} for name in names for j in range(n)]
            return all(Ev(self.m, {**self.env, **pt}).holds(body) for pt in [zero] + (units if D == 1 else []))
        EN.enumerating(f"the grid {{0, ..., {D}}}^{n}: {T.to_qpp(c)}")
        pts = [tuple(Fr(x) for x in pt) for pt in product(range(D + 1), repeat=n)]
        return all(Ev(self.m, {**self.env, **dict(zip(names, ps))}).holds(body) for ps in product(pts, repeat=len(names)))

    def compare(self, op, a, b):
        if op == "subseteq":
            if not all(any(all(t[0] <= s[0] and s[1] <= t[1] for s, t in zip(ba, bb)) for bb in b) for ba in a):
                if len(b) <= 1:
                    return False
                raise Undecided("a box covered by a union of boxes")
            return True
        if isinstance(a, Fr) and isinstance(b, Fr):
            ka, kb = a, b
        elif isinstance(a, Coord) and isinstance(b, Coord) and op in ("=", "!=", "<=", "<", ">=", ">"):
            # two indices: counts with their order and equality; of two ranges, compared as the
            # counts they are, from 1, as the generated Lean reads them ((iota : N) + 1 = (p : N) + 1)
            ka, kb = a.k, b.k
        elif all(isinstance(y, (Coord, Fr)) for y in (a, b)) and op in ("=", "!=", "<=", "<", ">=", ">"):
            # an index against a count or an index of another range: the counts they are, from 1
            ka, kb = (Fr(y.k + 1) if isinstance(y, Coord) else y for y in (a, b))
        elif op in ("=", "!=") and isinstance(a, tuple) and isinstance(b, tuple) and len(a) == len(b) and all(
                isinstance(x, Fr) for x in a + b):
            # points of NN^n (and pairs, whose order key is injective): equal coordinate by coordinate
            ka, kb = a, b
        elif (a == TOP or isinstance(a, tuple) and len(a) == 2) and (b == TOP or isinstance(b, tuple) and len(b) == 2):
            ka, kb = pkey(a), pkey(b)
        else:
            raise Undecided(f"the comparison {op} of {a!r} and {b!r}")
        return {"=": ka == kb, "!=": ka != kb, "<=": ka <= kb, "<": ka < kb, ">=": ka >= kb, ">": ka > kb}[op]

    def model_pair(self, c):
        """the model's pair of a context applied (its arguments but the last)"""
        sig = self.m.contexts[c[1][1]]
        kinds = [self.m.kind(t, self.env)[0] for _, t in sig]
        if len(c[2]) != len(sig) or kinds[-1] != "pair" or sorted(kinds[:-1]) not in (
                ["loss", "region"], ["loss", "region", "tuple"]):
            raise Undecided(f"the context {c[1][1]}: a loss, a region, a weight or not, and a pair last")
        vals = {kd: self.val(t) for kd, t in zip(kinds[:-1], c[2][:-1])}
        return pair(vals["loss"], vals["region"], vals.get("tuple"))

    def context_pair(self, c):
        """(the model's pair, the pair the application names) of a context applied"""
        return self.model_pair(c), self.val(c[2][-1])

    def graph(self, c):
        """a relation read as the graph of the model's pair (a fixture's \"graph\"): the loss has the pair (l, m),
        not top, over the region for the weight"""
        K, lam, m, q, B = (self.val(t) for t in c[2])
        if not (isinstance(K, Loss) and isinstance(lam, Fr) and isinstance(m, Fr) and isinstance(q, tuple)
                and isinstance(B, list)):
            raise Undecided(f"the graph {T.to_qpp(c)}: a loss, a rational, a natural number, a weight, a region")
        p = pair(K, B, q)
        return p != TOP and pkey(p) == pkey((lam, m))

    def relation(self, c):
        rel = self.m.relations.get(c[1])
        if rel is None:
            raise Undecided(f"no relation row for {T.to_qpp(c)}")
        params, clauses = rel
        env = {p: self.val(a) for p, a in zip(params, c[2])}
        for p in list(env):
            if isinstance(env[p], dict):
                env.update({f"{p}.{q}": v for q, v in env[p].items()})  # the parts of a bundle
        for cl in clauses:
            # the implicit parameters (k, n of Pr in Prog(k, n)) from the shapes of the arguments
            if cl[0] == "decl":
                for v in cl[1]:
                    if v[0] == "var" and v[1] in env:
                        self.m.bind_dims(cl[2], env[v[1]], env)
        inner = Ev(self.m, env)
        for cl in clauses:
            if cl[0] == "decl":
                continue
            if not inner.shape(cl):
                return False
        return True

    def shape(self, cl):
        """the three clause shapes of a relation row that the model decides"""
        while cl[0] == "paren":
            cl = cl[1]
        if cl[0] == "exists" and cl[2] == ("set", "QQ>0") and cl[3][0] == "forall" and len(cl[3][1]) == 1:
            consts = [v[1] for v in cl[1]]
            w, region, body = cl[3][1][0][1], self.val(cl[3][2]), cl[3][3]
            while body[0] == "paren":
                body = body[1]
            if body[0] == "rel" and body[1] == ("<=",) and len(consts) == 1 and body[2][0] == ("var", consts[0]):
                L = self.loss_at(body[2][1], w)
                v = least_value(L, region)
                return v is None or v > 0
            if body[0] == "rel" and body[1] == ("<=",) and len(consts) == 1:
                b = self.scaled_at(body[2][1], consts[0], w)
                if b is not None:
                    return below(self.loss_at(body[2][0], w), b, region)
            if body[0] == "rel" and body[1] == ("<=", "<=") and len(consts) == 2:
                lo, mid, hi = body[2]
                a = self.scaled_at(lo, consts[0], w)
                b = self.scaled_at(hi, consts[1], w)
                L2 = self.loss_at(mid, w)
                if a is not None and b is not None and a is b:
                    return comparable(L2, a, region)
        if cl[0] == "rel":
            return self.holds(cl)
        try:
            return self.holds(cl)  # a clause on coordinates, points and bundles, read as a statement row reads it
        except Undecided:
            raise Undecided(f"the clause {T.to_qpp(cl)} of a relation row")

    def loss_at(self, t, w):
        while t[0] == "paren":
            t = t[1]
        if t[0] == "app" and t[3] == "call" and len(t[2]) == 1 and t[2][0] == ("var", w):
            L = self.val(t[1])
            if isinstance(L, Loss):
                return L
        raise Undecided(f"not a loss at {w}: {T.to_qpp(t)}")

    def scaled_at(self, t, const, w):
        while t[0] == "paren":
            t = t[1]
        if t[0] == "bin" and t[1] == "*" and t[2] == ("var", const):
            return self.loss_at(t[3], w)
        return None


def summands(t):
    while t[0] == "paren":
        t = t[1]
    if t[0] == "bin" and t[1] == "+":
        return summands(t[2]) + summands(t[3])
    return [t]


def x_is_context(model, c):
    return c[1][0] == "var" and c[1][1] in model.contexts and c[3] == "call"


# ---------------------------------------------------------------------------------------------------------
# a row of a rule on an instance

def check_row(model, text, inst):
    """holds, fails, vacuous or undecided: ... for the typed row text on the instance inst (a dict of JSON values); a
    row of several clauses (separated by `;`) holds when no clause fails and one holds, each clause read on the same
    instance"""
    try:
        parts = T.parse_qpp_item(text)
    except ValueError as e:
        return f"undecided: {e}"
    if len(parts) != 1:
        res = [check_part(model, q, inst) for q in parts]
        bad = [r for r in res if r.startswith("undecided") or r == "fails"]
        if bad:
            return bad[0]
        return "holds" if "holds" in res else "vacuous"
    return check_part(model, parts[0], inst)


def check_part(model, part, inst):
    """check_row for one clause, parsed"""
    hyps, concl = (flat(part[1]), part[2]) if part[0] == "ctx" else ([], part)
    env = {}
    model.row = inst  # read by an existential whose witness the row gives (Ev.holds)
    ev = Ev(model, env)
    try:
        for c in hyps:
            if c[0] == "decl":
                for v in c[1]:
                    declare(model, env, v, c[2], inst)
                continue
            if bind_context(ev, c):
                continue
            if c[0] == "forall" and len(c[1]) == 1 and c[3][0] == "imp" and c[3][2][0] == "app" \
                    and x_is_context(model, c[3][2]):
                j = c[1][0][1]
                fam = [a for a in c[3][2][2] if a[0] == "app" and a[3] == "idx"]
                ok = True
                for name in {a[1][1] for a in fam}:
                    if not isinstance(env.get(name), dict):
                        raise Undecided(f"the family {name}")
                idx = sorted({i for a in fam for i in env[a[1][1]]})
                for i in idx:
                    sub = Ev(model, {**env, j: i})
                    if not sub.holds(c[3][1]):
                        continue
                    app = c[3][2]
                    tgt = app[2][-1]
                    if tgt[0] == "app" and tgt[3] == "idx" and env[tgt[1][1]].get(i) is None:
                        env[tgt[1][1]][i] = sub.model_pair(app)
                    else:
                        ok = ok and sub.holds(app)
                if not ok:
                    return "vacuous"
                continue
            if not ev.holds(c):
                return "vacuous"
        return "holds" if ev.holds(concl) else "fails"
    except Undecided as e:
        return f"undecided: {e}"


def counter_row(model, text, inst, drop):
    """a row of a counterexample (neqfix) on the model: the hypotheses of the typed row text but the dropped ones (drop:
    their printed Q++) hold on the instance, a dropped one fails, and the conclusion fails ("counterexample"); else what
    the row is instead. A dropped clause that is no hypothesis, or a declaration, is an error (ValueError)."""
    try:
        parts = T.parse_qpp_item(text)
    except ValueError as e:
        return f"undecided: {e}"
    if len(parts) != 1:
        return "undecided: a row `declarations, hypotheses : conclusion`"
    hyps, concl = (flat(parts[0][1]), parts[0][2]) if parts[0][0] == "ctx" else ([], parts[0])
    try:
        texts = {T.to_qpp(c) for x in drop for q in T.parse_qpp_item(x) for c in flat(q)}
    except ValueError as e:
        raise ValueError(f"a dropped clause: {e}")
    missing = texts - {T.to_qpp(c) for c in hyps}
    if missing:
        raise ValueError(f"not a hypothesis of the row: {', '.join(sorted(missing))}")
    if any(c[0] in ("decl", "def") and T.to_qpp(c) in texts for c in hyps):
        raise ValueError("a declaration or a definition is not dropped")
    env = {}
    model.row = inst  # read by an existential whose witness the row gives (Ev.holds)
    ev = Ev(model, env)
    dropped = []
    try:
        for c in hyps:
            if c[0] == "decl":
                for v in c[1]:
                    declare(model, env, v, c[2], inst)
                continue
            if T.to_qpp(c) in texts:
                dropped.append(c)  # evaluated once the kept clauses have bound their names
                continue
            if bind_context(ev, c):
                continue
            if not ev.holds(c):
                return "not a witness: a hypothesis kept fails"
        held = [ev.holds(c) for c in dropped]
        if ev.holds(concl):
            return "the row meets the statement"
        if all(held):
            return "the statement fails at the row: every hypothesis dropped holds"
        return "counterexample"
    except Undecided as e:
        return f"undecided: {e}"


def value_row(model, text, inst):
    """a row of an eqfix fixture on the model: the hypotheses of the typed row text hold on the instance, its
    conclusion is an equation, and every side of it is the value inst["="] ("value"); else what the row is"""
    if "=" not in inst:
        raise ValueError("a row of an eqfix fixture gives the value \"=\"")
    try:
        parts = T.parse_qpp_item(text)
    except ValueError as e:
        return f"undecided: {e}"
    if len(parts) != 1:
        return "undecided: a row `declarations, hypotheses : conclusion`"
    hyps, concl = (flat(parts[0][1]), parts[0][2]) if parts[0][0] == "ctx" else ([], parts[0])
    while concl[0] == "paren":
        concl = concl[1]
    if concl[0] != "rel" or any(op != "=" for op in concl[1]):
        raise ValueError(f"the conclusion {T.to_qpp(concl)} is not an equation")
    env = {}
    model.row = inst  # read by an existential whose witness the row gives (Ev.holds)
    ev = Ev(model, env)
    try:
        for c in hyps:
            if c[0] == "decl":
                for v in c[1]:
                    declare(model, env, v, c[2], {k: x for k, x in inst.items() if k != "="})
                continue
            if bind_context(ev, c):
                continue
            if not ev.holds(c):
                return "not an instance: a hypothesis fails"
        want = rat(inst["="])
        vals = [ev.val(t) for t in concl[2]]
        if all(v == want for v in vals):
            return "value"
        return f"fails: the sides are {', '.join(str(v) for v in vals)}, the value {want}"
    except Undecided as e:
        return f"undecided: {e}"


def run_value(model, item, key, path):
    """(counts {status: n}, bad [(row, status)]) of an eqfix fixture of the rule item on the model: on every row the
    hypotheses hold and every side of the equation of the row key is the value \"=\""""
    d = json.loads(Path(path).read_text(encoding="utf-8"))
    if d.get("kind") != "values":
        return {}, [(None, "an eqfix fixture has kind \"values\"")]
    rows = [r for r in item.stmt_rows() if r.key == key and "?{" not in r.text]
    if not rows:
        return {}, [(None, f"{item.label}: no typed row {key}")]
    counts, bad = {}, []
    try:
        with model.reading(d):
            for inst in d.get("rows", []):
                try:
                    st = value_row(model, row_text(item, rows[0]), inst)
                except ValueError as e:
                    st = f"error: {e}"
                counts[st] = counts.get(st, 0) + 1
                if st != "value":
                    bad.append((inst, st))
    except ValueError as e:
        return {}, [(None, str(e))]
    if not d.get("rows"):
        bad.append((None, "no row"))
    return counts, bad


def run_check(model, item, ann, key, path):
    """the eqfix (a value) or neqfix (a counterexample) fixture of a rule read on the model"""
    return (run_value if ann == "eqfix" else run_counter)(model, item, key, path)


def run_counter(model, item, key, path):
    """(counts {status: n}, bad [(row, status)]) of a neqfix fixture of the cited rule item over a context, on the model:
    every row a counterexample to the row key without the hypotheses "drop" """
    d = json.loads(Path(path).read_text(encoding="utf-8"))
    if d.get("kind") != "counterexample":
        return {}, [(None, "a neqfix fixture has kind \"counterexample\"")]
    drop = d.get("drop")
    drop = [drop] if isinstance(drop, str) else list(drop or [])
    if not drop:
        return {}, [(None, "a counterexample names the hypotheses it drops (\"drop\")")]
    rows = [r for r in item.stmt_rows() if r.key == key and "?{" not in r.text]
    if not rows:
        return {}, [(None, f"{item.label}: no typed row {key}")]
    lost = given_dropped(item, rows[0])
    if lost:
        # a counterexample shows that a hypothesis is needed only if the point meets every other one: a clause with
        # a hole cannot be checked, so the point might violate it
        return {}, [(None, f"a counterexample on a row whose given has clauses with a hole, which the point might "
                           f"violate: {'; '.join(lost)}")]
    counts, bad = {}, []
    try:
        with model.reading(d):
            for inst in d.get("rows", []):
                try:
                    st = counter_row(model, row_text(item, rows[0]), inst, drop)
                except ValueError as e:
                    st = f"error: {e}"
                counts[st] = counts.get(st, 0) + 1
                if st != "counterexample":
                    bad.append((inst, st))
    except ValueError as e:
        return {}, [(None, str(e))]
    if not d.get("rows"):
        bad.append((None, "no row"))
    return counts, bad


def declare(model, env, v, ty, inst):
    kind, dim = model.kind(ty, env)
    if v[0] == "family":
        name = v[1]
        lo, hi = Ev(model, env).val(v[2]), Ev(model, env).val(v[3])
        given = inst.get(name, inst.get(name + "[]"))  # a family as a tuple, by its name or by NAME[]
        if given is None and kind != "pair":
            raise Undecided(f"no value for the family {name}")
        if given is not None and (not isinstance(given, list) or len(given) != hi - lo + 1):
            raise Undecided(f"the family {name}: {int(hi - lo + 1)} members")
        env[name] = {Fr(int(lo) + i): (value_of(kind, dim, g) if given is not None else None)
                     for i, g in enumerate(given if given is not None else [None] * int(hi - lo + 1))}
        return
    name = v[1]
    if name in inst:
        env[name] = value_of(kind, dim, inst[name])
        if kind == "bundle":
            for p, pv in env[name].items():
                env[f"{name}.{p}"] = pv  # the part Pr.P, read as a name
        bound = {("set", "QQ>0"): (lambda x: x > 0), ("set", "QQ>=0"): (lambda x: x >= 0)}.get(ty)
        if ty[0] == "setlist" and all(m[0] == "num" for m in ty[1]):
            bound = lambda x: x in {Fr(m[1]) for m in ty[1]}
        if bound is not None and not bound(env[name]):
            raise Undecided(f"{name} = {env[name]} is not in {T.to_qpp(ty) if ty[0] == 'setlist' else ty[1]}")
    elif kind == "pair":
        env[name] = None  # bound by a context hypothesis
    else:
        raise Undecided(f"no value for {name}")


def value_of(kind, dim, v):
    if kind == "nat":
        if not isinstance(v, int) or v < 0:
            raise Undecided(f"a natural number: {v!r}")
        return Fr(v)
    if kind == "rat":
        return rat(v)
    if kind == "loss" and isinstance(v, dict) and "table" in v:
        return table_of(v, dim, None)
    if kind == "loss":
        return loss_of(v, dim)
    if kind == "table":
        return table_of(v, dim[0], dim[1], points=True)
    if kind == "line":
        return line_of(v)
    if kind == "region":
        return region_of(v, dim)
    if kind == "tuple":
        return tuple_of(v, dim)
    if kind == "tuples":
        if not isinstance(v, list) or (dim[0] is not None and len(v) != dim[0]):
            raise Undecided(f"a tuple of {dim[0]} tuples: {v!r}")
        return tuple(tuple_of(r, dim[1]) for r in v)
    if kind == "pair":
        return pair_of(v)
    if kind == "bundle":
        if not isinstance(v, dict) or set(v) != set(dim):
            raise Undecided(f"a bundle is an object with the parts {', '.join(dim)}: {v!r}")
        return {p: value_of(*dim[p], v[p]) for p in dim}
    raise Undecided(f"a value of kind {kind}")


def bind_context(ev, c):
    """a context hypothesis whose pair is an unbound name: the name is bound to the model's pair; a defined name
    (`x := t`, a clause of a core row) is bound to the value of `t`, as the statement reads it (a value of the instance
    under that name is not read)"""
    if c[0] == "def" and c[1][0] == "var":
        ev.env[c[1][1]] = ev.val(c[2])
        return True
    if not (c[0] == "app" and x_is_context(ev.m, c)):
        return False
    tgt = c[2][-1]
    if tgt[0] == "var" and tgt[1] in ev.env and ev.env[tgt[1]] is None:
        ev.env[tgt[1]] = ev.model_pair(c)
        return True
    return False


# ---------------------------------------------------------------------------------------------------------
# fixtures

def over_context(item, contexts):
    """a cited rule about a context: every typed statement row applies one"""
    import re
    rows = [r for r in item.stmt_rows() if r.key not in ("given", "origin", "names") and "?{" not in r.text]
    return bool(rows) and all(any(re.search(rf"(?<![\w.']){re.escape(c)}\(", r.text) for c in contexts)
                              for r in rows)


def scalar_degree(t, me):
    """the degree of the term t in the number me = ("var", name) when t is a polynomial in it, else None"""
    while t[0] == "paren":
        t = t[1]
    if me not in walk(t):
        return 0
    if t == me:
        return 1
    if t[0] == "bin" and t[1] in ("+", "-"):
        a, b = scalar_degree(t[2], me), scalar_degree(t[3], me)
        return None if a is None or b is None else max(a, b)
    if t[0] == "bin" and t[1] == "*":
        a, b = scalar_degree(t[2], me), scalar_degree(t[3], me)
        return None if a is None or b is None else a + b
    if t[0] == "bin" and t[1] == "/" and me not in walk(t[3]):
        return scalar_degree(t[2], me)
    return None


def poly_degree(t, names):
    """the degree of the term t in the coordinates of the points names (a coordinate x_(i) of degree one, a term
    free of them of degree zero), or None when t is not a polynomial in them: a quotient, a power with an exponent
    other than a numeral, or a bracket, a call or a word that reads them"""
    k = t[0]
    if not (set(names) & {v[1] for v in walk(t) if v[0] == "var"}):
        return 0
    if k == "paren":
        return poly_degree(t[1], names)
    if k == "app" and t[3] == "idx" and t[1][0] == "var" and t[1][1] in names:
        return 1
    if k == "bin" and t[1] in ("+", "-"):
        a, b = poly_degree(t[2], names), poly_degree(t[3], names)
        return None if a is None or b is None else max(a, b)
    if k == "bin" and t[1] == "*":
        a, b = poly_degree(t[2], names), poly_degree(t[3], names)
        return None if a is None or b is None else a + b
    if k == "bin" and t[1] == "/":
        a = poly_degree(t[2], names)
        return a if a is not None and poly_degree(t[3], names) == 0 else None
    if k == "pow" and t[2][0] == "num" and t[2][1].isdigit():
        a = poly_degree(t[1], names)
        return None if a is None else a * int(t[2][1])
    if k == "sum" and len(t) == 4 and t[2] is None:
        return poly_degree(t[3], names)
    return None


def has_prog(item):
    """a rule whose typed statement rows all state the pair of a program (prog(...) = P), read on the model:
    the pair of the program by the exact simplex at the values of the fixture (prog_value); its core rows, which
    only the checks read, are read on the model too"""
    import re
    rows = [r for r in item.stmt_rows() if r.key not in ("given", "origin", "names") and "?{" not in r.text
            and not T.is_core(r.key)]
    return bool(rows) and all(re.search(r"(?<![\w.'])prog\(", r.text) for r in rows)


def states_prog(item):
    """a rule with a typed row, core rows included, that states the pair of a program: the checker of the paper does
    not read prog in a term, so the rule is read on the model, with its other rows (lem:surplus, whose rows are core
    rows, and thm:chain, whose row (loud) is a program)"""
    import re
    return any(re.search(r"(?<![\w.'])prog\(", r.text) for r in item.stmt_rows()
               if r.key not in ("given", "origin", "names") and "?{" not in r.text)


def has_lattice(item):
    """a rule whose typed statement rows read the coordinates of tuples of a type row X^n or the lattice points of
    boxes, evaluated on the model at the values of a fixture: the sums over the coordinates and over the points
    of the box. A sum without a range over the members of a vector `b_x in QQ^k` (no type row) is not one: the checker
    of the modules reads it"""
    trees = []
    for r in item.stmt_rows():
        if r.key in ("origin", "names") or "?{" in r.text:
            continue
        try:
            trees += T.parse_qpp_item(r.text)
        except ValueError:
            continue
    nodes = [y for x in trees for y in walk(x)]
    tuples = {v[1] for c in nodes if c[0] == "decl" and c[2][0] in ("app", "var") for v in c[1]
              if v[0] in ("var", "family")}

    def tuple_term(t):
        # a name of a type row, a member a_(j) of a family of them, a row f_(iota) of a tuple of tuples
        return (t[0] == "var" and t[1] in tuples) or (t[0] == "app" and len(t) == 4 and t[3] == "idx"
                                                     and t[1][0] == "var" and t[1][1] in tuples)

    def indexes_tuple(body, i):
        return any(y[0] == "app" and len(y) == 4 and y[3] == "idx" and y[2] == (("var", i),) and tuple_term(y[1])
                   for y in walk(body))
    for x in nodes:
        if x[0] == "sum" and len(x) == 4 and isinstance(x[2], tuple) and x[2][0] == "le":
            return True
        if x[0] in ("sum", "prod") and len(x) == 4 and x[2] is None and indexes_tuple(x[3], x[1]):
            return True
        if x[0] in ("forall", "exists") and len(x) == 4 and x[2] is None and len(x[1]) == 1 \
                and x[1][0][0] == "var" and indexes_tuple(x[3], x[1][0][1]):
            return True
    return False


def has_bidet(item):
    """a rule whose typed statement rows name a half of the bideterminant, bidetP or bidetM, evaluated on the
    model at the tables of a fixture by Laplace's recursion (bidet)"""
    for r in item.stmt_rows():
        if r.key in ("origin", "names") or "?{" in r.text:
            continue
        try:
            trees = T.parse_qpp_item(r.text)
        except ValueError:
            continue
        if any(y[0] == "app" and len(y) == 4 and y[3] == "call" and y[1] in (("var", "bidetP"), ("var", "bidetM"))
               for x in trees for y in walk(x)):
            return True
    return False


def walk(x):
    """the subtrees of a Q++ tree (tuples), x first"""
    out = []
    if isinstance(x, tuple) and x and isinstance(x[0], str):
        out.append(x)
    if isinstance(x, tuple):
        for y in x:
            out += walk(y)
    return out


def reads_graph(path):
    """whether a fixture file names a relation read as the graph of the model's pair (\"graph\"), so that the rule
    it checks is read on the model whatever its kind"""
    path = Path(path)
    if path.suffix != ".json" or not path.is_file():
        return False
    try:
        return "graph" in json.loads(path.read_text(encoding="utf-8"))
    except (ValueError, TypeError):
        return False


def model_fixtures(item, fixdir):
    """the ids of the fixtures of the item (fix) of the kind model: a rule on functions on the counts (`NN -> QQ>=0`,
    families of them), which the checker of the paper does not read, is read on the model"""
    out = set()
    for _, fid, _ in item.fixes:
        path = Path(fixdir) / f"{fid}.json"
        try:
            if path.is_file() and json.loads(path.read_text(encoding="utf-8")).get("kind") == "model":
                out.add(fid)
        except (ValueError, TypeError, AttributeError):
            continue
    return out


def graph_fixtures(item, fixdir):
    """the ids of the fixtures of the item (fix, eqfix, neqfix) that read a relation as the graph of the pair"""
    ids = [fid for _, fid, _ in item.fixes] + [fid for _, _, fid, _ in item.checks]
    return {fid for fid in ids if reads_graph(Path(fixdir) / f"{fid}.json")}


def on_model(item, contexts):
    """a rule read on the model: a cited rule over a context, a rule on the pairs of programs, or a rule on the
    coordinates of tuples and the lattice points of boxes"""
    return (item.kind == "cit" and bool(contexts) and over_context(item, contexts)) or has_prog(item) or \
        has_lattice(item) or has_bidet(item)


def formal_given(text):
    """(kept, dropped): the clauses of a given without the clauses with a hole (a part between semicolons, or a clause
    between commas in it), joined by commas, and the clauses with a hole: the drop rule of the statements, which
    leave those clauses out"""
    cs = [c.strip() for part in SY.split_top(text, ";") for c in SY.split_top(part, ",")]
    return ", ".join(c for c in cs if c and "?{" not in c), [c for c in cs if "?{" in c]


def given_dropped(item, r):
    """the clauses with a hole that the given of a rule on programs loses on the row r (none for a core row, which
    is read without the given)"""
    g = item.row("given")
    if g is None or not has_prog(item) or T.is_core(r.key):
        return []
    return formal_given(g.text)[1]


def row_text(item, r):
    """the text of a typed row, with the given of a rule on programs as its hypotheses: its formal clauses only, and
    none for a core row, which is read without the given (as the statements read them)"""
    g = item.row("given")
    if g is None or not has_prog(item) or T.is_core(r.key):
        return r.text
    gt = formal_given(g.text)[0]
    if not gt:
        return r.text
    try:
        parts = T.parse_qpp_item(r.text)
    except ValueError:
        return r.text
    return f"{gt}, {r.text}" if len(parts) == 1 and parts[0][0] == "ctx" else f"{gt} : {r.text}"


def run_fixture(model, item, key, path):
    """(kind, counts {status: n}, bad [(row, status)]) of a fixture of the cited rule item (key None: every typed
    row). model: no row fails or is undecided, and some row holds; witness (the kind of the checker of the
    statements, so that a fixture of a row read there is carried as it is): every row holds"""
    d = json.loads(Path(path).read_text(encoding="utf-8"))
    kind = d.get("kind")
    if kind not in ("model", "witness"):
        raise ValueError(f"{Path(path).name}: a fixture of a rule over a context has kind \"model\" or \"witness\"")
    rows = [r for r in item.stmt_rows() if r.key not in ("given", "origin", "names") and "?{" not in r.text
            and (key is None or r.key == key)]
    if not rows:
        raise ValueError(f"{item.label}: no typed row {key}")
    counts, bad = {}, []
    with model.reading(d):
        sts_rows = [(inst, [check_row(model, row_text(item, r), inst) for r in rows]) for inst in d["rows"]]
    for inst, sts in sts_rows:
        st = next((s for s in sts if s == "fails" or s.startswith("undecided")),
                  next((s for s in sts if s != "holds"), "holds"))
        counts[st] = counts.get(st, 0) + 1
        if st == "fails" or st.startswith("undecided") or (kind == "witness" and st != "holds"):
            bad.append((inst, st))
    if not counts.get("holds"):
        bad.append((None, "no row meets the hypotheses and the conclusion"))
    return kind, counts, bad


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 2
    src, fixdir = Path(argv[0]), Path(argv[1])
    expect_fail = "--expect-fail" in argv
    doc = S.read_file(src)
    model = Model(doc.vocab)
    ok, n = True, 0
    for it in doc.items():
        if not on_model(it, model.contexts) and not graph_fixtures(it, fixdir):
            continue
        if not it.fixes and not it.checks and not has_prog(it) and not has_lattice(it) and not has_bidet(it):
            print(f"{it.label}: FAILED a cited rule over a context with no fix line")
            ok = False
        for key, fid, _ in it.fixes:
            n += 1
            path = fixdir / f"{fid}.json"
            if not path.is_file():
                print(f"{fid} ({it.label}): FAILED no file {path}")
                ok = False
                continue
            kind, counts, bad = run_fixture(model, it, key, path)
            undecided = [st for _, st in bad if st.startswith("undecided")]
            if expect_fail:
                # stated wrong: some row fails, and none is undecided (a row the model cannot read refutes nothing)
                good = bool(counts.get("fails")) and not undecided
                verdict = "fails, as expected" if good else f"FAILED: {undecided[:2] or 'no row fails'}"
            else:
                good = not bad
                verdict = "OK" if good else "FAILED " + str(bad[:2])
            print(f"{fid} ({it.label} {key or 'all'}, {kind}): {counts} {verdict}")
            ok = ok and good
        for ann, key, fid, _ in it.checks:
            # a counterexample (neqfix): the rule without the hypotheses dropped fails on the model
            n += 1
            path = fixdir / f"{fid}.json"
            if not path.is_file():
                counts, bad = {}, [(None, f"no file {path}")]
            else:
                counts, bad = run_check(model, it, ann, key, path)
            print(f"{fid} ({it.label} {key}, {ann}): {counts} " + ("OK" if not bad else f"FAILED {bad[:2]}"))
            ok = ok and not bad
    if not n:
        print(f"qpp.ctxmodel: {src}: no fix line of a cited rule over a context")
        return 1
    print(f"qpp.ctxmodel: {src}: {n} fixtures, {'OK' if ok else 'FAILED'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
