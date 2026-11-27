"""Exact linear algebra and linear programming over Q (fact:elim): Gauss, ranks and kernels, an exact two-phase
simplex with Bland's rule that returns an optimal point and its multipliers or a Farkas certificate, the implicit
equalities and the extreme rays of small polyhedra, lattice points by branch and bound, and lattice bases of
subspaces (Hermite normal form, for lem:normalize).

A polyhedron is given by rows: ge = [(a, b)] for a.x >= b and eq = [(a, b)] for a.x = b, a a list of rationals.
"""
from fractions import Fraction
from itertools import combinations
from math import floor, ceil, gcd

F = Fraction


def dot(a, x):
    return sum((F(u) * F(v) for u, v in zip(a, x)), F(0))


# ---------------------------------------------------------------- Gauss

def rref(M):
    """(reduced row echelon form, pivot columns) of a list of rational rows"""
    A = [[F(c) for c in r] for r in M]
    if not A:
        return A, []
    m, n = len(A), len(A[0])
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == m:
            break
    return A, piv


def rank(rows):
    rows = [r for r in rows]
    if not rows:
        return 0
    return len(rref(rows)[1])


def kernel(rows, n):
    """a basis of {x in Q^n: r.x = 0 for every row r}"""
    if not rows:
        return [[F(int(i == j)) for j in range(n)] for i in range(n)]
    A, piv = rref(rows)
    free = [c for c in range(n) if c not in piv]
    out = []
    for f in free:
        v = [F(0)] * n
        v[f] = F(1)
        for i, c in enumerate(piv):
            v[c] = -A[i][f]
        out.append(v)
    return out


def solve(A, b):
    """the unique solution x of A x = b (A square, nonsingular), or None"""
    n = len(A)
    M = [list(map(F, row)) + [F(bb)] for row, bb in zip(A, b)]
    R, piv = rref(M)
    if len(piv) < n or piv[-1] == n:
        return None
    return [R[i][n] for i in range(n)]


def combination(h, basis):
    """c with sum_b c_b basis_b = h, or None"""
    n = len(h)
    nb = len(basis)
    M = [[F(basis[b][i]) for b in range(nb)] + [F(h[i])] for i in range(n)]
    R, piv = rref(M)
    if nb in piv:
        return None
    sol = [F(0)] * nb
    for i, c in enumerate(piv):
        sol[c] = R[i][nb]
    return sol


# ---------------------------------------------------------------- the simplex

class LPResult:
    def __init__(self, status, x=None, value=None, y_ge=None, y_eq=None, farkas=None, ray=None):
        self.status, self.x, self.value = status, x, value
        self.y_ge, self.y_eq, self.farkas, self.ray = y_ge, y_eq, farkas, ray

    def __repr__(self):
        return 'LPResult(%s, value=%s)' % (self.status, self.value)


class Polyhedron:
    """the polyhedron {a.x >= b (ge), a.x = b (eq)}, x free in Q^k, after phase one of the two-phase simplex with
    Bland's rule: phase one does not read the cost, so its tableau serves every cost on the polyhedron, and
    minimize(c) runs phase two on a copy of it. Polyhedron(ge, eq, k).minimize(c) is lp_min(c, ge, eq, k), pivot for
    pivot."""

    def __init__(self, ge=(), eq=(), k=0):
        ge, eq = list(ge), list(eq)
        self.k = k
        rows = [(list(map(F, a)), F(b), 'ge') for a, b in ge] + [(list(map(F, a)), F(b), 'eq') for a, b in eq]
        self.rows = rows
        m = self.m = len(rows)
        ns = self.ns = sum(1 for r in rows if r[2] == 'ge')
        # columns: x+ (k), x- (k), slacks (ns), artificials (m)
        N = self.N = 2 * k + ns + m
        T = []
        sgn = self.sgn = []
        si = 0
        for i, (a, b, kind) in enumerate(rows):
            row = a + [-v for v in a] + [F(0)] * ns + [F(0)] * m
            if kind == 'ge':
                row[2 * k + si] = F(-1)
                si += 1
            s = 1 if b >= 0 else -1
            row = [v * s for v in row]
            row[2 * k + ns + i] = F(1)
            T.append(row + [b * s])
            sgn.append(s)
        basis = [2 * k + ns + i for i in range(m)]
        art = self.art = set(basis)
        cost1 = [F(0)] * (2 * k + ns) + [F(1)] * m
        self._run(T, basis, cost1, lambda j: True)
        w = sum(T[i][N] for i in range(m) if basis[i] in art)
        self.farkas = None
        if w > 0:
            y = self._duals(T, basis, cost1)
            self.farkas = self._split([yi * s for yi, s in zip(y, sgn)])
            return
        # drive artificials out of the basis where possible
        for r in range(m):
            if basis[r] in art:
                col = next((j for j in range(2 * k + ns) if T[r][j] != 0), None)
                if col is not None:
                    self._pivot(T, basis, r, col)
        self.T, self.basis = T, basis

    def _pivot(self, T, basis, r, col, red=None):
        pv = T[r][col]
        Tr = T[r] = [v / pv if v else v for v in T[r]]
        nz = [j for j, v in enumerate(Tr) if v]  # the columns the pivot row changes: the others stay as they are
        for i in range(len(T)):
            Ti = T[i]
            f = Ti[col]
            if i != r and f != 0:
                for j in nz:
                    Ti[j] = Ti[j] - f * Tr[j]
        if red is not None:
            # the reduced costs are one more row of the tableau: the pivot updates them as it updates the rows
            f = red[col]
            if f != 0:
                N = len(red)
                for j in nz:
                    if j < N:
                        red[j] = red[j] - f * Tr[j]
        basis[r] = col

    def _run(self, T, basis, cost, allowed):
        m, N = self.m, self.N
        # the reduced costs cost_j - sum_i cost_(basis_i) T_ij, read once and then kept by each pivot (exact, so the
        # entering column of Bland's rule is the one that a reading afresh at each iteration gives)
        red = list(cost[:N])
        for i, b in enumerate(basis):
            c = cost[b]
            if c:
                Ti = T[i]
                for j in range(N):
                    if Ti[j]:
                        red[j] = red[j] - c * Ti[j]
        while True:
            inbasis = set(basis)
            enter = None
            for j in range(N):
                if red[j] < 0 and j not in inbasis and allowed(j):
                    enter = j
                    break
            if enter is None:
                return 'optimal', None
            best, leave = None, None
            for i in range(m):
                if T[i][enter] > 0:
                    ratio = T[i][N] / T[i][enter]
                    if best is None or ratio < best or (ratio == best and basis[i] < basis[leave]):
                        best, leave = ratio, i
            if leave is None:
                return 'unbounded', enter
            self._pivot(T, basis, leave, enter, red)

    def _duals(self, T, basis, cost):
        k, ns, m = self.k, self.ns, self.m
        cb = [cost[j] for j in basis]
        # y_i = cost of artificial i minus its reduced cost, = sum_r cb_r T[r][art_i]
        return [sum(cb[r] * T[r][2 * k + ns + i] for r in range(m)) for i in range(m)]

    def _split(self, y):
        rows = self.rows
        return ([y[i] for i in range(self.m) if rows[i][2] == 'ge'],
                [y[i] for i in range(self.m) if rows[i][2] == 'eq'])

    def minimize(self, c):
        """lp_min(c, ge, eq, k) on this polyhedron"""
        if self.farkas is not None:
            return LPResult('infeasible', farkas=self.farkas)
        k, ns, m, N, art = self.k, self.ns, self.m, self.N, self.art
        T, basis = [row[:] for row in self.T], self.basis[:]
        cost2 = [F(v) for v in c] + [-F(v) for v in c] + [F(0)] * ns + [F(0)] * m
        status, enter = self._run(T, basis, cost2, lambda j: j not in art)
        if status == 'unbounded':
            ray = [F(0)] * N
            ray[enter] = F(1)
            for i in range(m):
                ray[basis[i]] = -T[i][enter]
            d = [ray[j] - ray[k + j] for j in range(k)]
            return LPResult('unbounded', ray=d)
        z = [F(0)] * N
        for i in range(m):
            z[basis[i]] = T[i][N]
        x = [z[j] - z[k + j] for j in range(k)]
        y = self._duals(T, basis, cost2)
        yg, ye = self._split([yi * s for yi, s in zip(y, self.sgn)])
        return LPResult('optimal', x=x, value=dot(c, x), y_ge=yg, y_eq=ye)

    def maximize(self, c):
        """lp_max(c, ge, eq, k) on this polyhedron"""
        r = self.minimize([-F(v) for v in c])
        if r.status == 'optimal':
            r.value = -r.value
        return r


def lp_min(c, ge=(), eq=(), k=None):
    """minimize c.x over {a.x >= b (ge), a.x = b (eq)}, x free in Q^k. Returns an LPResult: 'optimal' with x,
    value and multipliers y_ge >= 0, y_eq with sum y a = c and sum y b = value (strong duality, fact:elim (2));
    'infeasible' with farkas = (y_ge >= 0, y_eq): sum y a = 0, sum y b > 0; or 'unbounded' with a ray"""
    if k is None:
        k = len(c)
    return Polyhedron(ge, eq, k).minimize(c)


def check_optimal(c, ge, eq, x, y_ge, y_eq):
    """the certificate of an optimum (fact:elim (2)): x feasible, y_ge >= 0, sum y a = c, sum y b = c.x"""
    k = len(c)
    if any(dot(a, x) < F(b) for a, b in ge) or any(dot(a, x) != F(b) for a, b in eq):
        return False
    if any(F(v) < 0 for v in y_ge):
        return False
    comb = [sum((F(y) * F(a[j]) for y, (a, _) in zip(list(y_ge) + list(y_eq), list(ge) + list(eq))), F(0))
            for j in range(k)]
    if comb != [F(v) for v in c]:
        return False
    return sum((F(y) * F(b) for y, (_, b) in zip(list(y_ge) + list(y_eq), list(ge) + list(eq))), F(0)) == dot(c, x)


def check_farkas(ge, eq, y_ge, y_eq, k):
    """{a.x >= b, a.x = b} is empty: y_ge >= 0, sum y a = 0, sum y b > 0 (fact:elim (1))"""
    if any(F(v) < 0 for v in y_ge):
        return False
    rows = list(ge) + list(eq)
    ys = list(y_ge) + list(y_eq)
    if any(sum((F(y) * F(a[j]) for y, (a, _) in zip(ys, rows)), F(0)) != 0 for j in range(k)):
        return False
    return sum((F(y) * F(b) for y, (_, b) in zip(ys, rows)), F(0)) > 0


def feasible(ge, eq, k):
    r = lp_min([0] * k, ge, eq, k)
    return r.x if r.status == 'optimal' else None


def lp_max(c, ge, eq, k):
    r = lp_min([-F(v) for v in c], ge, eq, k)
    if r.status == 'optimal':
        r.value = -r.value
    return r


# ---------------------------------------------------------------- faces, rays, lattice points

def implicit_equalities(ge, eq, k):
    """the indices of the ge rows that hold with equality on the whole (nonempty) polyhedron"""
    out = []
    for i, (a, b) in enumerate(ge):
        r = lp_max(a, ge, eq, k)
        if r.status == 'optimal' and r.value == F(b):
            out.append(i)
    return out


def dimension(ge, eq, k):
    """the dimension of a nonempty polyhedron"""
    imp = implicit_equalities(ge, eq, k)
    return k - rank([a for a, _ in eq] + [ge[i][0] for i in imp])


def cone_rays(ge, eq, k):
    """the extreme rays (primitive integer vectors) of the pointed cone {a.x >= 0, e.x = 0}"""
    rows = [list(map(F, a)) for a, _ in ge]
    eqs = [list(map(F, a)) for a, _ in eq]
    base = rank(eqs)
    need = k - 1 - base
    if need < 0:
        return []
    out = []
    seen = set()
    for S in combinations(range(len(rows)), need) if need > 0 else [()]:
        sub = eqs + [rows[i] for i in S]
        if rank(sub) != k - 1:
            continue
        ker = kernel(sub, k)
        if len(ker) != 1:
            continue
        v = ker[0]
        for s in (1, -1):
            d = [s * x for x in v]
            if all(dot(a, d) >= 0 for a in rows):
                p = primitive_int(d)
                if tuple(p) not in seen:
                    seen.add(tuple(p))
                    out.append(p)
    return out


def primitive_int(v):
    den = 1
    for x in v:
        den = den * F(x).denominator // gcd(den, F(x).denominator)
    w = [int(F(x) * den) for x in v]
    g = 0
    for x in w:
        g = gcd(g, abs(x))
    return [F(x // g) for x in w] if g else [F(0)] * len(v)


class SearchIncomplete(ArithmeticError):
    """the branch and bound of integer_point reached its depth with no lattice point found: the polyhedron is not
    shown to have none"""


def integer_point(ge, eq, k, obj=None, depth=60, tree=False):
    """a lattice point of the polyhedron, by branch and bound with exact LPs, or None when the polyhedron has none.

    Each node solves the LP of obj (the zero form where obj is unbounded below on the node) and returns its optimum
    if it is integral; else it branches on the first fractional coordinate t of the optimum, x_j <= floor t or
    x_j >= ceil t, which splits the lattice points of the node between the two children (the child x_j >= ceil t
    first). None is returned only when every branch ends in an infeasible LP, which proves that the polyhedron has
    no lattice point; with tree=True the pair (point, None) or (None, the branching tree) is returned, the tree a
    certificate of none (con:nolattice, check_tree): a leaf {'farkas': [y_ge, y_eq]} certifies the emptiness of its
    node (Farkas, over the rows of the node: those of the polyhedron, then the branch rows of the path), an inner
    node {'var': j, 'c': c, 'le': ..., 'ge': ...} has the children x_j <= c and x_j >= c + 1. When no lattice point
    is found and a branch was cut at the depth, SearchIncomplete is raised: the search then proves nothing."""
    obj = obj if obj is not None else [F(0)] * k
    zero = [F(0)] * k
    cut = [False]

    def node(g, e, d):
        r = lp_min(obj, g, e, k)
        if r.status == 'unbounded':  # the node is not empty: search it with the zero form
            r = lp_min(zero, g, e, k)
        if r.status == 'infeasible':
            return None, dict(farkas=[list(r.farkas[0]), list(r.farkas[1])])
        x = r.x
        frac = next((j for j in range(k) if x[j].denominator != 1), None)
        if frac is None:
            return [F(v) for v in x], None
        if d >= depth:
            cut[0] = True
            return None, None
        lo, hi = floor(x[frac]), ceil(x[frac])
        unit = [F(int(j == frac)) for j in range(k)]
        pt, t_hi = node(g + [(unit, F(hi))], e, d + 1)
        if pt is not None:
            return pt, None
        pt, t_lo = node(g + [([-u for u in unit], F(-lo))], e, d + 1)
        if pt is not None:
            return pt, None
        if t_hi is None or t_lo is None:
            return None, None
        return None, {'var': frac, 'c': F(lo), 'le': t_lo, 'ge': t_hi}

    pt, t = node(list(ge), list(eq), 0)
    if pt is None and cut[0]:
        raise SearchIncomplete('the lattice-point search did not finish at depth %d' % depth)
    return (pt, t) if tree else pt


def check_tree(t, ge, eq, k):
    """con:nolattice: the branching tree t certifies that {a.x >= b (ge), a.x = b (eq)} has no lattice point: every
    leaf's multipliers certify the emptiness of its node (check_farkas over the node's rows), and every inner node
    branches on x_j <= c or x_j >= c + 1 with c an integer, which partitions the lattice points of the node"""
    if not isinstance(t, dict):
        return False
    if 'farkas' in t:
        y_ge, y_eq = t['farkas']
        return len(y_ge) == len(ge) and len(y_eq) == len(eq) and check_farkas(ge, eq, y_ge, y_eq, k)
    j, c = t.get('var'), F(t.get('c', F(1, 2)))
    if not (isinstance(j, int) and 0 <= j < k) or c.denominator != 1:
        return False
    unit = [F(int(i == j)) for i in range(k)]
    return (check_tree(t.get('le'), list(ge) + [([-u for u in unit], -c)], eq, k)
            and check_tree(t.get('ge'), list(ge) + [(unit, c + 1)], eq, k))


# ---------------------------------------------------------------- lattices (lem:normalize)

def hnf_rows(M):
    """the Hermite normal form (row style) of an integer matrix, with the unimodular transform: (H, U), H = U M"""
    A = [list(map(int, r)) for r in M]
    m = len(A)
    n = len(A[0]) if A else 0
    U = [[int(i == j) for j in range(m)] for i in range(m)]
    r = 0
    for c in range(n):
        # gcd elimination on column c among rows r..m-1
        while True:
            nz = [i for i in range(r, m) if A[i][c] != 0]
            if not nz:
                break
            p = min(nz, key=lambda i: abs(A[i][c]))
            A[r], A[p] = A[p], A[r]
            U[r], U[p] = U[p], U[r]
            done = True
            for i in range(r + 1, m):
                if A[i][c]:
                    q = A[i][c] // A[r][c]
                    A[i] = [x - q * y for x, y in zip(A[i], A[r])]
                    U[i] = [x - q * y for x, y in zip(U[i], U[r])]
                    if A[i][c]:
                        done = False
            if done:
                break
        if r < m and A[r][c] != 0:
            if A[r][c] < 0:
                A[r] = [-x for x in A[r]]
                U[r] = [-x for x in U[r]]
            r += 1
        if r == m:
            break
    return A, U


def lattice_basis_of_kernel(rows, n):
    """an integer basis of Z^n intersected with {x: r.x = 0}, extended by integer vectors to a basis of Z^n:
    (kernel basis, complement), by the column Hermite form of the rows"""
    rows = [primitive_int(r) for r in rows if any(F(x) != 0 for x in r)]
    if not rows:
        return [[F(int(i == j)) for j in range(n)] for i in range(n)], []
    # column operations on M (rows x n) = row operations on M^T
    MT = [[int(rows[i][j]) for i in range(len(rows))] for j in range(n)]
    H, U = hnf_rows(MT)  # H = U M^T, so M U^T has columns ... ; columns of U^T are the new basis of Z^n
    rk = sum(1 for r in H if any(r))
    basis = [list(map(F, U[i])) for i in range(n)]
    # rows of H that vanish correspond to basis vectors in the kernel
    ker = [basis[i] for i in range(n) if not any(H[i])]
    comp = [basis[i] for i in range(n) if any(H[i])]
    assert len(ker) == n - rk
    return ker, comp
