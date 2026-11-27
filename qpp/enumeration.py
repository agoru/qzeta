"""The switch that keeps the fixture checkers from enumerating.

A fixture check reads a row at the numbers of its fixture. It enumerates when it decides a clause or a term by
visiting the points of a set of candidates: the lattice points of a box (`sum u <= b`, a quantifier over NN^n bounded
by a box), the numbers up to a bound (a quantifier over NN read on 0..t, an existential over NN), the points of a
grid or the sample points over Q, the vertices of a polyhedron by the bases of its constraints, the permutations of a
table. One universal number or point that occurs as an index of a family of the row or as the argument of a function
that the fixture gives by its values (`forall j in NN>=1 : j + 1 <= N => a_(j) <= b_(j + 1)`, `forall x in NN : x < d
=> P(x) = Q(x)` with P and Q lists of values) runs over the positions of that data: visiting them reads the data the
fixture gives once, and is no enumeration. A second such number or point inside the first is one more index of the
same entry when one entry of the data holds both (`W_(p)(q)`, `P_(j)(x)`: the entries of a family of families), and
makes pairs of positions when none does (`forall u : forall v : u < v => ... A_(u)_(i) * A_(v)_(i)`, a sum over a box
of `f(u) * g(w)` inside a sum over another): pairs of positions are an enumeration. An existential number over the
positions of data reads them as the universal does, being the negation of a universal over the same positions.
Pairs u < v of positions that meet, `1 <= (sum l, A_(u)_(l) * A_(v)_(l))` with natural numbers, meet at a coordinate:
a clause on them whose other parts each read u or v (or `forall i : A_(u)_(i) <= A_(v)_(i)`, read at the first later
position that meets u, by transitivity) is read through the last position at each coordinate: each position once.
An equation of affine forms in the coordinates of the points (`forall x in Exponent(n) : sum a, nu_(i)_(a) * (sum b,
D_(a)_(b) * x_(b)) = x_(i)`) is read by its coefficients, at the point 0 and at each unit point: no enumeration.
A number that an equation of the clause fixes (`forall s in NN : s = t => P(s)`, `exists t in NN : kappa + t = k2,
P(t)`, with t and k2 free of the number) is read at that one number: no enumeration.
A sum over a box of a product of factors that each read one point (`sum w <= b2, (sum u <= b1, f(u) * g(w))`), or of a
product over the coordinates that reads the points by their coordinates (`sum v <= b, prod i, h(v_(i))`, and boxes
nested in boxes), is the product of the sums of its parts (Fubini): each part is read on its own, and a geometric
series over the numbers that affine relations leave is read in closed form.
A clause over two points whose premise is their boxes and equations linear in u - w, with the conclusion u = w
(`forall u, w : (boxes), D(u) = D(w) => forall i : u_(i) = w_(i)`), holds when the map D read from the coefficients
has full rank: no enumeration.
A relation over two points whose terms each read one point (`forall t, t2 : (boxes) => a * t_(i) <= a * t2_(i) + 2^N *
(f(t) + f(t2))`) holds for every pair if and only if the largest value of the terms of each point does: each point
is read on its own.
An existential over NN whose body is a conjunction of relations affine in its number (`exists t in NN : L <= q * t,
q * t <= L + q`) is read at the least number above the lower bounds that the relations give (a ceiling): no enumeration.

While ENUMERATE is False (qpp.modfix sets it so), each of these places raises Enumerates instead of enumerating, and
the driver reports the fixture as one whose check enumerates; the readers of a clause never catch it (it is a
BaseException), so it is never read as an undecided or a failed clause.
"""

ENUMERATE = True


class Enumerates(BaseException):
    """the check of a fixture reached an enumeration while ENUMERATE is False; the argument says which one"""


def enumerating(what):
    """the place where a check starts to visit the points of a set: refused while ENUMERATE is False"""
    if not ENUMERATE:
        raise Enumerates(what)


def _strip(x):
    while isinstance(x, tuple) and x and x[0] == "paren":
        x = x[1]
    return x


def _parts(g):
    out, stack = [], [g]
    while stack:
        y = _strip(stack.pop())
        if isinstance(y, tuple) and y and y[0] == "and":
            stack += list(y[1])
        else:
            out.append(y)
    return out


def index_only(body, name):
    """whether the number `name` of a universal clause runs over the positions of a family of the row: the premise
    bounds it (`name <= t`, `name + 1 <= t`, `1 <= name`, with t free of it), and it occurs in the index of a family
    (x_(name), x_(name + 1)). Visiting these positions reads the data the fixture gives; it is no enumeration"""
    me = ("var", name)

    def free(t):
        return me not in walk(t)

    def shift(t):
        t = _strip(t)
        return t == me or (isinstance(t, tuple) and len(t) == 4 and t[0] == "bin" and t[1] in ("+", "-")
                           and ((_strip(t[2]) == me and free(t[3])) or (t[1] == "+" and _strip(t[3]) == me
                                                                         and free(t[2]))))

    def bound(c):
        c = _strip(c)
        if not (isinstance(c, tuple) and c and c[0] == "rel" and all(op in ("<=", "<", ">=", ">") for op in c[1])):
            return False
        terms = c[2]
        return any(shift(t) for t in terms) and all(shift(t) or free(t) for t in terms)

    def indexed(x):
        if not isinstance(x, tuple):
            return False
        if len(x) == 4 and x[0] == "app" and x[3] == "idx" and any(me in walk(y) for y in x[2]):
            return True
        return any(indexed(y) for y in x)

    body = _strip(body)
    if not (isinstance(body, tuple) and body and body[0] in ("imp", "ctx") and len(body) == 3):
        return False
    return any(bound(g) for g in _parts(body[1])) and indexed(body)


def walk(x):
    """the subterms of x"""
    out, stack = [], [x]
    while stack:
        y = stack.pop()
        out.append(y)
        if isinstance(y, tuple):
            stack += [z for z in y if isinstance(z, tuple)]
    return out
