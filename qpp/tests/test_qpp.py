r"""test_qpp: the checker of fixtures, run here on the .qpp files of qpp/tests/fixtures. Every `fix` line of a .qpp
file (the \FIX{id} of its LaTeX) names a fixture, <id>.json (rows) or <id>.py (an algorithm in the standard library
that yields rows) next to the file, and the rows are checked on the statement of the .qpp, in exact rational
arithmetic.

A row binds the names that a result declares (scalars by name, a family a_1,...,a_N under "a[]" as a list from its
first index or as a dict index -> value); check() then evaluates the context `given` and each conclusion item on the
row:

    holds      every context clause is true and the conclusion is true
    fails      every context clause is true and the conclusion is false
    vacuous    a context clause is false (the row is not an instance)
    undecided  the evaluation needs something this reader does not decide (the reason is given)

The fragment that is decided: arithmetic over Q (an exponent must be an integer), sums over families and index ranges,
chains, membership in Q, Z, N with bounds, intervals and words, and quantifiers over the range of a family. Defined
relations and relational words are expanded as for Lean. A quantifier over Z_{>=c} is evaluated on c..b when the
fixture gives a bound b for its variable, and the result says so ("bounded"); a quantifier over Q, Q_{>0}, ... on
the sample points the fixture gives as a list for its variable ("sampled"); without them it is undecided.

    python3 qpp/tests/test_qpp.py qpp/tests/fixtures/a_slice.qpp qpp/tests/fixtures   (one file, verbose)
"""
import json
import math
import runpy
import sys
from fractions import Fraction
from pathlib import Path

import pytest

if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))  # run as a script from anywhere

from qpp import enumeration as EN  # noqa: E402
from qpp import qpp2lean as Q  # noqa: E402
from qpp import texmath as T  # noqa: E402


class Undecided(Exception):
    pass


SET_TYPES = {"QQ": "\u211a", "ZZ": "\u2124", "NN": "\u2115"}


class Box:
    """the interval [lo, hi] of numbers or of vectors (componentwise), closed unless an end is open ((lo, hi] when
    open_lo)"""

    def __init__(self, lo, hi, open_lo=False, open_hi=False):
        self.lo, self.hi, self.open_lo, self.open_hi = lo, hi, open_lo, open_hi

    def __eq__(self, other):
        return isinstance(other, Box) and (self.lo, self.hi, self.open_lo, self.open_hi) == (
            other.lo, other.hi, other.open_lo, other.open_hi)

    def __hash__(self):
        return hash((self.lo, self.hi, self.open_lo, self.open_hi))

    def __contains__(self, v):
        return le(self.lo, v, self.open_lo) and le(v, self.hi, self.open_hi)

    def __repr__(self):
        return f"Box({self.lo}, {self.hi})" if not (self.open_lo or self.open_hi) else \
            f"Box({'(' if self.open_lo else '['}{self.lo}, {self.hi}{')' if self.open_hi else ']'})"


def le(a, b, strict=False):
    """a <= b (a < b if strict) in every component for vectors; a number against a vector is compared with each
    component"""
    if isinstance(a, tuple) or isinstance(b, tuple):
        if isinstance(a, tuple) and isinstance(b, tuple) and len(a) != len(b):
            raise Undecided("an order between vectors of two lengths")
        n = len(a) if isinstance(a, tuple) else len(b)
        a, b = (a if isinstance(a, tuple) else (a,) * n), (b if isinstance(b, tuple) else (b,) * n)
        return all(x < y if strict else x <= y for x, y in zip(a, b))
    return a < b if strict else a <= b


def compare(op, a, b):
    """the order links of Q++: on vectors, a <= b and a < b hold in every component (a < b is strict in every
    component, which is not Lean's a <= b and a != b; qpp2lean writes it out)"""
    vec = isinstance(a, tuple) or isinstance(b, tuple)
    if op == "=":
        return le(a, b) and le(b, a) if vec else a == b
    if op == "!=":
        if vec and not (isinstance(a, tuple) and isinstance(b, tuple)) and 0 not in (a, b):
            raise Undecided("a vector unequal to a number other than 0")
        return not (le(a, b) and le(b, a)) if vec else a != b
    if op in (">=", ">"):
        a, b, op = b, a, {">=": "<=", ">": "<"}[op]
    if op in ("<=", "<"):
        return le(a, b, strict=op == "<")
    if op in ("subseteq", "subset"):
        sub = subset(a, b)
        return sub if op == "subseteq" else sub and not subset(b, a)
    if op in ("divides", "ndivides"):
        # a | b on integers (as Lean reads it, in Z): b = c a for an integer c; 0 | b only for b = 0
        if vec or not all(isinstance(t, (int, Fraction)) and Fraction(t).denominator == 1 for t in (a, b)):
            raise Undecided("divisibility of terms that are not integers")
        d = (b == 0) if a == 0 else Fraction(b) % Fraction(a) == 0
        return d if op == "divides" else not d
    raise Undecided(f"the relation {op}")


def subset(a, b):
    """a is a subset of b, for finite sets and boxes"""
    if isinstance(a, frozenset):
        return all(contains(b, v) for v in a)
    if isinstance(a, Box) and isinstance(b, Box):
        if not le(a.lo, a.hi, a.open_lo or a.open_hi):
            return True  # a is empty
        # an open end of b holds an end of a when a's end is strictly inside, or open at the same bound
        lo = le(b.lo, a.lo, b.open_lo and not a.open_lo)
        hi = le(a.hi, b.hi, b.open_hi and not a.open_hi)
        return lo and hi
    if isinstance(a, Box) and isinstance(b, frozenset):
        if not le(a.lo, a.hi):
            return True
        if a.lo == a.hi:
            return a.lo in b
        return False  # a box with two points is infinite
    raise Undecided("a subset relation between these sets")


def contains(S, v):
    if isinstance(S, (Box, frozenset)):
        return v in S
    raise Undecided("membership in a set that is not a box or a finite set")


def arith(op, a, b):
    """+, -, * on numbers and vectors (componentwise; a number times a vector)"""
    va, vb = isinstance(a, tuple), isinstance(b, tuple)
    if not va and not vb:
        return a + b if op == "+" else a - b if op == "-" else a * b
    if op == "*" and va != vb:
        c, v = (a, b) if vb else (b, a)
        return tuple(c * x for x in v)
    if va and vb and len(a) == len(b) and op in "+-":
        return tuple(x + y if op == "+" else x - y for x, y in zip(a, b))
    raise Undecided(f"{op} between these values")


def num(v):
    """a row value: an int, or a string of a rational ("3/2"); a float is refused (it is not exact)"""
    if isinstance(v, bool) or not isinstance(v, (int, str, Fraction)):
        raise ValueError(f"the row value {v!r}: an int or a string of a rational")
    return Fraction(v)


class Env:
    """values (scalars by name, families under name[] as dicts index -> value), family ranges, the types that the
    expansion of defined relations reads, and the bounds of unbounded quantifiers"""

    def __init__(self, vocab, row, bounds, parent=None):
        self.vocab, self.row, self.bounds = vocab, row, bounds
        self.vals = dict(parent.vals) if parent else {}
        self.fams = dict(parent.fams) if parent else {}
        self.types = Q.Env(vocab, parent.types if parent else None)
        self.flags = parent.flags if parent else set()

    def child(self):
        return Env(self.vocab, self.row, self.bounds, self)


# ---------------------------------------------------------------- terms

def value(x, env):
    k = x[0]
    if k == "num":
        return Fraction(x[1])
    if k == "var":
        if x[1] not in env.vals:
            raise Undecided(f"no value for {x[1]}")
        return env.vals[x[1]]
    if k == "app" and x[3] == "idx" and x[1][0] == "var":
        fam = env.vals.get(Q.seq_key(x[1][1]))
        vec = env.vals.get("b_" + x[1][1])
        if fam is None and isinstance(vec, tuple) and len(x[2]) == 1:
            # the component x_i of the vector b_x, numbered from 1
            i = int(index(x[2][0], env))
            if not 1 <= i <= len(vec):
                raise Undecided(f"the component {x[1][1]}_{i} of a vector of dimension {len(vec)}")
            return vec[i - 1]
        if fam is None:
            raise Undecided(f"no values for the family {x[1][1]}")
        idx = tuple(int(index(i, env)) for i in x[2])
        if callable(fam):
            return as_value(fam(*idx))  # a family the given defines (sigma_(a, b) := E)
        i = idx[0] if len(idx) == 1 else idx
        if i not in fam:
            raise Undecided(f"no value for {x[1][1]}_{i} (the row gives {x[1][1]} at {sorted(fam)}; a list starts "
                            f"at 1, a dict {{\"0\": ...}} gives other indices)")
        return fam[i]
    if k == "neg":
        v = value(x[1], env)
        return tuple(-c for c in v) if isinstance(v, tuple) else -v
    if k == "app" and x[1] == ("var", "card") and len(x[2]) == 1:
        return Fraction(len(elements(x[2][0], env)))
    if k == "app" and x[3] == "call" and x[1] in (("var", "min"), ("var", "max")) and len(x[2]) >= 2:
        vals = [value(a, env) for a in x[2]]  # min(a, b), max(x - t, 0): the positive part (x - t)_+
        return min(vals) if x[1][1] == "min" else max(vals)
    if k == "iverson":
        return Fraction(1 if prop(x[1], env) else 0)  # \mathbf 1[P]
    if k == "app" and x[3] == "call" and x[1] == ("var", "choose") and len(x[2]) == 2:
        n, r = index(x[2][0], env), index(x[2][1], env)
        if n < 0 or r < 0:
            raise Undecided("a binomial coefficient of a negative number")
        return Fraction(math.comb(int(n), int(r)))  # Nat.choose: 0 when r > n
    if k == "app" and x[3] == "call" and x[1][0] == "var":
        f = env.vals.get(x[1][1])
        if not callable(f):
            raise Undecided(f"no function {x[1][1]} (a function is given by a .py fixture)")
        args = [value(a, env) for a in x[2]]
        return as_value(f(*args))
    if k == "interval" and x[3] is None:
        return Box(value(x[1], env), value(x[2], env))
    if k == "ivl":
        return Box(value(x[2], env), value(x[3], env), open_lo=x[1] == "oc", open_hi=x[1] == "co")
    if k == "setof" and x[1][0] in ("var", "app", "tuple", "num") and not T.is_prop(x[1]):
        return frozenset({value(x[1], env)})
    if k in ("setlist", "intrange") or (k == "setof" and x[1][0] == "such"):
        return elements(x, env)
    if k == "least":
        S = elements(x[2], env)
        if not S:
            raise Undecided(f"the {x[1]} of an empty set")
        return min(S) if x[1] == "min" else max(S)
    if k == "tuple":
        return tuple(value(a, env) for a in x[1])
    if k == "bin":
        a, b = value(x[2], env), value(x[3], env)
        if x[1] in ("+", "-", "*"):
            return arith(x[1], a, b)
        if x[1] == "/":
            if b == 0:
                raise Undecided("division by zero")
            return a / b
        raise Undecided(f"operator {x[1]}")
    if k == "pow":
        a, e = value(x[1], env), value(x[2], env)
        if e.denominator != 1:
            raise Undecided(f"the rational power {T.to_qpp(x)}")
        if a == 0 and e < 0:
            raise Undecided("division by zero")
        return a ** int(e)
    if k == "abs":
        return abs(value(x[1], env))
    if k in ("ceil", "floor") and x[1][0] == "app" and x[1][1] == ("var", "lg") and len(x[1][2]) == 1:
        return lg_round(value(x[1][2][0], env), k == "ceil")
    if k in ("ceil", "floor"):
        v = value(x[1], env)
        return Fraction(math.ceil(v) if k == "ceil" else math.floor(v))
    if k in ("min", "max"):
        vals = []
        for i in sum_range(x, env):
            inner = env.child()
            inner.vals[x[1]] = Fraction(i)
            vals.append(value(x[3], inner))
        if not vals:
            raise Undecided(f"{k} over no index")
        return min(vals) if k == "min" else max(vals)
    if k in ("sum", "prod"):
        out = Fraction(0 if k == "sum" else 1)
        for i in sum_range(x, env):
            inner = env.child()
            inner.vals[x[1]] = Fraction(i)
            v = value(x[3], inner)
            out = out + v if k == "sum" else out * v
        return out
    raise Undecided(f"{k} in a term")


def lg_round(t, up):
    """the ceiling (up) or floor of lg t for a rational t > 0, exactly: the least k with t <= 2^k (the greatest k
    with 2^k <= t)"""
    if t <= 0:
        raise Undecided("lg of a number that is not positive")
    k = t.numerator.bit_length() - t.denominator.bit_length()
    while Fraction(2) ** k < t:
        k += 1
    while Fraction(2) ** (k - 1) >= t:
        k -= 1
    # now 2^(k-1) < t <= 2^k: k is the ceiling; the floor is k, or k - 1 unless t is a power of 2
    return Fraction(k if up or Fraction(2) ** k == t else k - 1)


def index(x, env):
    v = value(x, env)
    if v.denominator != 1:
        raise Undecided(f"the index {T.to_qpp(x)} is not an integer")
    return v


def family_range(t, i, env):
    """the indices that i runs over in t: the range of a declared family indexed by i, else the indices the row gives"""
    found = []

    def walk(x):
        if isinstance(x, tuple) and x:
            if x[0] == "app" and len(x) > 3 and x[3] == "idx" and x[1][0] == "var" and ("var", i) in x[2]:
                found.append(x[1][1])
            for y in Q.kids(x):
                walk(y)
    walk(t)
    for name in found:
        if name in env.fams:
            lo, hi = env.fams[name]
            return range(int(index(lo, env)), int(index(hi, env)) + 1)
    for name in found:
        fam = env.vals.get(Q.seq_key(name))
        if fam is not None and not callable(fam):
            return given_terms(t, i, sorted(fam), env)
    for name in found:
        vec = env.vals.get("b_" + name)
        if isinstance(vec, tuple):
            return range(1, len(vec) + 1)  # the components of the vector b_x
    raise Undecided(f"no range for the index {i}")


def given_terms(t, i, values, env):
    """the values of i at which the row gives every term of a sequence (a family with no range) that t takes at an
    index with i in it: a recurrence W_(i+1) = f(W_(i)) on a row W_0, ..., W_m is read at i < m (a finite row gives
    a finite part of the sequence; the result says so)"""
    terms = []

    def walk(x):
        if isinstance(x, tuple) and x:
            if (x[0] == "app" and len(x) > 3 and x[3] == "idx" and x[1][0] == "var" and x[1][1] not in env.fams
                    and isinstance(env.vals.get(Q.seq_key(x[1][1])), dict) and ("var", i) in T.subterms(x[2])):
                terms.append(x)
            for y in Q.kids(x):
                walk(y)
    walk(t)
    out = []
    for v in values:
        inner = env.child()
        inner.vals[i] = Fraction(v)
        ok = True
        for y in terms:
            try:
                idx = tuple(int(index(a, inner)) for a in y[2])
            except Undecided:
                continue  # another index of the term is bound later: decided there
            if (idx[0] if len(idx) == 1 else idx) not in env.vals[Q.seq_key(y[1][1])]:
                ok = False
        if ok:
            out.append(v)
        else:
            env.flags.add(f"{', '.join(sorted({y[1][1] for y in terms}))} read where the row gives its terms")
    return out


def bounds_range(body, i, env):
    """the values of an index i bound by no set (forall i : 1 <= i <= D => ...) between the bounds its hypothesis
    puts on it, from 0 when it puts none below (i is a natural number, as Lean reads it); None without an upper
    bound"""
    if body[0] not in ("imp", "ctx"):
        return None
    lo, hi, me = Fraction(0), None, ("var", i)
    for c in Q.flatten(body[1]):
        if c[0] != "rel":
            continue
        for op, a, b in zip(c[1], c[2], c[2][1:]):
            if op in (">=", ">"):
                op, a, b = ("<=" if op == ">=" else "<"), b, a
            if op not in ("<=", "<"):
                continue
            if b == me:
                lo = max(lo, index(a, env) + (op == "<"))
            elif a == me:
                v = index(b, env) - (op == "<")
                hi = v if hi is None else min(hi, v)
    return None if hi is None else range(int(lo), int(hi) + 1)


def sum_range(x, env):
    fam_lo = None
    rng = None
    if x[2] is None:
        return family_range(x[3], x[1], env)
    if x[2][0] == "cond":
        # the indices of the family that satisfy the condition
        out = []
        for i in family_range(("tuple", (x[2][1], x[3])), x[1], env):
            inner = env.child()
            inner.vals[x[1]] = Fraction(i)
            inner.types.vars[x[1]] = {"lean": x[1], "type": "\u2115"}
            if prop(x[2][1], inner):
                out.append(i)
        return out
    if x[2][0] == "in":
        return sorted(int(v) for v in elements(x[2][1], env))
    for name in index_families(x[3], x[1]):
        if name in env.fams:
            fam_lo = int(index(env.fams[name][0], env))
            break
    lo = fam_lo if fam_lo is not None else 1
    if x[2][0] == "range":
        rng = range(int(index(x[2][1][0], env)), int(index(x[2][1][1], env)) + 1)
    elif x[2][0] == "le":
        rng = range(lo, int(index(x[2][1], env)) + 1)
    elif x[2][0] == "lt":
        rng = range(lo, int(index(x[2][1], env)))
    else:
        raise Undecided(f"a sum over {T.to_qpp(x[2][1])}")
    return rng


def elements(s, env):
    """the elements of a finite set: a listing, the integers {a..b}, a set the row gives, or a builder {x in S : P}
    over one of these"""
    if s[0] == "setlist":
        return frozenset(value(a, env) for a in s[1])
    if s[0] == "intrange":
        return frozenset(Fraction(i) for i in range(int(index(s[1], env)), int(index(s[2], env)) + 1))
    if s[0] == "var" and isinstance(env.vals.get(s[1]), frozenset):
        return env.vals[s[1]]
    if s[0] == "setof" and s[1][0] == "such":
        head, cond = s[1][1], s[1][2]
        if head[0] == "rel" and head[1] == ("in",) and head[2][0][0] == "var":
            dom = head[2][1]
            first = cond[1][0] if cond[0] == "and" else cond
            if dom[0] == "set" and dom[1] in ("ZZ", "NN") and first[0] == "rel" and first[1] == ("<=", "<=") \
                    and first[2][1] == head[2][0]:
                # {k in Z : a <= k <= b, P}: the first condition bounds k, so k runs over {a..b}
                dom = ("intrange", first[2][0], first[2][2])
            out = set()
            for v in elements(dom, env):
                local = env.child()
                local.vals[head[2][0][1]] = v
                local.types.vars[head[2][0][1]] = {"lean": head[2][0][1], "type": "\u211a"}
                if context(cond, local):
                    out.add(v)
            return frozenset(out)
        if head[0] == "var" or (head[0] == "app" and head[3] == "idx"):
            # {k : P} or {a_k : P} for an index k of a family: the k (the a_k) with P (the head name k is bound
            # here, whatever the statement calls k)
            if head[0] == "var":
                idx = [head[1]]
                if Q.free_index_vars(cond) - set(env.vals) - {head[1]}:
                    raise Undecided(f"the elements of {T.to_qpp(s)}")
            else:
                idx = sorted(Q.free_index_vars(("tuple", (head, cond))) - set(env.vals))
            if len(idx) != 1:
                raise Undecided(f"the elements of {T.to_qpp(s)}")
            out = set()
            for i in family_range(("tuple", (head, cond)), idx[0], env):
                local = env.child()
                local.vals[idx[0]] = Fraction(i)
                local.types.vars[idx[0]] = {"lean": idx[0], "type": "\u2115"}
                if context(cond, local):
                    out.add(value(head, local))
            return frozenset(out)
    if s[0] == "bin" and s[1] in ("cap", "cup", "minus"):
        a, b = elements(s[2], env), elements(s[3], env)
        return a & b if s[1] == "cap" else a | b if s[1] == "cup" else a - b
    raise Undecided(f"the elements of {T.to_qpp(s)} (not a finite set the row decides)")


def index_families(t, i):
    out = []

    def walk(x):
        if isinstance(x, tuple) and x:
            if x[0] == "app" and len(x) > 3 and x[3] == "idx" and x[1][0] == "var" and ("var", i) in x[2]:
                out.append(x[1][1])
            for y in Q.kids(x):
                walk(y)
    walk(t)
    return out


# ---------------------------------------------------------------- sets and declarations

def member(v, s, env):
    """v in s"""
    if s[0] == "set" and s[1][:2] in SET_TYPES:
        base, rest = s[1][:2], s[1][2:]
        if base in ("ZZ", "NN") and v.denominator != 1:
            return False
        if base == "NN" and v < 0:
            return False
        if rest.startswith(">="):
            return v >= Fraction(rest[2:])
        if rest.startswith(">"):
            return v > Fraction(rest[1:])
        if rest:
            raise Undecided(f"the set {s[1]}")
        return True
    if s[0] == "word":
        w = env.vocab.get(s[1])
        if w is None or "set" not in w:
            raise Undecided(f"the word {s[1]}")
        return member(v, w["set"], env)
    if s[0] == "interval":
        lo, hi = value(s[1], env), value(s[2], env)
        if s[3] is not None:
            u = value(s[3], env)
            lo, hi = arith("*", lo, u), arith("*", hi, u)
        return le(lo, v) and le(v, hi)
    if s[0] == "ivl":
        return v in value(s, env)
    if s[0] in ("setlist", "intrange"):
        return v in elements(s, env)
    if s[0] == "bin" and s[1] in ("cap", "cup", "minus"):
        a = member(v, s[2], env)
        return (a and member(v, s[3], env)) if s[1] == "cap" else (a or member(v, s[3], env)) if s[1] == "cup" \
            else (a and not member(v, s[3], env))
    if s[0] == "pow":
        n = index(s[2], env)
        return isinstance(v, tuple) and len(v) == n and all(member(c, s[1], env) for c in v)
    if s[0] == "fun":
        if not callable(v):
            return False
        env.flags.add("functions taken as declared (domain and codomain not checked)")
        return True
    if s[0] == "setof" and s[1][0] == "such":
        return in_builder(v, s[1][1], s[1][2], env)
    if s[0] == "setof":
        return v in value(s, env)
    if s[0] == "var":
        return contains(value(s, env), v)
    raise Undecided(f"the set {T.to_qpp(s)}")


def in_builder(v, head, cond, env):
    """v in {head : cond}: {x in X : P} is v in X and P at x = v; an image {t : D} is solved by matching t with v
    (an interval [a, b] against a box, a name against anything), then D is checked on what the match gives"""
    local = env.child()
    if head[0] == "rel" and head[1] == ("in",) and head[2][0][0] == "var":
        if not member(v, head[2][1], env):
            return False
        local.vals[head[2][0][1]] = v
        return context(cond, local)
    match = {}
    if head[0] == "var":
        match[head[1]] = v
    elif head[0] == "interval" and head[3] is None and isinstance(v, Box) and head[1][0] == "var" \
            and head[2][0] == "var":
        match[head[1][1]], match[head[2][1]] = v.lo, v.hi
    else:
        raise Undecided(f"membership in the image {{{T.to_qpp(head)} : ...}}: no match for this value")
    for n, val in match.items():
        local.vals[n] = val
        local.types.vars[n] = {"lean": n, "type": "\u211a"}
    return context(cond, local)


def as_value(r):
    """a value a function of a fixture returns: an int or a Fraction, a tuple of them, or a box or finite set"""
    if isinstance(r, bool):
        raise ValueError("a function returned a boolean")
    if isinstance(r, (int, Fraction)):
        return Fraction(r)
    if isinstance(r, (list, tuple)):
        return tuple(as_value(c) for c in r)
    if isinstance(r, (Box, frozenset)):
        return r
    raise ValueError(f"a function returned {r!r}: an int, a Fraction or a tuple of them (exact)")


def row_get(row, name):
    """the row's value of a name: under its Q++ name, or under its Lean name (w for the bold b_w, mu for mu), or
    for a bold vector under its letter (varsigma for b_varsigma)"""
    if name in row:
        return row[name]
    if name.startswith("b_") and name[2:] in row:
        return row[name[2:]]
    return row.get(T.lean_name(name))


def row_value(raw, s, env):
    """the value of a declared name from the row: a number, a vector (a list, for Q^n), a function (a callable of a
    .py fixture), or a set ({"box": [lo, hi]} or a list of its points, for a word whose elements are sets)"""
    if callable(raw):
        return raw
    kind = elem_kind(s, env)
    if kind == "vec":
        if not isinstance(raw, list):
            raise ValueError(f"a vector is a list, not {raw!r}")
        return tuple(num(c) for c in raw)
    if isinstance(raw, dict) and set(raw) == {"box"}:
        lo, hi = raw["box"]
        conv = (lambda z: tuple(num(c) for c in z)) if isinstance(lo, list) else num
        return Box(conv(lo), conv(hi))
    if isinstance(raw, list):
        return frozenset(tuple(num(c) for c in p) if isinstance(p, list) else num(p) for p in raw)
    return num(raw)


def elem_kind(s, env):
    """what the elements of the set s are: vec (vectors), set (sets: boxes or finite sets) or num"""
    if s[0] == "pow":
        return "vec"
    if s[0] == "var" and s[1] in env.vals:
        S = env.vals[s[1]]
        if isinstance(S, Box):
            return "vec" if isinstance(S.lo, tuple) else "num"
        if isinstance(S, frozenset):
            return "vec" if any(isinstance(v, tuple) for v in S) else "num"
    if s[0] == "word":
        w = env.vocab.get(s[1])
        return elem_kind(w["set"], env) if w and "set" in w else "num"
    if s[0] == "setof" and s[1][0] == "such":
        head = s[1][1]
        if head[0] == "interval":
            return "set"
        if head[0] == "rel" and head[1] == ("in",):
            return elem_kind(head[2][1], env)
    return "num"


def set_type(s, env):
    if s[0] == "set" and s[1][:2] in SET_TYPES:
        return SET_TYPES[s[1][:2]]
    if s[0] == "word":
        w = env.vocab.get(s[1])
        if w and "set" in w:
            return set_type(w["set"], env)
    return "\u211a"


def bind(node, s, env):
    """bind a declared name to its row value, and check its membership (a family: every member)"""
    typ = set_type(s, env)
    if node[0] == "var":
        name = node[1]
        if name in env.vals:
            return member(env.vals[name], s, env)
        raw = row_get(env.row, name)
        if raw is None:
            raise Undecided(f"the row gives no value for {name}")
        env.vals[name] = row_value(raw, s, env)
        env.types.vars[name] = {"lean": name, "type": typ}
        return member(env.vals[name], s, env)
    if node[0] == "family" or (node[0] == "app" and node[3] == "idx" and node[1][0] == "var"):
        name = node[1] if node[0] == "family" else node[1][1]
        key = Q.seq_key(name)
        if node[0] == "family":
            env.fams[name] = (node[2], node[3])
        if key not in env.vals:
            raw = env.row.get(key)
            if raw is None:
                raise Undecided(f"the row gives no values for {name}_i (key {key})")
            if isinstance(raw, list):
                lo = int(index(node[2], env)) if node[0] == "family" else 1
                env.vals[key] = {lo + n: num(v) for n, v in enumerate(raw)}
            else:
                env.vals[key] = {int(i): num(v) for i, v in raw.items()}
            env.types.vars[key] = {"lean": name, "type": f"\u2115 \u2192 {typ}", "seq": True, "elem": typ}
        fam = env.vals[key]
        if node[0] == "family":
            want = range(int(index(node[2], env)), int(index(node[3], env)) + 1)
            if sorted(fam) != list(want):
                raise Undecided(f"the row gives {name} at {sorted(fam)}, the family runs over {list(want)}")
        return all(member(v, s, env) for v in fam.values())
    raise Undecided(f"a declaration of {T.to_qpp(node)}")


# ---------------------------------------------------------------- propositions

def free_indices(x, env):
    """the free indices of x (scoped: a sum binds its index), bound at x (qpp2lean.prefix_indices): an index letter,
    or any index of a family that the row gives no value for (mu_u with u free, as qpp2lean reads it)"""
    return [n for n in Q.prefix_indices(x, env.vals) if Q.is_index_name(n) or n not in env.row]


def for_all_indices(x, env, f, idx=None):
    """f(env') for every value of the free indices of x (over the ranges of their families)"""
    idx = free_indices(x, env) if idx is None else idx
    if not idx:
        return f(env)
    i, inner = idx[0], env.child()
    for v in family_range(x, i, env):
        inner.vals[i] = Fraction(v)
        inner.types.vars[i] = {"lean": i, "type": "\u2115"}
        if not for_all_indices(x, inner, f, idx[1:]):
            return False
    return True


def clause(c, env):
    """a clause of a context, binding what it declares: True, False"""
    if c[0] == "decl":
        return all(bind(n, c[2], env) for n in c[1])
    if c[0] == "def":
        if c[1][0] == "app" and c[1][1][0] == "var":
            return define(c[1], c[2], env)
        if c[1][0] != "var":
            raise Undecided(f"a definition of {T.to_qpp(c[1])}")
        env.vals[c[1][1]] = value(c[2], env)
        env.types.vars[c[1][1]] = {"lean": c[1][1], "type": "\u211a"}
        return True
    if c[0] == "ctx":
        return all(clause(y, env) for y in Q.flatten(c[1]) + Q.flatten(c[2]))
    if c[0] == "imp" and c[2][0] == "def":
        # a case of a case definition (H => x := t): the case whose condition holds defines x
        if c[2][1][0] != "var":
            raise Undecided(f"a case definition of {T.to_qpp(c[2][1])} on rows")
        return clause(c[2], env) if prop(c[1], env) else True
    if Q.family_decl(c):
        # theta_k in X for k in K: the row gives theta (a dict index -> value), checked at every k of K
        for name in Q.family_decl(c)[2]:
            key = Q.seq_key(name)
            if key not in env.vals:
                raw = env.row.get(key)
                if raw is None:
                    raise Undecided(f"the row gives no values for {name}_k (key {key})")
                pairs = raw.items() if isinstance(raw, dict) else enumerate(raw, 1)
                env.vals[key] = {int(i): num(v) for i, v in pairs}
                env.types.vars[key] = {"lean": name, "type": "\u2124 \u2192 \u211a", "seq": True, "elem": "\u211a"}
        return prop(c, env)
    if c[0] == "rel" and len(c[1]) == 1 and c[1][0] in ("subseteq", "subset") and c[2][0][0] == "var" \
            and c[2][0][1] not in env.vals:
        # S subseteq X declares S: the row gives it as a box or a list of points
        name, X = c[2][0][1], c[2][1]
        if name not in env.row:
            raise Undecided(f"the row gives no value for {name}")
        S = row_value(env.row[name], ("set", "QQ"), env)
        if not isinstance(S, (Box, frozenset)):
            raise ValueError(f"the set {name}: a box or a list of points")
        env.vals[name] = S
        env.types.vars[name] = {"lean": name, "type": "Set"}
        if X[0] in ("set", "pow"):
            pts = list(S) if isinstance(S, frozenset) else [S.lo, S.hi]
            return all(member(v, X, env) for v in pts)  # a box of Q^n: its corners in X decide
        return compare(c[1][0], S, value(X, env))
    if c[0] == "rel":
        # a chain of bounds on a new index declares it (1 <= k <= N): the row gives its value
        for a in c[2]:
            if a[0] == "var" and a[1] not in env.vals and Q.is_index_name(a[1]) and a[1] in env.row:
                env.vals[a[1]] = num(env.row[a[1]])
                env.types.vars[a[1]] = {"lean": a[1], "type": "\u2115"}
        if free_indices(c, env):
            # mu_u >= n_u / 3 in a context, u free in this clause only: for every u of the family's range, as the
            # Lean statement reads it (qpp2lean.free_index_prefix)
            return for_all_indices(c, env, lambda e: prop(c, e))
    return prop(c, env)


def define(lhs, rhs, env):
    """f(y) := E or sigma_(a, b) := E, the arguments names with no value (parameters): a function of them, read at
    each use; beta'_(j) := E at indices with values: that member of the family beta' (as qpp2lean.define_applied
    reads them)"""
    name, args = lhs[1][1], lhs[2]
    free = [a for a in args if not (a[0] == "var" and a[1] not in env.vals)]
    if free and len(free) < len(args):
        raise Undecided(f"a definition of {T.to_qpp(lhs)} with some indices declared, some free")
    key = Q.seq_key(name) if lhs[3] == "idx" else name
    if free:
        at = tuple(int(index(a, env)) for a in args)
        fam = env.vals.setdefault(key, {})
        if not isinstance(fam, dict):
            raise Undecided(f"a member of {name} and its definition")
        fam[at[0] if len(at) == 1 else at] = value(rhs, env)
    else:
        params = [a[1] for a in args]

        def f(*vals):
            if len(vals) != len(params):
                raise Undecided(f"{name} of {len(vals)} arguments, defined with {len(params)}")
            inner = env.child()
            for p, v in zip(params, vals):
                inner.vals[p] = Fraction(v)
                inner.types.vars[p] = {"lean": p, "type": "\u211a"}
            return value(rhs, inner)
        env.vals[key] = f
    typ = "\u211a"
    env.types.vars[key] = {"lean": name, "type": f"\u2115 \u2192 {typ}", "seq": True, "elem": typ} if lhs[3] == "idx" \
        else {"lean": name, "type": f"\u211a \u2192 {typ}"}
    return True


def witnesses(hyp, rest, env):
    """the witness rule of qpp2lean: a clause t in Z (or N) of a context, t not a name, binds an integer n = t, and t
    is read as n in what follows (so a defined relation is not expanded again on it). (hypotheses, rest), or
    (False, rest) when some t is not an integer"""
    keep = []
    for c in Q.flatten(hyp):
        if (c[0] == "rel" and c[1] == ("in",) and not Q.is_name_node(c[2][0]) and c[2][1][0] == "set"
                and c[2][1][1] in ("ZZ", "NN")):
            if not member(value(c[2][0], env), c[2][1], env):
                return False, rest
            n = Q.fresh("n", env.types)
            env.vals[n] = value(c[2][0], env)
            env.types.vars[n] = {"lean": n, "type": SET_TYPES[c[2][1][1]]}
            rest = Q.replace_term(rest, c[2][0], ("var", n))
            continue
        keep.append(c)
    return ("and", tuple(keep)), rest


def context(x, env):
    """the clauses of a context: its declarations first (a context declares its names wherever they stand in it, as
    the Lean statement does), then the other clauses in order"""
    cs = []

    def walk(y):
        for c in Q.flatten(y):
            if c[0] == "ctx":
                walk(c[1])
                walk(c[2])
            else:
                cs.append(c)
    walk(x)

    def declares(c):
        return c[0] == "decl" or Q.family_decl(c) is not None or (
            c[0] == "rel" and c[1] in (("subseteq",), ("subset",)) and c[2][0][0] == "var" and c[2][0][1] not in env.vals)
    first = [c for c in cs if declares(c)]
    return all(clause(c, env) for c in first) and all(clause(c, env) for c in cs if not any(c is d for d in first))


def prop(x, env):
    k = x[0]
    if k in ("and", "or", "iff", "imp", "ctx") and free_indices(x, env):
        # an index free in two parts is bound here, once for both (qpp2lean.prefix_indices): forall g : g != l =>
        # x_(g) != x_(l) binds l at the implication
        return for_all_indices(x, env, lambda e: prop(x, e))
    if k == "and":
        return all(prop(c, env) for c in x[1])
    if k == "or":
        return prop(x[1], env) or prop(x[2], env)
    if k == "iff":
        return prop(x[1], env) == prop(x[2], env)
    if k in ("imp", "ctx"):
        inner = env.child()
        hyp, rest = witnesses(x[1], x[2], inner)
        if hyp is False:
            return True
        return (not context(hyp, inner)) or prop(rest, inner)
    if k == "decl":
        return all(bind(n, x[2], env) for n in x[1])
    if k in ("exists", "forall"):
        return quantifier(x, env)
    if k == "textrel":
        r = Q.expand_textrel(x, env.types)
        if r is None:
            raise Undecided(f"the relational word {' _ '.join(x[1])} has no row")
        return prop(r, env)
    if k == "on":
        return on(x[1], x[2], env)
    if k == "not":
        return not prop(x[1], env)
    if k == "at":
        # P at p: P with the functions the row gives applied at the point p (as qpp2lean.at_point reads it)
        fs = {n for n, v in env.vals.items() if callable(v)}
        return prop(Q.apply_on(x[2], fs, x[1]), env)
    if k == "rel":
        return for_all_indices(x, env, lambda e: chain(x, e))
    raise Undecided(f"{k} in a statement")


def on(S, P, env):
    """P on S: P at every point of S, with the functions applied there; a box is sampled on the grid the fixture
    gives (bounds "grid": g, g + 1 points per axis), and the result says so; without a grid it is undecided"""
    Sv = value(S, env)
    if isinstance(Sv, frozenset):
        pts = list(Sv)
    elif isinstance(Sv, Box):
        g = env.bounds.get("grid")
        if g is None:
            raise Undecided("P on a box without a grid")
        EN.enumerating(f"the points of a grid of a box: {T.to_qpp(S)}")
        env.flags.add(f"sampled on a grid of {g}")
        lo, hi = Sv.lo, Sv.hi
        if not isinstance(lo, tuple):
            pts = [lo + (hi - lo) * Fraction(i, g) for i in range(g + 1)]
        else:
            import itertools
            axes = [[a + (b - a) * Fraction(i, g) for i in range(g + 1)] for a, b in zip(lo, hi)]
            pts = [tuple(p) for p in itertools.product(*axes)]
    else:
        raise Undecided("P on a set that is not a box or a finite set")
    fs = {n for n, v in env.vals.items() if callable(v)}
    w = "w"
    while w in env.vals:
        w += "'"
    body = Q.apply_on(P, fs, ("var", w))
    for p in pts:
        inner = env.child()
        inner.vals[w] = p
        if not prop(body, inner):
            return False
    return True


def chain(x, env):
    for op, a, b in zip(x[1], x[2], x[2][1:]):
        if op == "in":
            if not member(value(a, env), b, env):
                return False
            continue
        r = Q.expand_relation(op, a, b, env.types)
        if r is not None:
            if not prop(r, env):
                return False
            continue
        if not compare(op, value(a, env), value(b, env)):
            return False
    return True


def quantifier(x, env):
    ex = x[0] == "exists"
    vs, s, body = x[1], x[2], x[3]
    if any(v[0] != "var" for v in vs):
        raise Undecided("a binder that is not a name")
    ranges = []
    for v in vs:
        if s is None:
            try:
                ranges.append(list(family_range(body, v[1], env)))
            except Undecided:
                rng = bounds_range(body, v[1], env)
                if rng is None:
                    raise
                if not EN.index_only(body, v[1]):
                    EN.enumerating(f"the numbers up to a bound: {T.to_qpp(x)}")
                ranges.append(list(rng))
            continue
        if s[0] in ("interval", "ivl"):
            # forall x in [a, b]: on the grid of the fixture (bounds "grid": g, g + 1 points), as P on a box is
            B, g = value(s, env), env.bounds.get("grid")
            if g is None:
                raise Undecided(f"{x[0]} {v[1]} in an interval without a grid")
            EN.enumerating(f"the points of a grid of an interval: {T.to_qpp(x)}")
            env.flags.add(f"sampled on a grid of {g}")
            ranges.append([t for t in (B.lo + (B.hi - B.lo) * Fraction(n, g) for n in range(g + 1)) if t in B])
            continue
        if s[0] == "set" and s[1][:2] in ("ZZ", "NN"):
            if ex or not EN.index_only(body, v[1]):
                EN.enumerating(f"the numbers up to a bound: {T.to_qpp(x)}")
            rest = s[1][2:]
            lo = Fraction(rest[2:]) if rest.startswith(">=") else Fraction(rest[1:]) + 1 if rest.startswith(">") else None
            if s[1][:2] == "NN" and lo is None:
                lo = Fraction(0)
            b = env.bounds.get(v[1])
            rng = bounds_range(body, v[1], env) if b is None and lo is not None and not ex else None
            if rng is not None:
                # forall r in NN>=1 : r <= N => ...: the bound the hypothesis puts on r
                ranges.append([t for t in rng if t >= lo])
                continue
            if lo is None or b is None:
                raise Undecided(f"{x[0]} {v[1]} in {s[1]} without a bound")
            env.flags.add(f"bounded {v[1]} <= {b}")
            ranges.append(list(range(int(lo), int(b) + 1)))
            continue
        if s[0] == "set" and s[1].startswith("QQ") and isinstance(env.bounds.get(v[1]), list):
            # a quantifier over Q, Q>0, ... on the sample points the fixture gives: a spec of a function the row
            # gives (forall x in Q>0 : 2^(-e(x)-1) < x <= 2^(-e(x))) is checked there, and the result says so
            EN.enumerating(f"the sample points over Q of the fixture: {T.to_qpp(x)}")
            pts = [Fraction(str(t)) for t in env.bounds[v[1]]]
            ranges.append([t for t in pts if member(t, s, env)])
            env.flags.add(f"sampled {v[1]} in {s[1]} at {len(ranges[-1])} points")
            continue
        S = value(s, env) if s[0] == "var" and s[1] in env.vals else None
        if isinstance(S, frozenset):
            ranges.append(sorted(S))  # a finite set the row gives
            continue
        raise Undecided(f"{x[0]} {v[1]} in {T.to_qpp(s)}")

    def go(n, inner):
        if n == len(vs):
            return prop(body, inner)
        for val in ranges[n]:
            inner.vals[vs[n][1]] = Fraction(val)
            typ = "\u2124" if s is not None and s[0] == "set" and s[1][:2] == "ZZ" else "\u211a" if s is not None and s[0] != "set" else "\u2115"
            inner.types.vars[vs[n][1]] = {"lean": vs[n][1], "type": typ}
            if go(n + 1, inner) == ex:
                return ex
        return not ex
    return go(0, env.child())


# ---------------------------------------------------------------- results

def result(paper, label):
    for r in paper["results"]:
        if r["label"] == label and r["kind"] != "proof":
            return r
    raise KeyError(label)


def items_of(r, vocab=None, only=None):
    """[(key, [parts])], given first; an empty key continues the previous item. With only, the given and the items
    only (with their continuations): a hole elsewhere does not block them, as an item stands on its own in qpp2lean.
    The items read as qpp2lean.statement reads them: a core item without the given (qpp2lean.stand_alone); the
    clauses of the given that the Lean statement leaves out (a clause with a hole, or one that does not compile,
    that no conclusion needs) left out here too, so a row checks the statement the Lean side states; f_0 a term of
    the family f (qpp2lean.family_digits); the operators the result or the vocabulary defines (a_1 par ... par a_N
    := R) replaced by their definitions"""
    raw, skip = [], False
    for k, q in r["items"]:
        if k != "-":
            skip = bool(only) and k != "given" and k not in only
        if not skip:
            raw.append((k, q))
    raw = Q.stand_alone(raw)
    kept, holes = Q.given_without_holes(raw)
    out = []
    for k, q in kept:
        if T.is_formal(q) is False:
            raise Undecided(f"item {k} has a hole")
        parts = T.parse_qpp_item(q)
        if k == "-" and out:
            out[-1][1].extend(parts)
        else:
            out.append((k, parts))
    if holes:
        try:
            Q.hole_drops(out, holes)
        except Q.Skip as e:
            raise Undecided(str(e))
    out = Q.with_op_defs(Q.family_digits(out), vocab or {})
    dropped = lean_drops(r, raw, vocab)
    if not dropped:
        return out
    return [(k, [("and", tuple(c for c in Q.flatten(p) if T.to_qpp(c) not in dropped)) for p in ps])
            if k == "given" else (k, ps) for k, ps in out]


def lean_drops(r, raw, vocab):
    """the clauses of the given (in Q++) that qpp2lean.statement leaves out of the statement of the items raw since
    they do not compile (no conclusion uses their names); the drop rule is shared, so that the two readers check one
    statement, and the evaluation stays this reader's own"""
    cache = r.setdefault("_lean_drops", {})
    key = tuple(raw)
    if key not in cache:
        try:
            Q.statement(raw, vocab)
        except Exception:  # noqa: BLE001 (the clauses read before the statement stopped are the ones it drops)
            pass
        cache[key] = set(Q.STMT_DROPPED)
    return cache[key]


def check(paper, label, row, bounds=None, only=None):
    """{'given': bool, 'items': {key: status}, 'flags': [...]} for the result `label` of the paper on the row (the
    conclusion items `only`, or all)"""
    if isinstance(paper, str):
        paper = Q.read_qpp(paper)
    vocab = paper.get("vocab") or dict(T.PRELUDE)
    env = Env(vocab, row, bounds or {})
    out = {"given": None, "items": {}, "flags": []}
    try:
        items = items_of(result(paper, label), vocab, only)
    except Undecided as e:
        out["given"] = f"undecided: {e}"
        return out
    try:
        # the paper's context (the dimension n): a context row that declares a name the row gives is read whole
        # (qpp2lean.context_row)
        g = all(clause(c, env) for part in vocab.get("#context", []) for c in Q.context_row(part, set(row), env.types))
        g = g and all(context(p, env) for k, ps in items if k == "given" for p in ps)
    except Undecided as e:
        out["given"] = f"undecided: {e}"
        return out
    out["given"] = g
    for k, ps in items:
        if k == "given" or (only and k not in only):
            continue
        if not g:
            out["items"][k] = "vacuous"
            continue
        out["items"][k] = part_status(ps, env)
    out["flags"] = sorted(env.flags)
    return out


def part_status(parts, env):
    """holds, fails, vacuous (no instance satisfies the hypotheses) or undecided. The indices free on both sides of
    an implication are bound at the implication, over the ranges of their families; an index free on one side is
    bound at its own clause (as in qpp2lean: prefix_indices)"""
    status = "holds"
    for p in parts:
        try:
            if p[0] in ("imp", "ctx"):
                seen = set()

                def one(e):
                    inner = e.child()
                    hyp, rest = witnesses(p[1], p[2], inner)
                    if hyp is False or not context(hyp, inner):
                        seen.add("vacuous")
                        return True
                    ok = prop(rest, inner)
                    seen.add("holds" if ok else "fails")
                    return ok
                for_all_indices(p, env, one, free_indices(p, env))
                if "fails" in seen:
                    return "fails"
                if "holds" not in seen:
                    return "vacuous"
                continue
            ok = prop(p, env.child())
        except Undecided as e:
            return f"undecided: {e}"
        if not ok:
            status = "fails"
    return status


# ---------------------------------------------------------------- fixtures

STDLIB = {"fractions", "itertools", "math", "random", "functools", "collections", "operator"}
KINDS = ("instances", "witness")


def load_fixture(path):
    """(kind, bounds, rows) of a fixture: a .json table {"kind", "bounds", "rows"}, or a .py algorithm in the standard
    library only, with rows() and optionally KIND and BOUNDS"""
    path = Path(path)
    if path.suffix == ".json":
        d = json.loads(path.read_text(encoding="utf-8"))
        kind, bounds, rows = d.get("kind", "instances"), d.get("bounds", {}), list(d["rows"])
    elif path.suffix == ".py":
        other = stdlib_only(path)
        if other:
            raise ValueError(f"{path.name} imports {sorted(other)}: an algorithm uses the standard library only")
        ns = runpy.run_path(str(path))
        kind, bounds, rows = ns.get("KIND", "instances"), ns.get("BOUNDS", {}), list(ns["rows"]())
    else:
        raise ValueError(f"{path.name}: a fixture is a .json table or a .py algorithm")
    if kind not in KINDS:
        raise ValueError(f"{path.name}: kind {kind} (one of {KINDS})")
    return kind, bounds, rows


def stdlib_only(path):
    """the modules a .py fixture imports beyond the standard library allowed for algorithms"""
    import ast
    mods = set()
    for n in ast.walk(ast.parse(Path(path).read_text(encoding="utf-8"))):
        if isinstance(n, ast.Import):
            mods |= {a.name.split(".")[0] for a in n.names}
        elif isinstance(n, ast.ImportFrom):
            mods.add((n.module or "").split(".")[0] if n.level == 0 else ".")
    return mods - STDLIB


def fixture_path(fixdir, fid):
    """the file of a fixture ID in the folder: <id>.json or <id>.py, exactly one"""
    found = [p for p in (Path(fixdir) / f"{fid}.json", Path(fixdir) / f"{fid}.py") if p.exists()]
    if len(found) != 1:
        raise FileNotFoundError(f"fixture {fid}: {'no file' if not found else 'both .json and .py'} in {fixdir}")
    return found[0]


def fixtures_of(paper):
    """[(label, item or None, id)] from the `fix` lines of the .qpp (the \\FIX{id} of the LaTeX)"""
    return [(r["label"], k, fid) for r in paper["results"] for k, fid in r.get("fixes", [])]


def run_fixture(paper, label, item, path):
    """(kind, counts {status: n}, bad [(row, status)], flags) of a fixture of the result label (item None: every
    item). instances: no row fails or is undecided, and some row holds; witness: every row holds. The flags say what
    was bounded."""
    kind, bounds, rows = load_fixture(path)
    counts, bad, flags = {}, [], set()
    for row in rows:
        r = check(paper, label, row, bounds, [item] if item else None)
        flags |= set(r["flags"])
        if r["given"] is not True:
            st = "vacuous" if r["given"] is False else r["given"]
        else:
            keys = [item] if item else list(r["items"])
            sts = [r["items"].get(k, f"undecided: no item {k}") for k in keys]
            st = next((s for s in sts if s == "fails" or s.startswith("undecided")),
                      next((s for s in sts if s != "holds"), "holds"))
        counts[st] = counts.get(st, 0) + 1
        if st == "fails" or st.startswith("undecided") or (kind == "witness" and st != "holds"):
            bad.append((row, st))
    if not counts.get("holds"):
        bad.append((None, "no row meets the hypotheses and the conclusion"))
    return kind, counts, bad, sorted(flags)


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(description="check the fixtures that the fix lines of a .qpp file point to")
    ap.add_argument("qpp")
    ap.add_argument("fixdir")
    a = ap.parse_args(argv)
    paper = Q.read_qpp(Path(a.qpp).read_text(encoding="utf-8"))
    ok = True
    for label, item, fid in fixtures_of(paper):
        kind, counts, bad, flags = run_fixture(paper, label, item, fixture_path(a.fixdir, fid))
        print(f"{fid} ({label} {item or 'all'}, {kind}): {counts}{' ' + str(flags) if flags else ''} "
              + ("OK" if not bad else f"FAILED {bad[:3]}"))
        ok = ok and not bad
    return 0 if ok else 1


# ---------------------------------------------------------------- the test

REPO = Path(__file__).resolve().parents[2]


def extracted():
    """(.qpp file, fixtures folder): the test files qpp/tests/fixtures/*.qpp with a fix line, their fixtures next to
    them. The fixtures of the Q++ modules, modules/M/fixtures, are checked by qpp/modfix.py, with the checker of this
    file"""
    return [(q, q.parent) for q in sorted((REPO / "qpp" / "tests" / "fixtures").glob("*.qpp"))
            if "\n  fix " in q.read_text(encoding="utf-8")]


def _cases():
    out = []
    for q, fixdir in extracted():
        paper = Q.read_qpp(q.read_text(encoding="utf-8"))
        out += [(q, fixdir, label, item, fid) for label, item, fid in fixtures_of(paper)]
    return out


CASES = _cases()


@pytest.mark.parametrize("qpp,fixdir,label,item,fid", CASES,
                         ids=[f"{c[0].stem}:{c[4]}" for c in CASES])
def test_fixture(qpp, fixdir, label, item, fid):
    """the rows of the fixture check on the statement: none fails or is undecided, some row holds, and for a witness
    fixture every row holds"""
    paper = Q.read_qpp(Path(qpp).read_text(encoding="utf-8"))
    kind, counts, bad, flags = run_fixture(paper, label, item, fixture_path(fixdir, fid))
    assert not bad, f"{fid} ({kind}, {counts}, {flags}): {bad[:3]}"


@pytest.mark.parametrize("qpp,fixdir", extracted(), ids=[q.stem for q, _ in extracted()])
def test_every_fixture_is_named(qpp, fixdir):
    """a fixture file that no fix line names is an orphan (a fix line without its file fails in test_fixture)"""
    named = {fid for _, _, fid in fixtures_of(Q.read_qpp(Path(qpp).read_text(encoding="utf-8")))}
    files = {p.name[: -len(p.suffix)] for p in Path(fixdir).iterdir() if p.suffix in (".json", ".py")}
    assert files <= named, f"fixtures that no \\FIX names: {sorted(files - named)}"


# ---------------------------------------------------------------- the reader on rows

from fractions import Fraction as Fr  # noqa: E402
import random  # noqa: E402

from qpp import latex2qpp  # noqa: E402

REL = ("relation e in QQ, x, c in #mass : x <= c * 2^(-e) :<=> forall q in ZZ>=1 : q * e in ZZ => "
       "x^q <= c^q * 2^(-(q * e))\n")

TOY = ("paper X\nword mass := QQ>0\n" + REL + "\nlemma lem:x\n  given: x in QQ, N in NN, a_(1..N) in QQ>=0\n"
       "  (1): x <= (sum i, a_(i))\n  (2): a_(i) <= x => N * a_(i) <= N * x\n"
       "  (3): a_(i) <= x => (sum j, a_(j)) <= N * x\n"
       "lemma lem:p\n  given: e in QQ, x, c in #mass\n  (1): x <= c * 2^(-e)\n")


def test_rows_hold_fail_or_are_vacuous():
    r = check(TOY, "lem:x", {"x": 3, "N": 2, "a[]": [1, 2]})
    assert r == {"given": True, "items": {"(1)": "holds", "(2)": "holds", "(3)": "holds"}, "flags": []}
    assert check(TOY, "lem:x", {"x": 4, "N": 2, "a[]": [1, 2]})["items"]["(1)"] == "fails"
    # the index i of (2), free on both sides, is bound at the implication: i = 1 is an instance, i = 2 does not
    # meet a_i <= x
    assert check(TOY, "lem:x", {"x": 1, "N": 2, "a[]": [1, 2]})["items"]["(2)"] == "holds"
    assert check(TOY, "lem:x", {"x": "1/2", "N": 2, "a[]": [1, 2]})["items"]["(2)"] == "vacuous"
    # the index i of (3) is free in the hypothesis only: it is bound there (every a_i <= x), so x = 1 with a_2 = 2
    # is no instance (bound at the implication, i = 1 would be one and the sum 3 <= 2 would fail)
    assert check(TOY, "lem:x", {"x": 1, "N": 2, "a[]": [1, 2]})["items"]["(3)"] == "vacuous"
    assert check(TOY, "lem:x", {"x": 2, "N": 2, "a[]": [1, 2]})["items"]["(3)"] == "holds"
    assert check(TOY, "lem:x", {"x": 3, "N": 2, "a[]": [-1, 2]})["given"] is False
    assert check(TOY, "lem:x", {"x": 3, "N": 3, "a[]": [1, 2]})["given"].startswith("undecided")
    with pytest.raises(ValueError):
        check(TOY, "lem:x", {"x": 0.5, "N": 2, "a[]": [1, 2]})


def test_power_reading_against_the_exact_criterion():
    """x <= c 2^{-e} read by powers (bounded at q <= the denominator of e) agrees with x^d <= c^d 2^{-de}, d the
    denominator of e, on random masses and exponents"""
    rng = random.Random(20261106)
    for _ in range(200):
        x, c = Fr(rng.randint(1, 50), rng.randint(1, 9)), Fr(rng.randint(1, 50), rng.randint(1, 9))
        e = Fr(rng.randint(-12, 12), rng.randint(1, 4))
        d = e.denominator
        want = x ** d <= c ** d * Fr(2) ** int(-d * e)
        r = check(TOY, "lem:p", {"e": str(e), "x": str(x), "c": str(c)}, {"q": d})
        assert r["items"]["(1)"] == ("holds" if want else "fails") and r["flags"] == [f"bounded q <= {d}"]
    assert check(TOY, "lem:p", {"e": "1/2", "x": 1, "c": 1})["items"]["(1)"].startswith("undecided")


def test_fixture_rules(tmp_path):
    paper = Q.read_qpp(TOY)
    (tmp_path / "v.json").write_text('{"rows": [{"x": 1, "N": 2, "a[]": [-1, 5]}]}', encoding="utf-8")
    assert run_fixture(paper, "lem:x", "(1)", tmp_path / "v.json")[2][-1][1].startswith("no row")
    (tmp_path / "w.json").write_text('{"kind": "witness", "rows": [{"x": 9, "N": 1, "a[]": [1]}, '
                                     '{"x": 9, "N": 1, "a[]": [-1]}]}', encoding="utf-8")
    kind, counts, bad, _ = run_fixture(paper, "lem:x", "(2)", tmp_path / "w.json")
    assert counts == {"holds": 1, "vacuous": 1} and bad[0][1] == "vacuous"
    (tmp_path / "np.py").write_text("import numpy\ndef rows():\n    return []\n", encoding="utf-8")
    with pytest.raises(ValueError):
        load_fixture(tmp_path / "np.py")
    with pytest.raises(FileNotFoundError):
        fixture_path(tmp_path, "missing")


def test_fix_tokens_name_items():
    src = (r"\begin{lemmaS}\label{lem:t}\begin{stmt}\sit{given}{x\in\Q}\sit{(1)}{x\le x}\FIX{t.1} \FIX{t.1b}"
           r"\sit{(2)}{x\ge x}\end{stmt}\FIX{t.all}\end{lemmaS}")
    text, _ = latex2qpp.convert(src, "T")
    assert "  fix (1) t.1\n  fix (1) t.1b\n  fix * t.all\n" in text
    assert fixtures_of(Q.read_qpp(text)) == [("lem:t", "(1)", "t.1"), ("lem:t", "(1)", "t.1b"),
                                                           ("lem:t", None, "t.all")]




def test_a_free_index_of_a_context_clause_runs_over_its_family():
    """mu_u >= n_u / 3 in a context, u free in that clause only: every u of the family's range, as qpp2lean reads it
    (u is no index letter, and the row gives no value for it)"""
    src = (r"\begin{lemma}\label{lem:c}x\begin{stmt}\sit{core}{U\in\N,\ n_1,\dots,n_U\in\N,\ \mu_1,\dots,\mu_U\in\Q,"
           r"\ \mu_u\ge\tfrac{n_u}3:\ \textstyle\sum_{u=1}^U\mu_u\ge0}\end{stmt}\end{lemma}")
    text, _ = latex2qpp.convert(src, "T")
    assert check(text, "lem:c", {"U": 2, "n[]": [3, 6], "mu[]": [1, 2]})["items"] == {"core": "holds"}
    assert check(text, "lem:c", {"U": 2, "n[]": [3, 6], "mu[]": [1, 1]})["items"] == {"core": "vacuous"}


def _one(given, key, item):
    src = (r"\begin{lemma}\label{lem:g}x\begin{stmt}\sit{given}{%s}\sit{%s}{%s}\end{stmt}\end{lemma}" % (given, key, item))
    return latex2qpp.convert(src, "T")[0]


def test_the_reader_reads_the_statement_the_lean_side_states():
    """the clauses of the given that qpp2lean leaves out (with a hole, or not compiling, and needed by no
    conclusion) are left out on rows too; a core item stands alone; f_0 is a term of the family f"""
    text = _one(r"p=1;\ \text{(H2) at}\ t^*;\ \text{(H4) in words}", "(1)",
                r"\eta\in\N,\ x\in\Q_{\ge0},\ (3+\eta)x\ge1:\ x\ge\tfrac1{3+\eta}")
    assert check(text, "lem:g", {"eta": 0, "x": "1/3"})["items"] == {"(1)": "holds"}
    assert check(text, "lem:g", {"eta": 0, "x": "1/4"})["items"] == {"(1)": "vacuous"}
    text = _one(r"k\in\N;\ \text{(H2) at}\ v:=t^*", "(1)", r"v\ge0")
    assert check(text, "lem:g", {"k": 1, "v": 0})["given"] == ("undecided: item given has a hole that mentions v, "
                                                               "which a conclusion uses")
    text = _one(r"k\in\N_{\ge1},\ m:=k+1,\ \text{a prose clause on}\ k", "core", r"k\in\N_{\ge1}:\ k+1\ge2")
    assert check(text, "lem:g", {"k": 1}) == {"given": True, "items": {"core": "holds"}, "flags": []}
    # a recurrence on a sequence, read where the row gives its terms; W_0 is the term W_(0)
    text = _one(r"C\in\N,\ W_i\in\N;\ W_0=C,\ W_{i+1}=2W_i+C", "(1)", r"W_1\ge W_0")
    r = check(text, "lem:g", {"C": 1, "W[]": {"0": 1, "1": 3, "2": 7}})
    assert r["items"] == {"(1)": "holds"} and r["flags"] == ["W read where the row gives its terms"]
    assert check(text, "lem:g", {"C": 1, "W[]": {"0": 1, "1": 3, "2": 8}})["given"] is False
    assert "a list starts at 1" in check(text, "lem:g", {"C": 1, "W[]": [1, 3, 7]})["given"]


def test_definitions_choose_ranges_and_intervals_on_rows():
    """a function and a family defined in a context, a binomial coefficient, a quantified index bound by its
    hypothesis (from 0 when only bounded above, as Lean reads it), an index bound at an implication, and a
    quantifier over an interval on the grid of the fixture"""
    text = _one(r"y\in\Q;\ \rho(t):=t^2+1", "(1)", r"\rho(y)>0")
    assert check(text, "lem:g", {"y": -3})["items"] == {"(1)": "holds"}
    text = _one(r"i,j\in\Z,\ \theta_i,\theta_j\in\Q;\ \sigma_{ab}:=\tfrac{\theta_a-\theta_b}{b-a}", "(1)",
                r"\sigma_{ij}=\sigma_{ji}")
    assert check(text, "lem:g", {"i": 0, "j": 2, "theta[]": {"0": 1, "2": 5}})["items"] == {"(1)": "holds"}
    text = _one(r"q\in\N", "core", r"k\in\N,\ \bd\in\Q^k,\ \rho(t):=\textstyle\sum_h(t-\delta_h)^2,\ y\in\Q:\ \rho(y)\ge0")
    assert check(text, "lem:g", {"k": 2, "delta": [1, "1/2"], "y": 0})["items"] == {"core": "holds"}
    text = _one(r"p\in\N_{\ge1},\ x\in\Q", "(1)", r"\textstyle\sum_{i=0}^p\binom pi x^i=(1+x)^p")
    assert check(text, "lem:g", {"p": 3, "x": "1/2"})["items"] == {"(1)": "holds"}
    text = _one(r"D\in\N,\ c\in\Q", "(1)", r"c\cdot i\ge0\ \text{for}\ 1\le i\le D")
    assert [check(text, "lem:g", {"D": 3, "c": c})["items"]["(1)"] for c in (1, -1)] == ["holds", "fails"]
    text = _one(r"D\in\N,\ c\in\Q", "(1)", r"c+i\ge1\ \text{for}\ i\le D")
    assert check(text, "lem:g", {"D": 3, "c": "1/2"})["items"] == {"(1)": "fails"}  # i = 0 is an instance
    text = _one(r"D\in\N,\ x_1,\dots,x_D\in\Q", "(1)", r"x_g\ne x_l\ \text{for}\ g\ne l")
    assert [check(text, "lem:g", {"D": 3, "x[]": x})["items"]["(1)"] for x in ([1, 2, 3], [1, 2, 1])] == ["holds", "fails"]
    text = _one(r"a,b\in\Q,\ a<b", "(1)", r"\forall x\in(a,b]:\ x>a")
    r = check(text, "lem:g", {"a": 0, "b": 1}, {"grid": 4})
    assert r["items"] == {"(1)": "holds"} and r["flags"] == ["sampled on a grid of 4"]
    assert check(text, "lem:g", {"a": 0, "b": 1})["items"]["(1)"].startswith("undecided")
    text = _one(r"y\in\Q", "(1)", r"(y)_+\ge y")
    assert check(text, "lem:g", {"y": -2})["items"] == {"(1)": "holds"}


def test_relational_words_on_rows():
    import test_pipeline as P
    text, _ = latex2qpp.convert(P.CLOSE, "T")
    paper = Q.read_qpp(text)
    assert check(paper, "lem:close", {"x": "-1", "y": "1/2"})["items"] == {
        "(1)": "vacuous", "(2)": "holds", "(3)": "holds"}
    # (2) is false: two small numbers need not be close to 0, and the row x = y = 1 says so
    assert check(paper, "lem:close", {"x": 1, "y": 1}, only=["(2)"])["items"] == {"(2)": "fails"}


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))


def test_vectors_boxes_functions_and_on():
    """the statements of test_pipeline.BOXES on rows: vectors are lists, sets boxes or lists of points, functions
    callables (as a .py fixture gives them); P on a box is sampled on the grid of the fixture"""
    import test_pipeline as P
    text, _ = latex2qpp.convert(P.BOXES, "T")
    paper = Q.read_qpp(text)

    def K(w):
        return w[0] + w[1]

    row = {"n": 2, "S": {"box": [[0, 0], [2, 2]]}, "B": {"box": [[0, 0], [1, 1]]}, "w": [1, "1/2"], "K": K,
           "a": [0, 0], "b": [1, 2]}
    r = check(paper, "lem:b", row, {"grid": 2})
    assert r["given"] is True and r["items"] == {"(1)": "holds", "(2)": "holds", "(3)": "holds", "(4)": "holds"}
    assert "sampled on a grid of 2" in r["flags"]
    # (3) without its hypothesis B subseteq S: a K negative on part of B, on a grid that sees it
    row2 = dict(row, S={"box": [[0, 0], [1, 1]]}, B={"box": [[-1, -1], [1, 1]]}, w=[0, 0])
    assert check(paper, "lem:b", row2, {"grid": 2}, only=["(3)"])["items"] == {"(3)": "vacuous"}
    row3 = dict(row, S=[[0, 0], [1, 1]], B={"box": [[1, 1], [1, 1]]}, w=[1, 1])
    assert check(paper, "lem:b", row3, {"grid": 1})["items"]["(1)"] == "holds"
    assert check(paper, "lem:b", dict(row, w=[3, 3]))["given"] is False          # w not in B
    assert check(paper, "lem:b", row)["items"]["(3)"].startswith("undecided")      # no grid
    assert check(paper, "lem:b", dict(row, b=[1, -1]), only=["(2)"])["items"] == {"(2)": "vacuous"}  # a <= b fails
    bad = dict(row, K=lambda w: w[0] - 1)
    assert check(paper, "lem:b", bad, {"grid": 2})["items"]["(4)"] == "vacuous"   # K(w) = 0: (4) needs K(w) > 0
    assert check(paper, "lem:nodim", {"e": lambda t: 1})["items"] == {"(1)": "holds"}


def test_vector_components_and_strict_order():
    """test_pipeline.VECS on rows: the components w_i of w are numbered from 1; a < b holds in every component, so a
    flat box is not a box"""
    import test_pipeline as P
    text, _ = latex2qpp.convert(P.VECS, "T")
    paper = Q.read_qpp(text)
    row = {"n": 2, "a": [0, 0], "b": [1, 2], "w": [1, "1/2"], "c": 1}
    assert check(paper, "lem:v", row)["items"] == {k: "holds" for k in ("(1)", "(2)", "(3)", "(4)", "(5)", "(6)")}
    flat = dict(row, b=[1, 0])                      # a <= b, a != b: Lean's a < b, not Q++'s
    assert check(paper, "lem:v", flat, only=["(1)"])["items"] == {"(1)": "vacuous"}
    assert check(paper, "lem:v", dict(row, w=[1, 0]), only=["(2)"])["items"] == {"(2)": "vacuous"}
    assert check(paper, "lem:v", dict(row, w=[2, 0]), only=["(3)"])["items"] == {"(3)": "vacuous"}
    assert check(paper, "lem:v", dict(row, w=[-1, -1]), only=["(4)"])["items"] == {"(4)": "fails"}
    assert check(paper, "lem:v", dict(row, w=[1, -1]), only=["(6)"])["items"] == {"(6)": "fails"}  # 2^2 (-1) < -1


def test_folds_defined_operators_min_max_and_contexts():
    """test_pipeline.FOLDS on rows: the parallel sum by its definition, min by its value, the ceiling of lg exactly"""
    import test_pipeline as P
    text, _ = latex2qpp.convert(P.FOLDS, "T")
    paper = Q.read_qpp(text)

    def e(x):  # the exponent: 2^(-e-1) < x <= 2^(-e)
        return -int(lg_round(Fraction(x), True))
    row = {"N": 3, "a[]": [1, 2, 4], "e": e}
    assert check(paper, "lem:f", row)["items"] == {"sums": "holds", "masses": "holds"}
    assert [lg_round(Fraction(t), True) for t in (1, 2, 3, 4, 5)] == [0, 1, 2, 2, 3]
    assert [lg_round(Fraction(t), False) for t in (1, 2, 3, "1/3", "1/4")] == [0, 1, 1, -2, -2]
    # e lowered by 5 below 1 (at the parallel sum 4/7): e_- = -2 > -5 + ceil(lg 3) = -3
    assert check(paper, "lem:f", dict(row, e=lambda x: e(x) - 5 if x < 1 else e(x)))["items"]["masses"] == "fails"
    # a set of integers, a family over it, a function declared in the item
    rk = {"cal_K": [0, 2], "theta[]": {0: 1, 2: 0}, "k_star": 2, "theta": lambda k: k + 1}
    assert check(paper, "lem:k", rk)["items"] == {"(1)": "holds"}
    assert check(paper, "lem:k", dict(rk, theta=lambda k: k - 3))["items"] == {"(1)": "vacuous"}  # theta(0) < 1


def test_signs_intervals_sets_and_least_on_rows():
    """qpp/tests/fixtures/review.tex on rows: half-open intervals, the signs of an orthant, a listing, a relation
    symbol by its row, a context row read whole, the least element of a set, a conditioned sum, a count"""
    paper = Q.read_qpp((REPO / "qpp" / "tests" / "fixtures" / "review.qpp").read_text(encoding="utf-8"))
    row = {"n": 2, "rho": "1/2", "x": 1, "y": 0, "u": ["3/4", 1]}
    assert check(paper, "lem:halfopen", row) == {"given": True, "items": {"(1)": "holds"}, "flags": []}
    assert check(paper, "lem:halfopen", dict(row, x=0))["given"] is False          # 0 is not in (0, 1]
    assert check(paper, "lem:halfopen", dict(row, y=1))["given"] is False          # 1 is not in [0, 1)
    assert check(paper, "lem:halfopen", dict(row, u=["1/2", 1]))["given"] is False  # 1/2 is not in (1/2, 1]
    assert check(paper, "lem:halfopen", dict(row, rho=2))["given"] is False        # the context row, whole
    assert check(paper, "lem:pm", {"P_plus": 2, "P_minus": 1})["items"] == {"(1)": "holds"}
    assert check(paper, "lem:pm", {"P_plus": 2, "P_minus": -1})["given"] is False  # P_- >= 0, the second reading
    assert check(paper, "lem:preceq", {"x": 1, "y": 1, "z": 1})["items"] == {"(1)": "holds"}
    assert check(paper, "lem:preceq", {"x": 3, "y": 1, "z": 1})["given"] is False  # x preceq y is x <= 2y
    assert check(paper, "lem:context", {"n": 3, "rho": "1/2"})["items"] == {"(1)": "holds"}
    sets = {"n": 2, "rho": 1, "N": 3, "a[]": [1, 1, 1], "g[]": [-1, 2, 3], "s[]": [1, -1, 1], "varsigma": [1, -1],
            "z": [2, -3], "m": 2, "j": 2}
    r = check(paper, "lem:sets", sets)
    assert r["given"] is True and r["items"] == {k: "holds" for k in ("(1)", "(2)", "(3)", "(4)", "(5)")}
    assert check(paper, "lem:sets", dict(sets, m=3))["given"] is False             # 3 is not in {1, 2}
    assert check(paper, "lem:sets", dict(sets, varsigma=[1, 0]))["given"] is False  # not a sign
    assert check(paper, "lem:sets", dict(sets, z=[2, "1/2"]))["given"] is False    # not in Z^n
    # (2): k = 2 is the least index with g_k >= 0, and the count of such indices is 2; with g_N < 0 the part is vacuous
    assert check(paper, "lem:sets", {**sets, "g[]": [-1, -2, -3]}, only=["(2)"])["items"] == {"(2)": "vacuous"}
    # (4): a_j <= m for every j (bound at the hypothesis) fails at a_3 = 5, so the part is vacuous, not a failure
    assert check(paper, "lem:sets", {**sets, "a[]": [1, 1, 5]}, only=["(4)"])["items"] == {"(4)": "vacuous"}
    assert check(paper, "lem:sets", dict(sets, j=3), only=["(5)"])["items"] == {"(5)": "vacuous"}  # j in {1..n}
    # the least element and the count as values: on the row, {k : g_k >= 0} = {2, 3}
    env = Env(paper["vocab"], sets, {})
    assert all(context(p, env) for p in T.parse_qpp_item("N in ZZ>=1, g_(1..N) in QQ"))
    assert value(T.parse_qpp("min {k : g_(k) >= 0}"), env) == 2 and value(T.parse_qpp("card({k : g_(k) >= 0})"), env) == 2
    assert value(T.parse_qpp("sum k with g_(k) > 0, g_(k)"), env) == 5
    assert value(T.parse_qpp("card({1..N} minus {1, 2})"), env) == 1


def test_a_spec_over_q_is_sampled():
    """the spec of a function the row gives, forall x in Q>0 : 2^(-e(x)-1) < x <= 2^(-e(x)), in the context or in the
    given, is checked at the sample points of the fixture (undecided without them)"""
    def exact_e(x):
        k = 0
        while Fraction(2) ** (-k) < x:
            k -= 1
        while Fraction(2) ** (-k - 1) >= x:
            k += 1
        return k
    for where in ("context e in (QQ>0 -> ZZ), forall x in QQ>0 : 2^(-e(x) - 1) < x <= 2^(-e(x))\n"
                  "lemma lem:s\n  given: y in QQ>0\n",
                  "lemma lem:s\n  given: e in (QQ>0 -> ZZ), (forall x in QQ>0 : 2^(-e(x) - 1) < x <= 2^(-e(x))), "
                  "y in QQ>0\n"):
        paper = "paper T\n" + where + "  (1): y <= 2^(-e(y))\n"
        row = {"e": exact_e, "y": "3/5"}
        assert check(paper, "lem:s", row)["given"].startswith("undecided")
        r = check(paper, "lem:s", row, {"x": ["1/3", "1/2", 1, "7/4", 5]})
        assert r["items"] == {"(1)": "holds"} and "sampled x in QQ>0 at 5 points" in r["flags"]
        wrong = check(paper, "lem:s", {"e": lambda x: 0, "y": "3/5"}, {"x": ["1/3", 1]})
        assert wrong["given"] is False                                           # e = 0 is not the exponent


def test_positive_parts_and_indicators_are_read_on_rows():
    """(x-t)_+ is max(x - t, 0) and \\mathbf 1[P] is 1 or 0 as P holds: both are decided on a row"""
    from qpp import latex2qpp
    tex = (r"\begin{lemma}\label{lem:r}x\begin{stmt}\sit{given}{x,t\in\Q}"
           r"\sit{(1)}{(x-t)_+^2=(x-t)^2\mathbf 1[x>t]}\sit{(2)}{(x-t)_+=0}\end{stmt}\end{lemma}")
    text, _ = latex2qpp.convert(tex, "R")
    assert "  (1): max(x - t, 0)^2 = (x - t)^2 * iverson(x > t)\n" in text
    assert check(text, "lem:r", {"x": 3, "t": 1})["items"] == {"(1)": "holds", "(2)": "fails"}
    assert check(text, "lem:r", {"x": "1/2", "t": 1})["items"] == {"(1)": "holds", "(2)": "holds"}
