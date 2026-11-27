"""qpp2lean: a Q++ file (.qpp) to a Lean file that imports qpp/lean/QPP.lean.

A result is generated when its statement and its proof are formal (no hole) and in the fragment below; every other
result is listed in a comment with the reason, so the generated file always compiles or fails on a real error, and
never contains `sorry`.

Statements (qpp/README.md, "The LaTeX form"):
* the items of `given` are declarations and hypotheses, in order: `x, u, v in QQ` declares three rationals,
  `a in QQ>=0` a rational with the hypothesis 0 <= a, `N in NN` a natural number, `a_(i) in QQ` a sequence NN -> QQ;
  every other item is a hypothesis, a chain a <= b <= c gives one hypothesis per link, and the hypotheses are
  named h_1, h_2, ... in order (in Lean with subscript digits), then the hypotheses of an implication in a
  conclusion; an index that is not declared is universally quantified;
* the items (1), (2), ... are the conclusions, in order, and the result proves their conjunction; when an item has
  a hole, each conclusion is its own statement with the given clauses (lem_x.item_1.statement, theorem
  lem_x.item_1), and only the items with a hole, or that use a name of another item, are not generated;
* a name with a numeric subscript, f_0, is the member f_(0) of a family or sequence f declared in the result.
Proofs: the line of item (k) proves conclusion (k). Data that are propositions are claims, proved first (`have`,
in the order of the word read forward, by the factor that carries them, in the search mode `qpp!`); other data
are certificates, checked in the strict mode `qpp`. A relation in parentheses in the data cites a hypothesis by
its content: eq[(x preceq y) + 2 * (y preceq z)] is eq[h_1 + 2 * h_2]; a citation that matches no hypothesis
is an error. A claim that names what the statement does not declare (a variable of the proof), or ind_x without
the word it runs, is not generated (Lean could not read it).

The match check (--match LEAN_DIR --import LIB): for each formal statement whose label tags a declaration of the
hand-written library, `example (hc_1 : X) : lem_x.statement` proved by applying the declaration; the cited facts X
that the declaration takes (structures X : Prop with no parameters) are hypotheses of the example.

The generator (--kernel): a Q++ 0.2 source to Lean, its Mathlib reading, with Lean errors at their Q++ lines
(--check); qpp/kernel.py.

Usage: python3 -m qpp.qpp2lean IN.qpp [-o OUT.lean] [--namespace NS]
       python3 -m qpp.qpp2lean IN.qpp --match LEAN_DIR [--import LIB] [-o OUT.lean]
       python3 -m qpp.qpp2lean IN.qpp --kernel -o OUT.lean [--check]
"""
import re
import sys
from pathlib import Path

from qpp import texmath as T


class Skip(Exception):
    """the result is outside the generated fragment"""


def read_qpp(text):
    """{'paper', 'aliases': [(name, word)], 'results': [{'kind','label','items':[(key, q)], 'lines':[(item, w)]}]}"""
    out = {"paper": "", "aliases": [], "results": [], "vocab": {}}
    cur, mode = None, None
    byl = {}
    for raw in text.splitlines():
        if not raw.strip() or raw.startswith("--"):
            continue
        if raw.startswith("paper "):
            out["paper"] = raw.split(None, 1)[1].strip()
        elif raw.startswith("word "):
            w, _, meaning = raw[5:].partition(" := ")
            w = w.strip().replace("_", " ")
            meaning = meaning.strip()
            out["vocab"][w] = ({"lean": meaning[5:].strip()} if meaning.startswith("lean ")
                               else {"set": T.parse_qpp(meaning)})
        elif raw.startswith("context "):
            out["vocab"].setdefault("#context", []).extend(T.parse_qpp_item(raw[8:].strip()))
        elif raw.startswith("define "):
            # an operator of the paper, defined once (a par b := (a^(-1) + b^(-1))^(-1)): every statement expands it
            out["vocab"].setdefault("#opdef", []).extend(T.parse_qpp_item(raw[7:].strip()))
        elif raw.startswith("relation "):
            out["vocab"].setdefault("#rel", []).append(T.parse_qpp_item(raw[9:].strip())[0])
        elif raw.startswith("alias "):
            name, _, w = raw[6:].partition(" := ")
            out["aliases"].append((name.strip(), w.strip()))
        elif not raw.startswith(" "):
            kind, label = raw.split(None, 1)
            label = label.strip()
            if kind == "proof":
                cur = byl.get(label)
                if cur is None:
                    cur = {"kind": "proof", "label": label, "items": [], "lines": []}
                    byl[label] = cur
                    out["results"].append(cur)
                mode = "proof"
            else:
                cur = {"kind": kind, "label": label, "items": [], "lines": []}
                byl[label] = cur
                out["results"].append(cur)
                mode = "stmt"
        else:
            body = raw.strip()
            if mode == "stmt" and body.startswith("fix "):
                # fix KEY FID: the key may hold spaces (core 0, site loss), the fixture id does not
                key, fid = body[4:].strip().rsplit(None, 1)
                cur.setdefault("fixes", []).append((None if key == "*" else key, fid.strip()))
                continue
            if mode == "stmt":
                key, _, q = body.partition(": ")
                cur["items"].append((key.strip(), q.strip()))
            else:
                m = re.match(r"^(\([^()\s]*\))\s+(.*)$", body)
                cur["lines"].append((m.group(1), m.group(2)) if m else ("", body))
    return out


def lean_ident(label):
    return re.sub(r"[^A-Za-z0-9_]", "_", label)


# ---------------------------------------------------------------------------------------------------------
# statements

def kids(x):
    """the subterms of a node (a node starts with its kind); a tuple of nodes is its own list of subterms"""
    if not isinstance(x, tuple) or not x:
        return ()
    return x[1:] if isinstance(x[0], str) else x


def seq_key(name):
    """the scope key of a sequence a_i (a scalar a may share the letter)"""
    return name + "[]"


BUILTIN_FUNS = {("var", "lg"), ("var", "card"), ("var", "min"), ("var", "max"), ("var", "deg"), ("var", "choose"),
                ("var", "transpose"), ("var", "det"), ("var", "tr"), ("var", "jac")} | {("var", f) for f in T.BUILTIN_LEAN}
# lg: in a ceiling or a floor (Nat.clog 2, Nat.log 2); card: Set.ncard; min, max: Lean's, two arguments at a time


def builder_names(b):
    """the names a set builder {t : D} or {x in S : P} binds: those D declares (or x)"""
    if b[0] != "such":
        return set()
    head, cond = b[1], b[2]
    if head[0] == "var":
        return {head[1]}
    if head[0] == "rel" and head[1] == ("in",) and head[2][0][0] == "var":
        return {head[2][0][1]}
    out = set()
    for c in flatten(cond):
        if c[0] == "decl":
            out.update(n[1] if n[0] in ("var", "family") else n[1][1] for n in c[1])
        elif c[0] == "def" and c[1][0] == "var":
            out.add(c[1][1])
    return out


def free_vars(x, acc=None):
    """the free names of a term; a sequence a_i counts as a[]"""
    acc = set() if acc is None else acc
    if not isinstance(x, tuple) or not x:
        return acc
    if x[0] == "var":
        acc.add(x[1])
        return acc
    if x[0] == "app" and x[3] == "call" and x[1] == ("var", "int") and len(x[2]) == 4 and x[2][1][0] == "var":
        inner = set()  # int(g, mu, a, b): mu is bound by the integral
        for y in x[2]:
            free_vars(y, inner)
        inner.discard(x[2][1][1])
        acc |= inner
        return acc
    if x[0] == "app" and x[3] == "call" and x[1] == ("var", "int") and len(x[2]) == 2:
        return free_vars(x[2][0], acc)  # int(g, q): q is the law, named by a binding
    if x[0] == "app" and x[3] == "call" and x[1] in BUILTIN_FUNS:
        for y in x[2]:
            free_vars(y, acc)
        return acc
    if x[0] == "app" and x[3] == "call" and op_with_variable(x):
        # deg_y S, Res_y(S, T), deriv(g, y, k): the variable y is the polynomials' formal variable, not a name
        for y in (x[2] if x[1][0] == "app" else x[2][:1] + x[2][2:]):
            free_vars(y, acc)
        return acc
    if x[0] == "family":
        acc.add(seq_key(x[1]))
        free_vars(x[2], acc)
        free_vars(x[3], acc)
        return acc
    if x[0] == "app" and x[3] == "idx" and x[1][0] == "var":
        acc.add(seq_key(x[1][1]))
        free_vars(x[2], acc)
        return acc
    if x[0] in ("sum", "prod", "max", "min", "par", "union", "inter", "oplus", "comp"):
        inner = set()
        for y in x[2:]:
            free_vars(y, inner)
        inner.discard(x[1])
        inner.discard(seq_key(x[1][2:]) if x[1].startswith("b_") else None)  # the components of a bound vector
        acc |= inner
        return acc
    if x[0] == "setof" and x[1][0] == "such":
        inner = set()
        free_vars(x[1][1], inner)
        free_vars(x[1][2], inner)
        bound = builder_names(x[1])
        acc |= {n for n in inner if n not in bound and not (n.endswith("[]") and n[:-2] in bound)}
        return acc
    for y in kids(x):
        free_vars(y, acc)
    return acc


def op_with_variable(x):
    """an application of an operator with a formal variable: deg_(y)(S), lc_(y)(S), Res_(y)(S, T), deriv(g, y, k)"""
    return (x[1][0] == "app" and x[1][3] == "idx" and x[1][1][0] == "var" and x[1][1][1] in T.POLY_OPS) or \
        x[1] == ("var", "deriv")


def free_names(t, bound=frozenset(), acc=None):
    """the names free in t, scoped: a big operator binds its index in its range and body, a quantifier its names in
    its body, a set builder the names it declares, an implication the names its hypotheses declare"""
    acc = set() if acc is None else acc
    if not isinstance(t, tuple) or not t:
        return acc
    k = t[0]
    if k == "var":
        if t[1] not in bound:
            acc.add(t[1])
        return acc
    if k == "app" and t[3] == "call" and t[1] == ("var", "int") and len(t[2]) == 4 and t[2][1][0] == "var":
        for y in t[2]:
            free_names(y, bound | {t[2][1][1]}, acc)  # int(g, mu, a, b): mu is bound by the integral
        return acc
    if k == "app" and t[3] == "call" and op_with_variable(t):
        # deg_y S, deriv(g, y, k): the formal variable is not a name of the statement
        for y in (t[2] if t[1][0] == "app" else t[2][:1] + t[2][2:]):
            free_names(y, bound, acc)
        return acc
    if k in ("sum", "prod", "max", "min", "par", "union", "inter", "oplus", "comp"):
        inner = bound | {t[1]}
        for y in t[2:]:
            free_names(y, inner, acc)
        return acc
    if k in ("exists", "forall"):
        if t[2] is not None:
            free_names(t[2], bound, acc)
        free_names(t[3], bound | {v[1] for v in t[1] if v[0] == "var"}, acc)
        return acc
    if k == "setof" and t[1][0] == "such":
        inner = bound | builder_names(t[1])
        free_names(t[1][1], inner, acc)
        free_names(t[1][2], inner, acc)
        return acc
    if k in ("imp", "ctx"):
        inner = bound | declared_in(t)
        free_names(t[1], inner, acc)
        free_names(t[2], inner, acc)
        return acc
    if k == "decl":
        # the index in a declared name b_j is the pattern of the family, not a name of the statement
        for n in t[1]:
            if n[0] == "family":
                free_names(n[2], bound, acc)
                free_names(n[3], bound, acc)
        free_names(t[2], bound, acc)
        return acc
    if k == "app" and t[3] == "idx" and t[1][0] == "var":
        for a in t[2]:
            free_names(a, bound, acc)
        return acc
    for y in kids(t):
        free_names(y, bound, acc)
    return acc


def free_index_vars(t, bound=frozenset(), acc=None):
    """the names used as indices a_(i) in t that no binder of t binds (scoped, as free_names)"""
    acc = set() if acc is None else acc
    if not isinstance(t, tuple) or not t:
        return acc
    k = t[0]
    if k in ("sum", "prod", "max", "min", "par", "union", "inter", "oplus", "comp"):
        inner = bound | {t[1]}
        for y in t[2:]:
            free_index_vars(y, inner, acc)
        return acc
    if k in ("exists", "forall"):
        if t[2] is not None:
            free_index_vars(t[2], bound, acc)
        free_index_vars(t[3], bound | {v[1] for v in t[1] if v[0] == "var"}, acc)
        return acc
    if k == "setof" and t[1][0] == "such":
        inner = bound | builder_names(t[1])
        free_index_vars(t[1][1], inner, acc)
        free_index_vars(t[1][2], inner, acc)
        return acc
    if k in ("imp", "ctx"):
        inner = bound | declared_in(t)
        free_index_vars(t[1], inner, acc)
        free_index_vars(t[2], inner, acc)
        return acc
    if k == "decl":
        for n in t[1]:
            if n[0] == "family":
                free_index_vars(n[2], bound, acc)
                free_index_vars(n[3], bound, acc)
        free_index_vars(t[2], bound, acc)
        return acc
    if k == "app" and t[3] == "idx" and t[1][0] == "var" and t[1][1] in T.POLY_OPS:
        return acc  # deg_(y): the formal variable, not an index
    if k == "app" and t[3] == "idx":
        for a in t[2]:
            if a[0] == "var" and a[1] not in bound:
                acc.add(a[1])
    for y in kids(t):
        free_index_vars(y, bound, acc)
    return acc


def prefix_indices(t, in_scope):
    """the free indices of t quantified in front of t: those free in two or more of its parts (the hypothesis and
    the conclusion of an implication, the sides of or and iff, the clauses of a list); an index free in one part
    only is quantified there, at the smallest clause that holds all its occurrences. So a_i <= x => sum_j a_j <= N x
    reads (forall i, a_i <= x) => ..., and a_i <= a_k => a_k <= s reads forall k, ((forall i, a_i <= a_k) => a_k <= s).
    An index meant as a parameter of the whole statement is declared (1 <= k <= N) or used on both sides."""
    idx = free_index_vars(t) - set(in_scope)
    parts = (t[1], t[2]) if t[0] in ("imp", "ctx", "or", "iff") else t[1] if t[0] == "and" else None
    if parts is not None:
        counts = [free_names(p) for p in parts]
        if t[0] in ("imp", "ctx"):
            for i in sorted(i for i in idx if i in counts[0] and i not in counts[1]):
                STMT_WARN.append(f"the index {i} occurs only in a hypothesis, so it reads 'for every {i}' there "
                                 f"(a weaker statement if {i} is a parameter: declare it, or write the range)")
        idx = {i for i in idx if sum(i in names for names in counts) >= 2}
    return sorted(idx)


STMT_WARN = []  # the warnings of the statement being read (style; the statement is generated as it reads)
STMT_DROPPED = []  # the clauses of the given with a hole that the statement being read leaves out (their LaTeX)


def split_parts(q, sep=";"):
    """the parts of an item in Q++, split at the separators outside braces, brackets and parentheses (a hole
    ?{...} is one piece)"""
    out, depth, cur = [], 0, []
    for ch in q:
        if ch in "{[(":
            depth += 1
        elif ch in "}])":
            depth -= 1
        if ch == sep and depth == 0:
            out.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    out.append("".join(cur).strip())
    return [x for x in out if x]


def tex_bases(tex):
    """the letters a clause in LaTeX mentions, as bases of names (a for a_h, \\ba, a^0; beta for \\beta'_0), words in
    \\text and references left out"""
    t = re.sub(r"\\(?:text|textup|emph|cref|Cref|ref|eqref|cite|label)\s*\{[^{}]*\}", " ", tex)
    out = set()
    for m in re.finditer(r"\\([A-Za-z]+)|([A-Za-z])", t):
        c, letter = m.group(1), m.group(2)
        if letter:
            out.add(letter)
        elif c in T.GREEK:
            out.add(c)
        elif c in T.BOLD_CMDS and T.BOLD_CMDS[c] != "b_one":
            out.add(key_base(T.BOLD_CMDS[c]))  # \bd is the vector b_delta
        elif c[0] == "b" and (len(c) == 2 or c[1:] in T.GREEK):
            out.add(c[1:])  # \ba, \btheta: the vector of the letter
    return out


def with_vectors(keys):
    """the keys with their vector and family spellings: the components a_(h) of the vector b_a are one object"""
    out = set(keys)
    for k in keys:
        if k.startswith("b_"):
            out.add(seq_key(k[2:]))
        elif k.endswith("[]"):
            out.add("b_" + k[:-2])
    return out


def defined_keys(c):
    """the name a definition clause defines (x := t, a_(i) := t, f(y) := t)"""
    if c[0] == "def" and c[1][0] == "app" and c[1][1][0] == "var":
        return {seq_key(c[1][1][1]) if c[1][3] == "idx" else c[1][1][1]}
    if c[0] == "def" and c[1][0] == "var":
        return {c[1][1]}
    return set()


def key_base(k):
    """the base of a name in scope: a for a[], b_a, a_star; n for n_y; beta for beta'"""
    m = re.match(r"(?:b_)?([A-Za-z]+)", k)
    return m.group(1) if m else k


def minmax_in(t):
    """a min or a max (a fold or a call) somewhere in t"""
    if not (isinstance(t, tuple) and t):
        return False
    if isinstance(t[0], str):
        if t[0] in ("min", "max") and len(t) == 4 and isinstance(t[1], str):
            return True
        if t[0] == "app" and t[1] in (("var", "min"), ("var", "max")):
            return True
        return any(minmax_in(y) for y in t[1:])
    return any(minmax_in(y) for y in t)


def index_vars(x, acc=None):
    """variables used as indices a_(i)"""
    acc = set() if acc is None else acc
    if not isinstance(x, tuple) or not x:
        return acc
    if x[0] == "app" and x[3] == "idx" and x[1][0] == "var" and x[1][1] in T.POLY_OPS:
        return acc  # deg_(y): the formal variable, not an index
    if x[0] == "app" and x[3] == "idx":
        for a in x[2]:
            if a[0] == "var":
                acc.add(a[1])
    for y in kids(x):
        index_vars(y, acc)
    return acc


SET_TYPES = {"QQ": "\u211a", "ZZ": "\u2124", "NN": "\u2115"}
TYPE_RANK = {"\u2115": 0, "\u2124": 1, "\u211a": 2}


class Env:
    """the variables in scope: Q++ name -> {'lean', 'type', 'seq', 'fam'} (fam: the index range (lo, hi) of a
    family a_1,...,a_N), with the paper's vocabulary"""

    def __init__(self, vocab, parent=None):
        self.vocab = vocab
        self.vars = dict(parent.vars) if parent else {}

    def child(self):
        return Env(self.vocab, self)

    def lean(self, name):
        v = self.vars.get(name)
        return v["lean"] if v else T.lean_name(name)


def term_type(t, env):
    """the Lean type of a term: an interval of vectors is a set of vectors; a name has its declared type"""
    if t[0] == "interval" and t[3] is None:
        a = term_type(t[1], env)
        return f"Set ({a})" if " " in a else f"Set {a}"
    if t[0] == "var" and t[1] in env.vars:
        return env.vars[t[1]]["type"]
    return infer_type(t, env)


def set_info(s, env, x):
    """(Lean type or None, [hypotheses on x]) for x in the set s"""
    if s[0] == "set" and s[1][:2] in SET_TYPES:
        typ = SET_TYPES[s[1][:2]]
        m = re.fullmatch(r"(?:QQ|ZZ|NN)(>=|>)(\d+)", s[1])
        hyps = []
        if m:
            rel = "\u2264" if m.group(1) == ">=" else "<"
            hyps.append(f"{m.group(2)} {rel} {x}")
        elif s[1][2:]:
            raise Skip(f"set {s[1]}")
        return typ, hyps
    if s[0] == "setfrom":
        # Z_{>= M_0}: the members of Z (N, Q) from a bound that is a term
        with names(env):
            b = T.to_lean(s[3], 3)
        rel = "\u2264" if s[2] == ">=" else "<"
        return SET_TYPES[s[1]], [f"{b} {rel} {x}"]
    if s[0] == "word":
        v = env.vocab.get(s[1])
        if v is None:
            raise Skip(f"word {s[1]} is not in the vocabulary")
        if "lean" in v:
            return None, [f"{v['lean']} {x}"]
        return set_info(v["set"], env, x)
    if s[0] == "fun":
        # F : S -> T, a total Lean function; the bounds of S and T are a hypothesis for every t of S
        t = "t" if "t" not in x else "t\u2080"
        dt, dh = set_info(s[1], env, t)
        ct, ch = set_info(s[2], env, f"{x} {t}")
        if dt is None or ct is None:
            raise Skip(f"a function into or from {T.to_qpp(s)} (no Lean type yet)")
        typ = f"({dt}) \u2192 {ct}" if "\u2192" in dt else f"{dt} \u2192 {ct}"
        hyps = []
        if ch:
            body = conj(ch)
            hyps.append(f"\u2200 {t} : {dt}, " + "".join(h + " \u2192 " for h in dh) + body)
        return typ, hyps
    if s[0] == "pow" and s[2][0] == "bin" and s[2][1] == "times" and s[1][0] == "set" and s[1][1] in SET_TYPES:
        # Q^{m x n}: the matrices with m rows and n columns
        with names(env):
            m, n = T.to_lean(s[2][2], 9), T.to_lean(s[2][3], 9)
        return f"Matrix (Fin {m}) (Fin {n}) {SET_TYPES[s[1][1]]}", []
    if s[0] == "pow":
        # S^n: vectors indexed by Fin n (an integer dimension n is read through n.toNat), each component in S
        elem, hs = set_info(s[1], env, "\u00a7")
        if elem is None:
            raise Skip(f"vectors over {T.to_qpp(s[1])} (no type)")
        with names(env):
            dim = T.to_lean(s[2], 9)
        if s[2][0] == "var" and env.vars.get(s[2][1], {}).get("type") == "\u2124":
            dim = f"{dim}.toNat"
        typ = f"Fin {dim} \u2192 {elem}"
        if not hs:
            return typ, []
        i = "i" if x != "i" else "j"
        at = f"({x}) {i}" if " " in x else f"{x} {i}"
        return typ, [f"\u2200 {i} : Fin {dim}, " + conj([h.replace("\u00a7", at) for h in hs])]
    if s[0] == "interval":
        lo, hi = s[1], s[2]
        if s[3] is not None:
            lo, hi = ("bin", "*", lo, s[3]), ("bin", "*", hi, s[3])
        with names(env):
            return "\u211a", [f"{T.to_lean(lo, 3)} \u2264 {x}", f"{x} \u2264 {T.to_lean(hi, 3)}"]
    if s[0] == "ivl":
        # a half-open interval (a, b] or [a, b)
        lo_rel, hi_rel = ("<", "\u2264") if s[1] == "oc" else ("\u2264", "<")
        with names(env):
            return "\u211a", [f"{T.to_lean(s[2], 3)} {lo_rel} {x}", f"{x} {hi_rel} {T.to_lean(s[3], 3)}"]
    if s[0] == "intrange":
        # the integers from a to b
        typ = "\u2115" if all(infer_type(b, env) == "\u2115" for b in (s[1], s[2])) else "\u2124"
        with names(env):
            return typ, [f"{T.to_lean(s[1], 3)} \u2264 {x}", f"{x} \u2264 {T.to_lean(s[2], 3)}"]
    if s[0] == "setlist":
        # a listing {a, b}: x is one of them
        typ = max((infer_type(a, env) for a in s[1]), key=lambda t: TYPE_RANK[t])
        return typ, [" \u2228 ".join(f"{x} = {term(a, env, 3)}" for a in s[1])]
    if s[0] == "bin" and s[1] in ("cap", "cup", "minus"):
        t1, h1 = set_info(s[2], env, x)
        t2, h2 = set_info(s[3], env, x)
        typ = t1 or t2
        if s[1] == "cap":
            return typ, h1 + h2
        if s[1] == "cup":
            return typ, [f"({conj(h1)}) \u2228 ({conj(h2)})"] if h1 and h2 else []
        return typ, h1 + ([f"\u00ac ({conj(h2)})"] if h2 else [f"False"])
    if s[0] == "setof" and s[1][0] in ("var", "app", "tuple", "num") and not T.is_prop(s[1]):
        # a singleton {t}
        return term_type(s[1], env), [f"{x} = {term(s[1], env)}"]
    if s[0] == "setof" and s[1][0] == "such":
        head, cond = s[1][1], s[1][2]
        if head[0] == "rel" and head[1] == ("in",) and is_name_node(head[2][0]) and head[2][0][0] == "var":
            # {v in X : P}: x in X and P at v = x
            typ, hs = set_info(head[2][1], env, x)
            local = env.child()
            local.vars[head[2][0][1]] = {"lean": x if " " not in x else f"({x})", "type": typ}
            return typ, hs + [lean_prop(cond, local)]
        # {t : D}: some names declared by D, with the conditions of D, give x = t (D's names are bound here:
        # a name of the statement that D declares again, or that the head alone binds, is renamed); a free index
        # of a family in t or D is an existential binder over its range ({a_h : a_h > 0} is the a_h with a_h > 0)
        local = env.child()
        ren = {}
        bound = builder_names(s[1])
        for n in sorted(bound):
            if n in env.vars or T.lean_name(n) in x:
                m = n + "'"
                while m in env.vars or m in bound:
                    m += "'"
                ren[n] = ("var", m)
        if ren:
            head, cond = subst(head, ren), subst(rename_components(cond, ren), ren)
        b2, h2 = [], []
        declared = builder_names(("such", ("tuple", ()), cond))
        free = (free_index_vars(head) | free_index_vars(cond)) - set(env.vars) - declared
        if head[0] == "var" and head[1] not in env.vars and head[1] not in declared:
            free.add(head[1])  # {k : P}: k itself, an index of a family (so a count), or else of no type
        for i in sorted(free):
            rng = family_range_of(cond, i, env) or family_range_of(head, i, env)
            ln = T.lean_name(i)
            local.vars[i] = {"lean": ln, "type": "\u2115"}
            b2.append((ln, "\u2115"))
            if rng:
                h2 += [f"{term(rng[0], env, 3)} \u2264 {ln}", f"{ln} \u2264 {term(rng[1], env, 3)}"]
        for c in flatten(cond):
            lean_hyp(c, local, b2, h2)
        typ = term_type(head, local)
        eq = f"{x} = {term(head, local)}"
        bs = " ".join(f"({n} : {t})" for n, t in group_binders(b2))
        return typ, [f"\u2203 {bs}, " + conj(h2 + [eq]) if bs else conj(h2 + [eq])]
    if s[0] == "var" and s[1] in env.vars:
        t = env.vars[s[1]]["type"]
        return (t[4:].strip("()") if t.startswith("Set ") else None), [f"{x} \u2208 {env.lean(s[1])}"]
    if s[0] == "polyring" and s[1][0] == "set" and s[1][1] in SET_TYPES and len(s[2]) == 1 and s[2][0][0] == "var" \
            and not s[2][0][1].startswith("b_"):
        # S in Q[y]: a polynomial in one variable (Mathlib's Polynomial; y is its formal variable, not a name of the
        # statement)
        return f"Polynomial {SET_TYPES[s[1][1]]}", []
    if s[0] == "polyring" and s[1][0] == "set" and s[1][1] in SET_TYPES and len(s[2]) == 1 and s[2][0][0] == "var":
        # Q[w], w a declared vector of dimension d: polynomials in d variables (MvPolynomial (Fin d) Q)
        d = vec_dim(env.vars.get(s[2][0][1], {}).get("type"))
        if d is None:
            raise Skip(f"a ring of polynomials in {s[2][0][1]}, a vector whose dimension is not declared before it")
        return f"MvPolynomial (Fin {d}) {SET_TYPES[s[1][1]]}", []
    if s[0] == "polyring" and s[1][0] == "polyring" and len(s[2]) == 1 and s[2][0][0] == "var":
        # S in Q[w][y]: a polynomial in y with coefficients in Q[w]
        inner, _ = set_info(s[1], env, x)
        return f"Polynomial ({inner})", []
    if s[0] == "app" and s[1] == ("var", "interior") and len(s[2]) == 1 and s[2][0][0] == "interval" \
            and s[2][0][3] is None:
        # the interior of [a, b]: a < x < b (for vectors, in every component)
        typ, _ = set_info(s[2][0], env, x)
        lo, hi = term(s[2][0][1], env, 3), term(s[2][0][2], env, 3)
        if typ == "\u211a":
            return typ, [f"{lo} < {x}", f"{x} < {hi}"]
        raise Skip("the interior of a box of vectors in a declaration (no Lean form yet)")
    if s[0] == "app" and s[1] == ("var", "powerset") and len(s[2]) == 1:
        # P(S): the subsets of S
        elem, _ = set_info(s[2][0], env, "\u00a7")
        if elem is None:
            raise Skip(f"the subsets of {T.to_qpp(s[2][0])} (no element type)")
        typ = f"Set ({elem})" if " " in elem else f"Set {elem}"
        if s[2][0][0] in ("set", "pow") and s[2][0][1] != ("set", "empty"):
            return typ, []
        return typ, [f"{x} \u2286 {term(s[2][0], env, 9)}"]
    if s[0] == "units":
        # Q^x: the nonzero elements
        typ, hs = set_info(s[1], env, x)
        return typ, hs + [f"{x} \u2260 0"]
    if s[0] == "bin" and s[1] == "*" and s[3][0] == "set" and s[3][1] in ("ZZ", "NN"):
        # (1/N) Z: the multiples of 1/N by an integer
        n = "n" if "n" not in x else "n\u2080"
        return "\u211a", [f"\u2203 {n} : {SET_TYPES[s[3][1]]}, {x} = {term(s[2], env, 4)} * {n}"]
    raise Skip(f"set {T.to_qpp(s)} (no Lean type yet)")


class names:
    """the Lean names and family ranges of the environment, for the term printer"""

    def __init__(self, env):
        self.env = env

    def __enter__(self):
        self.saved = (dict(T.LEAN_NAMES), dict(T.LEAN_FAMS), dict(T.LEAN_VECS), dict(T.LEAN_FIN), dict(T.LEAN_ITYP),
                      dict(T.LEAN_PVAR), set(T.LEAN_INT), set(T.LEAN_RAT), set(T.LEAN_POLY), set(T.LEAN_MATS))
        T.LEAN_PVAR.clear()
        T.LEAN_MATS.clear()
        T.LEAN_NAMES.clear()
        T.LEAN_POLY.clear()
        T.LEAN_RAT.clear()
        T.LEAN_FAMS.clear()
        T.LEAN_INT.clear()
        T.LEAN_VECS.clear()
        T.LEAN_FIN.clear()
        T.LEAN_ITYP.clear()
        for n, v in self.env.vars.items():
            T.LEAN_NAMES[n] = v["lean"]
            if v.get("type") == "\u2124":
                T.LEAN_INT.add(n)
            if (v.get("type") or "").startswith("Polynomial "):
                T.LEAN_POLY.add(n)
                T.LEAN_PVAR[n] = (v.get("pvar"), v["type"])
            if (v.get("type") or "").startswith("Matrix "):
                T.LEAN_MATS.add(n)
            if (v.get("elem") or (v.get("type") or "").rsplit("\u2192 ", 1)[-1]) == "\u211a":
                T.LEAN_RAT.add(n)  # a rational scalar, a family a[] or vector b_x of rationals, a map into Q
            if v.get("fam"):
                T.LEAN_FAMS[n[:-2]] = v["fam"]
            if v.get("seq"):
                T.LEAN_ITYP[n[:-2]] = v.get("ityp", "\u2115")
            if v.get("fin"):
                T.LEAN_FIN[n] = v["fin"]
            if n.startswith("b_") and vec_dim(v.get("type")) and seq_key(n[2:]) not in self.env.vars:
                T.LEAN_VECS[n[2:]] = (v["lean"], vec_dim(v["type"]))

    def __exit__(self, *a):
        for g, old in zip((T.LEAN_NAMES, T.LEAN_FAMS, T.LEAN_VECS, T.LEAN_FIN, T.LEAN_ITYP, T.LEAN_PVAR, T.LEAN_INT,
                           T.LEAN_RAT, T.LEAN_POLY, T.LEAN_MATS), self.saved):
            g.clear()
            g.update(old)


def term(x, env, p=0):
    with names(env):
        return T.to_lean(x, p)


def declare(env, node, s, binders, hyps):
    """declare the name node (x, a_i or a_1..a_N) in the set s: binders [(lean, type)], hypotheses [str]"""
    if node[0] == "var":
        name, seq, fam = node[1], False, None
    elif node[0] == "family":
        name, seq, fam = node[1], True, (node[2], node[3])
    elif node[0] == "app" and node[3] == "idx" and node[1][0] == "var":
        name, seq, fam = node[1][1], True, None
    else:
        raise Skip(f"declaration of {T.to_qpp(node)}")
    key = seq_key(name) if seq else name
    if key in env.vars:
        # a second declaration of a declared name is a hypothesis
        if seq and node[0] == "app" and not (node[2][0][0] == "var" and node[2][0][1] not in env.vars):
            # a_(t) in X, t declared or a term (W_(j+1) after W_(j)): a hypothesis on that member only
            _, hs = set_info(s, env, term(node, env, 9))
            hyps += hs
            return
        if seq and node[0] == "app" and node[2][0][0] == "var" and node[2][0][1] not in env.vars:
            # a_(i) in X, i free: for every i of the range of the family
            i = node[2][0][1]
            v = env.vars[key]
            ln = T.lean_name(i)
            _, hs = set_info(s, env, f"{v['lean']} {ln}")
            pre = f"\u2200 {ln} : {v.get('ityp', chr(0x2115))}, "
            if v.get("fam"):
                pre += f"{term(v['fam'][0], env, 3)} \u2264 {ln} \u2192 {ln} \u2264 {term(v['fam'][1], env, 3)} \u2192 "
            hyps += [pre + h for h in hs]
            return
        if seq:
            raise Skip(f"{name}: a sequence declared twice")
        _, hs = set_info(s, env, env.lean(name))
        hyps += hs
        return
    lean = T.lean_name(name)
    if any(v["lean"] == lean for v in env.vars.values()):
        lean = lean + ("_seq" if seq else "_val")
    elem, hs = set_info(s, env, "\u00a7")
    if elem is None:
        raise Skip(f"{name}: a word without a type ({T.to_qpp(s)}) needs a typed declaration first")
    if seq:
        ityp = "\u2115"  # indices are counts; an integer bound N is read through N.toNat in sums
        if node[0] == "app" and all(a[0] == "var" and env.vars.get(a[1], {}).get("type") == "\u2124" for a in node[2]):
            # theta_(i) with i in ZZ: a family over the integers (through toNat, theta_(-1) and theta_(0) would
            # be one member)
            ityp = "\u2124"
        env.vars[key] = {"lean": lean, "type": f"{ityp} \u2192 {elem}", "seq": True, "fam": fam, "elem": elem,
                         "ityp": ityp}
        binders.append((lean, f"{ityp} \u2192 {elem}"))
        if hs and node[0] == "app" and not (node[2][0][0] == "var" and node[2][0][1] not in env.vars):
            # W_(j) in ZZ>=0 with j declared: the sequence W, and the hypothesis at j only (not for every index)
            hyps += [h.replace("\u00a7", term(node, env, 9)) for h in hs]
        elif hs:
            i = "i" if name != "i" else "j"
            pre = f"\u2200 {i} : {ityp}, "
            if fam is not None:
                with names(env):
                    pre += f"{T.to_lean(fam[0], 3)} \u2264 {i} \u2192 {i} \u2264 {T.to_lean(fam[1], 3)} \u2192 "
            hyps += [pre + h.replace("\u00a7", f"{lean} {i}") for h in hs]
    else:
        env.vars[name] = {"lean": lean, "type": elem}
        if s[0] == "polyring":
            env.vars[name]["pvar"] = T.to_qpp(s[2][-1])  # the formal variable of a polynomial (deg_y, lc_y, partial_y)
        binders.append((lean, elem))
        hyps += [h.replace("\u00a7", lean) for h in hs]


def is_name_node(x):
    return x[0] in ("var", "family") or (x[0] == "app" and x[3] == "idx" and x[1][0] == "var")


def fresh(base, env):
    i = 1
    while f"{base}_{i}" in env.vars:
        i += 1
    return f"{base}_{i}"


def flatten(x):
    """the clauses of a context: and-lists and contexts D : H read as lists"""
    if x[0] == "and":
        return [c for y in x[1] for c in flatten(y)]
    return [x]


def conj(props):
    """props joined by and: a quantified or implicational prop is parenthesized (its scope ends at its own end)"""
    def wrap(h):
        if len(props) > 1 and (h[:1] in ("\u2200", "\u2203") or any(o in h for o in (" \u2192 ", " \u2194 ", " \u2228 "))):
            return f"({h})"
        return h
    return " \u2227 ".join(wrap(h) for h in props)


def rename_components(t, ren):
    """rename the components x_(i) of the renamed vectors b_x -> b_x' (ren: Q++ name -> new var node)"""
    if not isinstance(t, tuple) or not t:
        return t
    if t[0] == "app" and len(t) > 3 and t[3] == "idx" and t[1][0] == "var" and "b_" + t[1][1] in ren:
        return ("app", ("var", ren["b_" + t[1][1]][1][2:]), rename_components(t[2], ren), t[3])
    if isinstance(t[0], str):
        return (t[0],) + tuple(rename_components(y, ren) for y in t[1:])
    return tuple(rename_components(y, ren) for y in t)


def vec_dim(typ):
    """the dimension (in Lean) of a vector type Fin d -> R, else None"""
    m = re.fullmatch(r"Fin (.+?) \u2192 [\u211a\u2124\u2115]", typ or "")
    return m.group(1) if m else None


def vector_of(letter, env):
    """(Lean name, dimension) of the vector b_x whose components are x_(i), if x_(i) is not a declared family"""
    v = env.vars.get("b_" + letter)
    if seq_key(letter) in env.vars or not v or not vec_dim(v["type"]):
        return None
    return v["lean"], vec_dim(v["type"])


def component_dim(t, i, env):
    """the dimension of a vector whose component in t is indexed by i (x_(i) for a vector b_x), or None"""
    if isinstance(t, tuple) and t:
        if t[0] == "app" and len(t) > 3 and t[3] == "idx" and t[1][0] == "var" and t[2] == (("var", i),):
            vec = vector_of(t[1][1], env)
            if vec:
                return vec[1]
        for y in kids(t):
            d = component_dim(y, i, env)
            if d:
                return d
    return None


def bind_fin(env, i, d):
    """i runs over Fin d (the components of a vector of dimension d); its value is i + 1"""
    env.vars[i] = {"lean": T.lean_name(i), "type": f"Fin {d}", "elem": "\u2115", "fin": d}


def drop_fin_bounds(t, i, d, env, quant):
    """forall i : (1 <= i <= d => P) is P over Fin d, and exists i : (i <= d, P) is P: the bounds of i that its
    type gives are dropped from the hypothesis (forall) or the first clause (exists) of t"""
    def is_dim(b):
        return term(b, env, 9) in (d, d.removesuffix(".toNat"))

    def given(op, a, b):
        if a == ("var", i):
            return (op == "<=" and is_dim(b)) or (op == ">=" and b == ("num", "1"))
        if b == ("var", i):
            return (op == ">=" and is_dim(a)) or (op == "<=" and a == ("num", "1"))
        return False

    def keep(c):
        if c[0] != "rel":
            return [c]
        links = [(op, a, b) for op, a, b in zip(c[1], c[2], c[2][1:]) if not given(op, a, b)]
        return [("rel", (op,), (a, b)) for op, a, b in links]
    if quant == "forall" and t[0] == "imp":
        hs = [y for c in flatten(t[1]) for y in keep(c)]
        return t[2] if not hs else ("imp", hs[0] if len(hs) == 1 else ("and", tuple(hs)), t[2])
    if quant == "exists" and t[0] == "and" and t[1]:
        cs = [y for y in keep(t[1][0])] + list(t[1][1:])
        return cs[0] if len(cs) == 1 else ("and", tuple(cs))
    return t


def declared_in(t):
    """the names that the hypotheses of an implication or context t declare"""
    out = set()
    while t[0] in ("imp", "ctx"):
        for c in flatten(t[1]):
            if c[0] == "decl":
                out.update(n[1] if n[0] == "var" else n[1][1] if n[0] == "app" else n[1] for n in c[1])
            elif c[0] == "def" and c[1][0] == "var":
                out.add(c[1][1])
            elif c[0] == "def" and c[1][0] == "app" and c[1][1][0] == "var":
                out.add(c[1][1][1])  # rho(t) := E
            elif c[0] == "rel" and c[1] in (("subseteq",), ("subset",)) and c[2][0][0] == "var":
                out.add(c[2][0][1])
        t = t[2]
    return out


def free_index_prefix(t, env, quant="\u2200", join="\u2192"):
    """(prefix, env with them) quantifying the indices of t that are not in scope (prefix_indices): over Fin d for
    the components of a vector, else over the range of their family when there is one"""
    idx = prefix_indices(t, env.vars)
    if not idx:
        return "", env
    local = env.child()
    pre = []
    for i in idx:
        ln = T.lean_name(i)
        d = component_dim(t, i, env)
        if d:
            bind_fin(local, i, d)
            pre.append(f"{quant} {ln} : Fin {d},")
            continue
        rng = family_range_of(t, i, env)
        local.vars[i] = {"lean": ln, "type": "\u2115"}
        if rng:
            pre.append(f"{quant} {ln} : \u2115, {term(rng[0], env, 3)} \u2264 {ln} {join} {ln} \u2264 {term(rng[1], env, 3)} {join}")
        else:
            if t[0] in ("imp", "ctx") and all(i in free_names(p) for p in (t[1], t[2])):
                # a context and its conclusion share it and no family gives a range: the conclusion is claimed at
                # every natural number, 0 and the indices past the family's length included (a stronger statement)
                STMT_WARN.append(f"the index {i} is free in a hypothesis and in its conclusion and no family gives "
                                 f"its range, so it reads 'for every {i} in N' (declare it, or write the range)")
            pre.append(f"{quant} {ln} : \u2115,")
    return " ".join(pre) + " ", local


def chain_bounds(body, name):
    """(a lower bound, an upper bound): what the hypothesis of the body of a quantifier (forall i : i <= D => ...)
    puts on the name"""
    lo = hi = False
    if body[0] in ("imp", "ctx"):
        for c in flatten(body[1]):
            if c[0] != "rel":
                continue
            for op, a, b in zip(c[1], c[2], c[2][1:]):
                if op in (">=", ">"):
                    a, b = b, a
                elif op not in ("<=", "<"):
                    continue
                lo, hi = lo or b == ("var", name), hi or a == ("var", name)
    return lo, hi


def bound_vars(t, acc=None):
    """every name some binder of t binds (unscoped: for renaming and scope checks, not for reading)"""
    acc = set() if acc is None else acc
    if isinstance(t, tuple) and t:
        if t[0] in ("exists", "forall"):
            for v in t[1]:
                if v[0] == "var":
                    acc.add(v[1])
        if t[0] in ("sum", "prod", "max", "min", "par", "union", "inter", "oplus", "comp"):
            acc.add(t[1])
        if t[0] == "setof" and t[1][0] == "such":
            acc |= builder_names(t[1])
        for y in kids(t):
            bound_vars(y, acc)
    return acc


def family_range_of(t, i, env):
    """the range of the family indexed by i in t, if a declared family with a range is"""
    found = []

    def walk(x):
        if isinstance(x, tuple) and x:
            if x[0] == "app" and x[3] == "idx" and x[1][0] == "var" and ("var", i) in x[2]:
                v = env.vars.get(seq_key(x[1][1]))
                if v and v.get("fam"):
                    found.append(v["fam"])
            for y in kids(x):
                walk(y)
    walk(t)
    return found[0] if found else None


def family_decl(c):
    """forall k in K : theta_(k) in X (theta_k in X for k in K): the family theta over the set K, or None"""
    if c[0] == "forall" and c[2] is not None and len(c[1]) == 1 and c[1][0][0] == "var" and c[3][0] == "decl" \
            and all(n[0] == "app" and n[3] == "idx" and n[1][0] == "var" and n[2] == (c[1][0],) for n in c[3][1]):
        return c[1][0][1], c[2], [n[1][1] for n in c[3][1]], c[3][2]
    if c[0] == "forall" and c[2] is None and len(c[1]) == 1 and c[1][0][0] == "var" and c[3][0] == "imp" \
            and c[3][1][0] == "rel" and c[3][1][1] == ("<=", "<=") and c[3][1][2][1] == c[1][0] \
            and c[3][2][0] == "decl" and all(n[0] == "app" and n[3] == "idx" and n[1][0] == "var"
                                             and n[2] == (c[1][0],) for n in c[3][2][1]):
        # g_l : Q -> Q for 1 <= l <= L: the family over the range
        lo, _, hi = c[3][1][2]
        return c[1][0][1], ("intrange", lo, hi), [n[1][1] for n in c[3][2][1]], c[3][2][2]
    return None


def declare_over(env, k, K, names_, X, binders, hyps):
    """the families names_ over the index set K (their index type is the element type of K), with values in X"""
    ityp, _ = set_info(K, env, "\u00a7")
    if ityp is None:
        raise Skip(f"a family over {T.to_qpp(K)} (no index type)")
    for name in names_:
        key = seq_key(name)
        if key in env.vars:
            raise Skip(f"{name}: a sequence declared twice")
        lean = T.lean_name(name)
        if any(v["lean"] == lean for v in env.vars.values()):
            lean += "_seq"
        elem, hs = set_info(X, env, "\u00a7")
        if elem is None:
            raise Skip(f"{name}: a family in {T.to_qpp(X)} (no type)")
        env.vars[key] = {"lean": lean, "type": f"{ityp} \u2192 {elem}", "seq": True,
                         "fam": (K[1], K[2]) if K[0] == "intrange" else None, "elem": elem, "ityp": ityp}
        binders.append((lean, f"{ityp} \u2192 {elem}" if "\u2192" not in elem else f"{ityp} \u2192 ({elem})"))
        if hs:
            t = "t" if lean != "t" else "t\u2080"
            _, ks = set_info(K, env, t)
            hyps.append(f"\u2200 {t} : {ityp}, " + "".join(f"{h} \u2192 " for h in ks)
                        + conj([h.replace("\u00a7", f"{lean} {t}") for h in hs]))


def lean_hyp(c, env, binders, hyps):
    """a clause of a context: a declaration, a definition or a hypothesis (one per link of a chain)"""
    if c[0] == "decl":
        for n in c[1]:
            declare(env, n, c[2], binders, hyps)
        return
    if family_decl(c):
        k, K, ns, X = family_decl(c)
        declare_over(env, k, K, ns, X, binders, hyps)
        return
    if c[0] == "def" and c[2][0] == "least" and c[1][0] == "var":
        # m := min {t : D}: the least element of the set, a name with its membership and m <= every element
        typ, _ = set_info(c[2][2], env, "\u00a7")
        if typ not in TYPE_RANK:
            raise Skip(f"the least element of {T.to_qpp(c[2][2])} (no type)")
        declare(env, c[1], ("set", {"\u2115": "NN", "\u2124": "ZZ", "\u211a": "QQ"}[typ]), binders, hyps)
        hyps.append(least_element(c[1], c[2], env))
        return
    if c[0] == "def" and c[2][0] in ("min", "max") and c[1][0] == "var":
        # m := min i, t: a name with its definition, m <= t for every i and m = t for some i (max: >=)
        m, (k, i, dom, body) = c[1], c[2]
        typ = infer_type(body, env)
        declare(env, m, ("set", {"\u2115": "NN", "\u2124": "ZZ", "\u211a": "QQ"}[typ]), binders, hyps)
        iv = ("var", i)
        if dom is None:
            bound = None
        elif dom[0] == "range":
            bound = ("rel", ("<=", "<="), (dom[1][0], iv, dom[1][1]))
        elif dom[0] == "cond":
            bound = dom[1]  # the indices of the family that satisfy a condition (the range comes with the index)
        elif dom[0] == "in":
            bound = ("rel", ("in",), (iv, dom[1]))
        elif dom[0] in ("le", "lt"):
            bound = ("rel", ("<=" if dom[0] == "le" else "<",), (iv, dom[1]))
        else:
            raise Skip(f"{k} over {T.to_qpp(dom[1])}")
        below = ("rel", ("<=" if k == "min" else ">=",), (m, body))
        attained = ("rel", ("=",), (m, body))
        hyps.append(lean_prop(("forall", (iv,), None, below if bound is None else ("imp", bound, below)), env))
        hyps.append(lean_prop(("exists", (iv,), None, attained if bound is None else ("and", (bound, attained))), env))
        return
    if c[0] == "def" and c[1][0] == "app" and c[1][1][0] == "var" and c[1][3] in ("idx", "call"):
        define_applied(c[1], c[2], env, binders, hyps)
        return
    if c[0] == "def":
        lhs = c[1]
        if lhs[0] != "var":
            raise Skip(f"definition of {T.to_qpp(lhs)}")
        typ = infer_type(c[2], env)
        declare(env, lhs, ("set", {"\u2115": "NN", "\u2124": "ZZ", "\u211a": "QQ"}[typ]), binders, hyps)
        hyps.append(f"{env.lean(lhs[1])} = {term(c[2], env)}")
        return
    if c[0] == "ctx":
        for y in flatten(c[1]) + flatten(c[2]):
            lean_hyp(y, env, binders, hyps)
        return
    if c[0] == "imp" and c[2][0] == "def":
        guarded_def(c[1], c[2], env, binders, hyps)
        return
    if r1_clause(c):
        raise Skip(R1_REASON)
    if c[0] == "rel" and len(c[1]) == 1 and c[1][0] in ("subseteq", "subset") and c[2][0][0] == "var" \
            and c[2][0][1] not in env.vars:
        # S subseteq X declares S, a set of the elements of X
        name, X = c[2][0][1], c[2][1]
        elem, hs = set_info(X, env, "\u00a7")
        if elem is None:
            raise Skip(f"{name}: a subset of {T.to_qpp(X)} (no element type)")
        lean = T.lean_name(name)
        env.vars[name] = {"lean": lean, "type": f"Set ({elem})" if " " in elem else f"Set {elem}"}
        binders.append((lean, env.vars[name]["type"]))
        if X[0] not in ("set", "pow"):
            hyps.append(f"{lean} {T.REL_LEAN[c[1][0]]} {term(X, env)}")
        elif hs:
            hyps.append(f"\u2200 t \u2208 {lean}, " + conj([h.replace("\u00a7", "t") for h in hs]))
        return
    if c[0] == "rel":
        # a chain of bounds on a new index declares it (1 <= k <= N)
        for a in c[2]:
            if a[0] == "var" and a[1] not in env.vars and is_index_name(a[1]):
                env.vars[a[1]] = {"lean": T.lean_name(a[1]), "type": "\u2115"}
                binders.append((T.lean_name(a[1]), "\u2115"))
        for op, a, b in zip(c[1], c[2], c[2][1:]):
            hyps.append(lean_prop(("rel", (op,), (a, b)), env))
        return
    hyps.append(lean_prop(c, env))


NUM_SETS = {"\u2115": "NN", "\u2124": "ZZ", "\u211a": "QQ"}


R1_REASON = ("a family of sets or functions over the members of a set (X_R subseteq Q^k for R in Pi, theta_(R, f) for "
             "f in J): finite sets as Lean types, not generated yet")


def r1_clause(c):
    """a declaration of a family over the members of a set (X_R subseteq Q^k, theta_(R, f) in (Q^k -> Q) for f in J)"""
    return (c[0] == "rel" and len(c[1]) == 1 and c[1][0] in ("subseteq", "subset") and c[2][0][0] == "app"
            and c[2][0][3] == "idx") or (c[0] == "forall" and c[3][0] == "decl" and any(
                n[0] == "app" and n[3] == "idx" and len(n[2]) > 1 for n in c[3][1]))


def guarded_def(H, d, env, binders, hyps):
    """H => x := t, a case of a case definition (x:=t\\ (H), y:=u\\ (\\text{else})): the name is declared by its
    first case, and its value is given where the condition holds (a member a_(i) or a function f(y) for every value of
    its parameters where it holds)"""
    lhs, rhs = d[1], d[2]
    if lhs[0] == "var":
        typ = infer_type(rhs, env)
        if lhs[1] not in env.vars:
            declare(env, lhs, ("set", NUM_SETS[typ]), binders, hyps)
        elif TYPE_RANK.get(env.vars[lhs[1]]["type"], 9) < TYPE_RANK[typ]:
            raise Skip(f"a case definition of {lhs[1]} whose cases have different types")
        hyps.append(f"({lean_prop(H, env)}) \u2192 {env.lean(lhs[1])} = {term(rhs, env)}")
        return
    if lhs[0] == "app" and lhs[1][0] == "var":
        define_applied(lhs, rhs, env, binders, hyps, guard=H)
        return
    raise Skip(f"a case definition of {T.to_qpp(lhs)}")


def index_type(rhs, a, env):
    """the type of a parameter a of a definition, from its uses as an index of a declared family in rhs (that
    family's index type), or None"""
    for y in T.subterms(rhs):
        if y[0] == "app" and len(y) > 3 and y[3] == "idx" and y[1][0] == "var" and ("var", a) in y[2]:
            v = env.vars.get(seq_key(y[1][1]))
            if v is not None:
                return v.get("ityp", "\u2115")
            if "b_" + y[1][1] in env.vars:
                raise Skip(f"a definition indexed by the components of the vector b_{y[1][1]} (no Lean form yet)")
    return None


def define_applied(lhs, rhs, env, binders, hyps, guard=None):
    """f(y) := E, sigma_(a, b) := E with free parameters: a function (a family) with its defining equation for every
    value of the parameters; beta'_(j) := E with j declared: the member at j of a family beta', with its value.
    Parameter types: the index type of a family they index in E, else Q for a function of a number and N for an
    index"""
    f, args, how = lhs[1][1], lhs[2], lhs[3]
    key = seq_key(f) if how == "idx" else f
    if not all(a[0] == "var" for a in args) and how == "call":
        raise Skip(f"definition of {T.to_qpp(lhs)}: an argument that is not a name")
    if guard is not None and key in env.vars:
        # the second case of a case definition: the name is declared by the first
        v = env.vars[key]
        ptypes = v["type"].split(" \u2192 ")[:-1]
        if len(ptypes) != len(args) or not all(a[0] == "var" and a[1] not in env.vars for a in args):
            raise Skip(f"a case definition of {T.to_qpp(lhs)} at other arguments than its first case")
        inner = env.child()
        for a, t in zip(args, ptypes):
            inner.vars[a[1]] = {"lean": fresh_lean(T.lean_name(a[1]), env), "type": t}
        if TYPE_RANK.get(v["type"].rsplit(" \u2192 ", 1)[-1], 9) < TYPE_RANK[infer_type(rhs, inner)]:
            raise Skip(f"a case definition of {T.to_qpp(lhs)} whose cases have different types")
        params = " ".join(f"({inner.vars[a[1]]['lean']} : {t})" for a, t in zip(args, ptypes))
        hyps.append(f"\u2200 {params}, ({lean_prop(guard, inner)}) \u2192 {term(lhs, inner, 3)} = {term(rhs, inner)}")
        return
    free = [a[1] for a in args if a[0] == "var" and a[1] not in env.vars and seq_key(a[1]) not in env.vars]
    if free and len(free) < len(args):
        raise Skip(f"definition of {T.to_qpp(lhs)}: some indices declared, some free")
    if not free:
        if how != "idx":
            raise Skip(f"definition of {T.to_qpp(lhs)} at a declared value (define the function with a free name)")
        # the member of a family at declared indices: beta'_(j) := E
        typ = infer_type(rhs, env)
        if key not in env.vars:
            ityps = {infer_type(a, env) for a in args}
            if len(ityps) != 1 or ityps & {"\u211a"}:
                raise Skip(f"definition of {T.to_qpp(lhs)}: indices of mixed or rational type")
            ityp = ityps.pop()
            lean = T.lean_name(f)
            if any(v["lean"] == lean for v in env.vars.values()):
                lean += "_seq"
            ftype = " \u2192 ".join([ityp] * len(args) + [typ])
            env.vars[key] = {"lean": lean, "type": ftype, "seq": True, "fam": None, "elem": typ, "ityp": ityp}
            binders.append((lean, ftype))
        hyps.append(f"{term(lhs, env, 3)} = {term(rhs, env)}")
        return
    if key in env.vars:
        raise Skip(f"definition of {T.to_qpp(lhs)}: {f} is declared already")
    late = sorted(set(free) & GIVEN_NAMES)
    if late:
        # rho_y := E with y declared after it: a member at y, or one name (a names row)? declare y first
        raise Skip(f"definition of {T.to_qpp(lhs)}: {', '.join(late)} is declared later in the given (declare it "
                   f"first for the member at it, or name {T.to_qpp(lhs)} in a names row)")
    if len(set(free)) < len(free):
        raise Skip(f"definition of {T.to_qpp(lhs)}: a repeated parameter")
    inner = env.child()
    taken = {v["lean"] for v in env.vars.values()}
    ptypes = []
    for a in free:
        typ = index_type(rhs, a, env) or ("\u211a" if how == "call" else "\u2115")
        lean = T.lean_name(a)
        while lean in taken:
            lean += "'"
        taken.add(lean)
        inner.vars[a] = {"lean": lean, "type": typ}
        ptypes.append(typ)
    if how == "idx" and len(set(ptypes)) > 1:
        raise Skip(f"definition of {T.to_qpp(lhs)}: indices of mixed type")
    typ = infer_type(rhs, inner)
    lean = T.lean_name(f)
    while lean in taken:
        lean += "'"
    ftype = " \u2192 ".join(ptypes + [typ])
    info = {"lean": lean, "type": ftype}
    if how == "idx":
        info.update({"seq": True, "fam": None, "elem": typ, "ityp": ptypes[0]})
    env.vars[key] = info
    inner.vars[key] = info
    binders.append((lean, ftype))
    params = " ".join(f"({inner.vars[a]['lean']} : {t})" for a, t in zip(free, ptypes))
    cond = f"({lean_prop(guard, inner)}) \u2192 " if guard is not None else ""
    hyps.append(f"\u2200 {params}, {cond}{term(lhs, inner, 3)} = {term(rhs, inner)}")


def least_element(m, node, env):
    """m is the least (greatest) element of the set S of the node min {..} (max {..}): m in S, and m <= x (>=)
    for every x in S"""
    kind, S = node[1], node[2]
    ml = term(m, env, 3)
    typ, hs = set_info(S, env, ml)
    if typ is None:
        raise Skip(f"the {kind} of {T.to_qpp(S)} (no type)")
    x = "x"
    while x in env.vars or T.lean_name(x) in {v["lean"] for v in env.vars.values()} or x == ml:
        x += "'"
    _, hx = set_info(S, env, x)
    rel = "\u2264" if kind == "min" else "\u2265"
    bound = f"\u2200 {x} : {typ}, " + "".join((f"({h}) \u2192 " if " " in h else f"{h} \u2192 ") for h in hx) + f"{ml} {rel} {x}"
    return conj(hs + [bound])


INDEX_LETTERS = set("ijklmn")


def is_index_name(v):
    return v.rstrip("'") in INDEX_LETTERS


def infer_type(x, env):
    """the least of N, Z, Q containing a term (division gives Q)"""
    rank = 0

    def walk(y):
        nonlocal rank
        if isinstance(y, tuple) and y:
            if y[0] == "app" and len(y) > 3 and y[3] == "call" and y[1][0] == "var" and y[1][1] in env.vars:
                # F(t), F declared: the type of its values (S(t) for S a polynomial: its coefficients)
                typ = env.vars[y[1][1]]["type"].rsplit("\u2192 ", 1)[-1].replace("Polynomial ", "")
                rank = max(rank, TYPE_RANK.get(typ, 2))
                return
            if y[0] == "app" and len(y) > 3 and y[3] == "call" and y[1] == ("var", "deg"):
                rank = max(rank, 0)  # a degree is a natural number
                return
            if y[0] == "app" and len(y) > 3 and y[3] == "call" and op_with_variable(y):
                # deg_y S is a natural number; lc_y, Res_y and a derivative at a point are values (rationals)
                rank = max(rank, 0 if y[1][0] == "app" and y[1][1][1] == "deg" else 2)
                return
            if y[0] == "app" and len(y) > 3 and y[3] == "call" and y[1][0] == "app" and y[1][1] == ("var", "deriv"):
                rank = 2  # a derivative at a point
                return
            if y[0] == "app" and len(y) > 3 and y[3] == "call" and y[1] == ("var", "choose"):
                rank = 2  # printed (Nat.choose p i : Q), as the papers' terms
                return
            if y[0] == "app" and len(y) > 3 and y[3] == "call" and y[1] in (("var", "min"), ("var", "max")):
                for a in y[2]:
                    walk(a)  # the type of its arguments
                return
            if y[0] == "app" and len(y) > 3 and y[3] == "call" and y[1] in BUILTIN_FUNS:
                # a count (card), or lg (rational only in a ceiling or a floor, which gives an integer)
                rank = max(rank, 0 if y[1][1] == "card" else 2)
                return
            if y[0] in ("ceil", "floor") and y[1][0] == "app" and y[1][1] == ("var", "lg"):
                rank = max(rank, 1)
                return
            if y[0] == "pow":
                # the type of the base, unless the exponent may be negative (zpow: a rational value)
                walk(y[1])
                if T.int_exponent(y[2]) or infer_type(y[2], env) != "\u2115":
                    rank = 2
                return
            if y[0] == "iverson" or (y[0] == "app" and len(y) > 3 and y[1] in (("var", "fact"), ("var", "dist"))):
                rank = 2  # printed in Q, as the papers' terms ((if P then (1 : Q) else 0), (Nat.factorial k : Q))
                return
            if y[0] == "least":
                typ, _ = set_info(y[2], env, "\u00a7")
                rank = max(rank, TYPE_RANK.get(typ, 2))
                return
            if y[0] == "app" and len(y) > 3 and y[3] == "idx" and y[1][0] == "var":
                # a term of a family (or a component of a vector): the type of its values
                v = env.vars.get(seq_key(y[1][1])) or env.vars.get("b_" + y[1][1])
                if v is None:
                    raise Skip(f"undeclared {y[1][1]}_i")
                typ = v.get("elem") or (v["type"].rsplit("\u2192 ", 1)[-1])
                rank = max(rank, TYPE_RANK.get(typ, 2))
                return
            if y[0] == "var":
                v = env.vars.get(y[1])
                if v is None:
                    raise Skip(f"undeclared {y[1]}")
                rank = max(rank, TYPE_RANK.get(v.get("elem", v["type"]), 2))
            elif y[0] == "bin" and y[1] == "/":
                rank = 2
            elif y[0] == "neg" or (y[0] == "bin" and y[1] == "-"):
                rank = max(rank, 1)
            for z in y[1:]:
                if isinstance(z, tuple):
                    walk(z)
    walk(x)
    return ["\u2115", "\u2124", "\u211a"][rank]


def lean_prop(x, env):
    """a proposition of a statement in Lean, with its own binders"""
    k = x[0]
    if k in ("imp", "ctx"):
        pre, env = free_index_prefix(x, env)
        if pre:
            return pre + lean_prop(x, env)
        local = env.child()
        binders, hyps = [], []
        rest = x[2]
        for c in flatten(x[1]):
            if (c[0] in ("rel", "decl") and c[0] == "rel" and c[1] == ("in",) and not is_name_node(c[2][0])
                    and c[2][1][0] == "set" and c[2][1][1] in ("ZZ", "NN")):
                # t in Z: an integer witness n = t, and t is read as n in what follows
                n = fresh("n", local)
                typ = SET_TYPES[c[2][1][1]]
                local.vars[n] = {"lean": T.lean_name(n), "type": typ}
                binders.append((T.lean_name(n), typ))
                hyps.append(f"({T.lean_name(n)} : \u211a) = {term(c[2][0], local)}")
                rest = replace_term(rest, c[2][0], ("var", n))
                continue
            lean_hyp(c, local, binders, hyps)
        body = lean_prop(rest, local)
        if hyps and rest[0] == "iff":
            body = f"({body})"  # Lean's \u2194 binds looser than \u2192: h \u2192 A \u2194 B would read (h \u2192 A) \u2194 B
        s = body
        for h in reversed(hyps):
            s = f"({h}) \u2192 {s}" if " " in h else f"{h} \u2192 {s}"
        if binders:
            s = "\u2200 " + " ".join(f"({n} : {typ})" for n, typ in binders) + ", " + s
        return s
    if k == "and":
        if any(c[0] in ("decl", "def") for c in x[1]):
            raise Skip("a declaration in a conclusion")
        pre, env = free_index_prefix(x, env)
        return pre + " \u2227 ".join(f"({lean_prop(c, env)})" for c in x[1])
    if k in ("exists", "forall"):
        local = env.child()
        vs = x[1]
        sym = "\u2203" if k == "exists" else "\u2200"
        join = "\u2227" if k == "exists" else "\u2192"
        conds = []
        bs = []
        body_t = x[3]
        for v in vs:
            if v[0] != "var":
                raise Skip("a binder that is not a name")
            if x[2] is None and component_dim(body_t, v[1], env):
                d = component_dim(body_t, v[1], env)
                bind_fin(local, v[1], d)
                bs.append(f"({T.lean_name(v[1])} : Fin {d})")
                body_t = drop_fin_bounds(body_t, v[1], d, local, k)
            elif x[2] is None and bound_type(body_t, v[1], k, env):
                # forall S : S subseteq X => ..., exists Z : Z subseteq O, ...: the binder takes its type from the
                # bound (a set of the elements of X, a member of X); the bound stays a condition
                typ = bound_type(body_t, v[1], k, env)
                local.vars[v[1]] = {"lean": T.lean_name(v[1]), "type": typ}
                bs.append(f"({T.lean_name(v[1])} : {typ})")
            elif x[2] is None:
                if key_base(v[1]) not in INDEX_LETTERS and not family_range_of(x[3], v[1], env):
                    # \exists c,C: a binder with no set is a count only when it is an index (i, j, k, l, m, n, j_0)
                    raise Skip(f"the binder {v[1]} has no set (declare it: {k} {v[1]} in QQ>0, ...)")
                local.vars[v[1]] = {"lean": T.lean_name(v[1]), "type": "\u2115"}
                bs.append(T.lean_name(v[1]))
                rng = family_range_of(x[3], v[1], env)
                if rng:
                    ln = T.lean_name(v[1])
                    conds += [f"{term(rng[0], env, 3)} \u2264 {ln}", f"{ln} \u2264 {term(rng[1], env, 3)}"]
                elif chain_bounds(x[3], v[1]) == (False, True):
                    STMT_WARN.append(f"the index {v[1]} of 'for {v[1]} <= ...' is of no family and has no lower bound, "
                                     f"so it runs from 0 (write 1 <= {v[1]} <= ... for the indices from 1)")
            else:
                b2, h2 = [], []
                declare(local, v, x[2], b2, h2)
                bs += [f"({n} : {typ})" for n, typ in b2]
                conds += h2
        body = lean_prop(body_t, local)
        inner = f" {join} ".join(conds + [f"({body})" if " " in body else body])
        typed = " ".join(b if b.startswith("(") else f"({b} : \u2115)" for b in bs)
        return f"{sym} {typed}, {inner}"
    if k == "rel" and any(t[0] == "app" and t[1] == ("var", "restrict") for t in x[2]) and len(x[1]) == 1:
        # h|_F = 0: h = 0 on F
        rs = [t for t in x[2] if t[0] == "app" and t[1] == ("var", "restrict")]
        if len(rs) != 1:
            raise Skip("a relation between two restrictions")
        h, F = rs[0][2]
        return lean_prop(("on", F, ("rel", x[1], tuple(h if t is rs[0] else t for t in x[2]))), env)
    if k == "attained":
        # m = min S, attained: the least element of S, a member of S (the reading of min already says it)
        y = x[1]
        if y[0] == "rel" and y[1] == ("=",) and (y[2][0][0] == "least" or y[2][1][0] == "least"):
            return lean_prop(y, env)
        raise Skip("attained after a clause that is not m = min S (or max)")
    if k == "uniform":
        raise Skip(f"constants free of {', '.join(T.to_qpp(n) for n in x[1])}: the order of the quantifiers of the "
                   "comparison, no Lean form yet")
    if k == "rel":
        x = point_sets(x, env)
        pre, env = free_index_prefix(x, env)
        links = []
        for op, a, b in zip(x[1], x[2], x[2][1:]):
            if op == "in":
                _, hs = set_info(b, env, term(a, env, 9))
                links += hs
                continue
            r = expand_relation(op, a, b, env)
            if r is not None:
                s = lean_prop(r, env)  # the free indices of the link are quantified once, outside (pre)
                links.append(f"({s})" if len(x[1]) > 1 else s)
            elif op == "=" and b[0] == "least":
                links.append(least_element(a, b, env))
            elif op == "=" and a[0] == "least":
                links.append(least_element(b, a, env))
            elif op == "succ" and b == ("num", "0") and a[0] == "var" and \
                    (env.vars.get(a[1], {}).get("type") or "").startswith("Matrix "):
                # G succ 0: positive definite, symmetric with x^T G x > 0 for x != 0
                m = re.fullmatch(r"Matrix \(Fin (.+?)\) \(Fin (.+?)\) \u211a", env.vars[a[1]]["type"])
                if not m or m.group(1) != m.group(2):
                    raise Skip(f"{a[1]} succ 0 for a matrix that is not square over Q")
                g, xv = term(a, env, 9), fresh_lean("x", env)
                links.append(f"(Matrix.transpose {g} = {g} \u2227 \u2200 {xv} : Fin {m.group(1)} \u2192 \u211a, {xv} \u2260 0 \u2192 "
                             f"0 < \u2211 i, \u2211 j, {xv} i * {g} i j * {xv} j)")
            else:
                s = vector_order(op, a, b, env)
                links.append(s if s is not None else term(("rel", (op,), (a, b)), env))
        return pre + conj(links)
    if k in ("or", "iff"):
        pre, env = free_index_prefix(x, env)
        return pre + f"({lean_prop(x[1], env)}) {'\u2228' if k == 'or' else '\u2194'} ({lean_prop(x[2], env)})"
    if k == "decl":
        out = []
        for n in x[1]:
            _, hs = set_info(x[2], env, term(n, env, 9))
            out += hs
        return conj(out) if out else "True"
    if k == "on":
        # P on S: for every w of S, P with its functions on the elements of S applied to w
        S, P = x[1], x[2]
        elem, _ = set_info(S, env, "\u00a7")
        if elem is None:
            raise Skip(f"on {T.to_qpp(S)}: no element type")
        w = "w"
        while w in env.vars or T.lean_name(w) in {v["lean"] for v in env.vars.values()}:
            w += "'"
        fs = {n for n, v in env.vars.items() if v.get("type", "").startswith(f"({elem}) \u2192")
              or v.get("type", "").startswith(f"{elem} \u2192")}
        if not fs:
            raise Skip(f"on {T.to_qpp(S)}: no function on its elements")
        local = env.child()
        local.vars[w] = {"lean": T.lean_name(w), "type": elem}
        body = lean_prop(apply_on(P, fs, ("var", w)), local)
        mem = set_info(S, env, T.lean_name(w))[1]
        return f"\u2200 {T.lean_name(w)} : {elem}, " + "".join(f"{h} \u2192 " for h in mem) + body
    if k == "not":
        return f"\u00ac({lean_prop(x[1], env)})"
    if k in ("ref", "refat"):
        raise Skip(f"the reference @{x[1]} as a hypothesis: the referenced condition as a predicate with its free names "
                   "is not generated yet")
    if k in ("at", "near"):
        return at_point(x, env)
    if k == "textrel":
        r = expand_textrel(x, env)
        if r is None:
            raise Skip(f"the relational word {' _ '.join(x[1])} has no row")
        return lean_prop(r, env)
    if k == "defrel":
        raise Skip("a defined relation (a vocabulary row, expanded where it is used)")
    raise Skip(f"{k} in a statement (no Lean form yet)")


def point_sets(x, env):
    """x with each set {P} of the points where P holds ({K <= 2^(-L)}, the declared functions of P not applied) read as
    {w | P at w}: the builder over the domain of those functions"""
    def walk(t):
        if not isinstance(t, tuple) or not t:
            return t
        if t[0] == "setof" and t[1][0] != "such" and T.is_prop(t[1]):
            fs = {n for n in free_vars(t[1]) if " \u2192 " in env.vars.get(n, {}).get("type", "")
                  and not env.vars[n].get("seq")}
            if fs:
                w = fresh_lean("w", env)
                return ("setof", ("such", ("var", w), apply_on(t[1], fs, ("var", w))))
            return t
        if isinstance(t[0], str):
            return (t[0],) + tuple(walk(y) for y in t[1:])
        return tuple(walk(y) for y in t)
    return walk(x)


def fresh_lean(base, env, avoid=()):
    """a Lean name from base that no name of the environment (nor avoid) has"""
    used = {v["lean"] for v in env.vars.values()} | set(env.vars) | set(avoid)
    n = base
    while n in used:
        n += "'"
    return n


def functions_on(typ, env):
    """the names of the environment that are functions on the elements of the type typ (their values are taken at a
    point by P at p, P on S, P near p)"""
    return {n for n, v in env.vars.items() if v.get("type", "").startswith(f"({typ}) \u2192")
            or v.get("type", "").startswith(f"{typ} \u2192")}


def at_point(x, env):
    """P at p: P with the functions on the type of p applied to p. P near p (one reading):
    some box has p in its interior and P on it, the interior of a box being the product of the open intervals (strict
    inequalities over Q, no topology): for p in Q, some a < p < b with P on [a, b]; for a vector, the same in every
    component"""
    k, p, P = x
    typ = term_type(p, env)
    fs = functions_on(typ, env)
    if not fs:
        raise Skip(f"{k} {T.to_qpp(p)}: no function on its type ({typ}) in the statement")
    if k == "at":
        return lean_prop(apply_on(P, fs, p), env)
    pl = term(p, env, 9)
    d = vec_dim(typ)
    if typ != "\u211a" and d is None:
        raise Skip(f"near {T.to_qpp(p)}: a point of {typ} (a box is in Q or Q^n)")
    a, b = fresh_lean("a", env), fresh_lean("b", env, ("a",))
    a = a if a != b else a + "'"
    w = fresh_lean("w", env, (a, b))
    local = env.child()
    local.vars[w] = {"lean": w, "type": typ}
    body = lean_prop(apply_on(P, fs, ("var", w)), local)
    if d is None:
        return (f"\u2203 {a} {b} : \u211a, {a} < {pl} \u2227 {pl} < {b} \u2227 \u2200 {w} : \u211a, {a} \u2264 {w} \u2192 "
                f"{w} \u2264 {b} \u2192 {body}")
    i = fresh_lean("i", env, (a, b, w))
    return (f"\u2203 {a} {b} : Fin {d} \u2192 \u211a, (\u2200 {i}, {a} {i} < {pl} {i} \u2227 {pl} {i} < {b} {i}) \u2227 "
            f"\u2200 {w} : Fin {d} \u2192 \u211a, (\u2200 {i}, {a} {i} \u2264 {w} {i} \u2227 {w} {i} \u2264 {b} {i}) \u2192 {body}")


def bound_type(body, v, quant, env):
    """the Lean type that the bound of a binder gives it (forall S : (empty != S subseteq X) => P, exists Z : Z
    subseteq O, P): Set of the element type of X for a link S subseteq X (or subset), the element type of X for v in
    X; None when the first condition has no such link"""
    cond = body[1] if quant == "forall" and body[0] == "imp" else body[1][0] if quant == "exists" and body[0] == "and" \
        else None
    for c in flatten(cond) if cond is not None else ():
        if c[0] != "rel":
            continue
        for op, a, b in zip(c[1], c[2], c[2][1:]):
            if a == ("var", v) and op in ("subseteq", "subset", "in"):
                try:
                    elem, _ = set_info(b, env, "\u00a7")
                except Skip:
                    return None
                if elem is None:
                    return None
                return (f"Set ({elem})" if " " in elem else f"Set {elem}") if op != "in" else elem
    return None


def codomain(typ):
    """the codomain of a function type (the type after its first arrow outside parentheses), or None"""
    depth = 0
    for j, ch in enumerate(typ):
        depth += {"(": 1, ")": -1}.get(ch, 0)
        if depth == 0 and typ.startswith(" \u2192 ", j):
            return typ[j + 3:]
    return None


def vector_term_dim(t, env):
    """the dimension of a vector term (a vector, a sum or difference of vectors, a number times one, a value of a map
    into vectors), or None"""
    if t[0] == "var" and t[1] in env.vars:
        return vec_dim(env.vars[t[1]]["type"])
    if t[0] == "app" and t[3] == "call" and t[1][0] == "var" and t[1][1] in env.vars and len(t[2]) == 1:
        return vec_dim(codomain(env.vars[t[1][1]]["type"]) or "")
    if t[0] == "neg":
        return vector_term_dim(t[1], env)
    if t[0] == "bin" and t[1] in ("+", "-", "*"):
        return vector_term_dim(t[2], env) or vector_term_dim(t[3], env)
    return None


def vector_order(op, a, b, env):
    """a < b on vectors is strict in every component (not Lean's order on Fin n -> Q, where a < b is a <= b and
    a != b); a vector against a number other than 0 is compared componentwise: the Lean link, or None"""
    da, db = vector_term_dim(a, env), vector_term_dim(b, env)
    if not (da or db):
        return None
    scalar = b if da and not db else a if db and not da else None
    if op in ("<=", ">=", "=", "!=") and (scalar is None or scalar == ("num", "0")):
        return None  # Lean's order and equality on Fin n -> Q are componentwise
    if op == "!=":
        raise Skip("a vector unequal to a number")
    i = "i"
    used = {v["lean"] for v in env.vars.values()}
    while i in used:
        i += "'"

    def at(t):
        if vector_term_dim(t, env) is None:
            return term(t, env, 3)
        s = term(t, env, 9)
        return f"{s} {i}"
    return f"\u2200 {i}, {at(a)} {T.REL_LEAN[op]} {at(b)}"


ORDER = {"<=": ">=", ">=": "<=", "<": ">", ">": "<"}
STRICT = {"<=": "<", ">=": ">", "<": "<", ">": ">"}


def unify(p, x, pv, s):
    """match the pattern p (pattern variables pv) against the term x, extending the substitution s"""
    if isinstance(p, tuple) and p and p[0] == "var" and p[1] in pv:
        if p[1] in s:
            return s[p[1]] == x
        s[p[1]] = x
        return True
    if isinstance(p, tuple) and isinstance(x, tuple):
        return len(p) == len(x) and all(unify(a, b, pv, s) for a, b in zip(p, x))
    return p == x


def subst(x, s):
    if isinstance(x, tuple) and x and x[0] == "var" and x[1] in s:
        return s[x[1]]
    if isinstance(x, tuple):
        return tuple(subst(y, s) for y in x)
    return x


def replace_term(x, old, new):
    if x == old:
        return new
    if isinstance(x, tuple):
        return tuple(replace_term(y, old, new) for y in x)
    return x


def relabel_ops(x, op_from, op_to):
    """R of a defined order relation read for another order: links op_from become op_to (strictness too)"""
    if isinstance(x, tuple) and x and x[0] == "rel":
        ops = tuple(op_to if o == op_from else o for o in x[1])
        return ("rel", ops, tuple(relabel_ops(y, op_from, op_to) for y in x[2]))
    if isinstance(x, tuple):
        return tuple(relabel_ops(y, op_from, op_to) for y in x)
    return x


def expand_relation(op, a, b, env):
    """the defining formula of a defined relation (vocabulary row D : L :<=> R) matching the link a op b, or None.
    A row for <= also reads >=, <, > (the same R with the order changed), and either side order. Pattern variables
    declared in QQ match only terms of type Q that are not integers (an integer power of 2 is a rational term)."""
    for row in env.vocab.get("#rel", []):
        d, defrel = (row[1], row[2]) if row[0] == "ctx" else (("and", ()), row)
        lhs, rhs = defrel[1], defrel[2]
        if lhs[0] != "rel" or len(lhs[1]) != 1:
            continue
        pv, qq = set(), set()
        for c in flatten(d):
            if c[0] == "decl":
                for n in c[1]:
                    if n[0] == "var":
                        pv.add(n[1])
                        if c[2] == ("set", "QQ"):
                            qq.add(n[1])
        opl = lhs[1][0]
        # a row for an order symbol reads the four orders and both sides; another symbol (asymp, divides) is read
        # as written
        tries = ((a, b, op), (b, a, ORDER.get(op))) if opl in ORDER else ((a, b, op),)
        for x1, x2, o in tries:
            if o is None:
                continue
            if opl in ORDER:
                if o not in (opl, ORDER[opl], STRICT[opl], ORDER[STRICT[opl]]):
                    continue
            elif o != opl:
                continue
            s = {}
            if not (unify(lhs[2][0], x1, pv, s) and unify(lhs[2][1], x2, pv, s)):
                continue
            try:
                if any(infer_type(s[v], env) != "\u211a" for v in qq if v in s):
                    continue
            except Skip:
                continue
            body = rhs if o == opl else relabel_ops(rhs, opl, o)
            # bound names of the row that the matched terms use are renamed
            used = set()
            for v in s.values():
                free_vars(v, used)
            ren = {n: ("var", n + "_r") for n in bound_vars(body) if n in used or n in env.vars}
            body = subst(body, {**ren, **s}) if ren else subst(body, s)
            return body
    return None


def apply_on(x, fs, w):
    """x with every function name of fs that is not applied replaced by its value at w (the reading of "on")"""
    if not isinstance(x, tuple) or not x:
        return x
    if x[0] == "app":
        return (x[0], x[1], tuple(apply_on(a, fs, w) for a in x[2]), x[3])
    if x[0] == "var" and x[1] in fs:
        return ("app", x, (w,), "call")
    return tuple(apply_on(y, fs, w) for y in x)


def expand_textrel(x, env):
    """the defining formula of the relational word of x (a row D : t_0 w_1 t_1 ... :<=> R) with the arguments of x
    put in, or None. The pattern variables are the names among the row's arguments; a bound name of R that an
    argument uses is renamed."""
    for row in env.vocab.get("#rel", []):
        defrel = row[2] if row[0] == "ctx" else row
        lhs, rhs = defrel[1], defrel[2]
        if lhs[0] != "textrel" or lhs[1] != x[1] or len(lhs[2]) != len(x[2]):
            continue
        pv = set()
        for a in lhs[2]:
            free_vars(a, pv)
        pv = {v for v in pv if not v.endswith("[]")}
        s = {}
        if not all(unify(p, a, pv, s) for p, a in zip(lhs[2], x[2])):
            continue
        used = set()
        for v in s.values():
            free_vars(v, used)
        ren = {n: ("var", n + "_r") for n in bound_vars(rhs) if n in used or n in env.vars}
        return subst(rhs, {**ren, **s})
    return None


def components(names, declared):
    """the sequences x[] of names that are the components of a declared vector b_x"""
    return {n for n in names if n.endswith("[]") and "b_" + n[:-2] in declared}


# ---------------------------------------------------------------------------------------------------------
# operators the paper defines: a par b := R (an infix operator), par i in lo..hi, a_(i) := R (its fold)

DEFINED_OPS = {"par"}


def is_op_def(p):
    """a definition of an operator: a par b := R, or par i in lo..hi, a_(i) := R"""
    if p[0] != "def":
        return False
    lhs = p[1]
    if lhs[0] == "bin" and lhs[1] in DEFINED_OPS:
        return lhs[2][0] == "var" and lhs[3][0] == "var" and lhs[2] != lhs[3]
    return (lhs[0] in DEFINED_OPS and lhs[2] is not None and lhs[2][0] == "range" and lhs[3][0] == "app"
            and lhs[3][3] == "idx" and lhs[3][1][0] == "var" and lhs[3][2] == (("var", lhs[1]),))


def bound_rename(rhs, avoid):
    """rhs with its bound names that are in avoid renamed (so that substituted terms are not captured)"""
    ren = {}
    for n in bound_vars(rhs):
        if n in avoid:
            m = n + "'"
            while m in avoid or m in ren.values():
                m += "'"
            ren[n] = m

    def go(x):
        if not isinstance(x, tuple) or not x:
            return x
        if x[0] == "var" and x[1] in ren:
            return ("var", ren[x[1]])
        if x[0] in ("sum", "prod", "max", "min", "par") and x[1] in ren:
            return (x[0], ren[x[1]]) + tuple(go(y) for y in x[2:])
        return tuple(go(y) if isinstance(y, tuple) else y for y in x)
    return go(rhs) if ren else rhs


def replace_family(x, a, j, body):
    """x with each term a_(t) of the family a replaced by body at j = t"""
    if not isinstance(x, tuple) or not x:
        return x
    if x[0] == "app" and len(x) > 3 and x[3] == "idx" and x[1] == ("var", a) and len(x[2]) == 1:
        return T.subst_var(body, j, replace_family(x[2][0], a, j, body))
    return tuple(replace_family(y, a, j, body) if isinstance(y, tuple) else y for y in x)


def drop_range(x, rng):
    """x with the big operators over the range rng taken over the family range (no range)"""
    if not isinstance(x, tuple) or not x:
        return x
    if x[0] in ("sum", "prod", "max", "min", "par") and x[2] == rng:
        return (x[0], x[1], None) + tuple(drop_range(y, rng) for y in x[3:])
    return tuple(drop_range(y, rng) if isinstance(y, tuple) else y for y in x)


def match_op(d, y):
    """the definition d (a def node) applied to the term y, or None"""
    lhs, rhs = d[1], d[2]
    if lhs[0] == "bin":
        if y[0] != "bin" or y[1] != lhs[1]:
            return None
        avoid = free_vars(y[2]) | free_vars(y[3])
        return subst(bound_rename(rhs, avoid), {lhs[2][1]: y[2], lhs[3][1]: y[3]})
    if y[0] != lhs[0]:
        return None
    i, (lo, hi), a = lhs[1], lhs[2][1], lhs[3][1][1]
    j, dom, body = y[1], y[2], y[3]
    avoid = (free_vars(body) - {j}) | (free_vars(dom[1]) if dom and dom[0] == "range" else set())
    r = bound_rename(rhs, avoid)
    if dom is None:
        r = drop_range(r, lhs[2])
    elif dom[0] == "range":
        s = {}
        for pat, val in ((lo, dom[1][0]), (hi, dom[1][1])):
            if pat[0] == "var" and pat[1] != a:
                if s.get(pat[1], val) != val:
                    return None
                s[pat[1]] = val
            elif pat != val:
                return None
        r = subst(r, s)
    else:
        return None
    return replace_family(r, a, j, body)


def expand_ops(x, defs, depth=0):
    """x with the defined operators replaced by their definitions (innermost first)"""
    if not defs or not isinstance(x, tuple) or not x:
        return x
    if depth > 50:
        raise Skip("an operator definition that does not terminate")
    if not isinstance(x[0], str):
        return tuple(expand_ops(y, defs, depth) for y in x)
    y = (x[0],) + tuple(expand_ops(c, defs, depth) if isinstance(c, tuple) else c for c in x[1:])
    for d in defs:
        r = match_op(d, y)
        if r is not None:
            return expand_ops(r, defs, depth + 1)
    return y


def with_op_defs(parsed, vocab):
    """[(key, parts)] with the operator definitions taken out (of the items and the vocabulary) and expanded"""
    defs = list(vocab.get("#opdef", [])) + [p for _, ps in parsed for p in ps if is_op_def(p)]
    out = []
    for k, ps in parsed:
        rest = [expand_ops(p, defs) for p in ps if not is_op_def(p)]
        if rest:
            out.append((k, rest))
    return out


def check_scope(s_tree, env):
    undeclared = free_vars(s_tree) - set(env.vars) - index_vars(s_tree) - bound_vars(s_tree)
    undeclared -= components(undeclared, env.vars)
    if undeclared:
        raise Skip(f"undeclared {sorted(undeclared)}")


DIGIT_NAME = re.compile(r"([A-Za-z]+'*)_(\d+)('*)")  # k_1, and k'_1 or k_1' of the family k'


def family_digits(trees):
    """the names f_0, f_1 (a numeric subscript) read as the terms f_(0), f_(1) of a family f_(lo..hi) or a sequence
    f_(i) declared in the result, when the digit is at least a numeric lo and f_0 is not declared as a name of its
    own"""
    fams, own = {}, set()

    def collect(x):
        if isinstance(x, tuple) and x and isinstance(x[0], str):
            if x[0] == "family":
                fams[x[1]] = x[2]
            elif x[0] == "decl":
                own.update(n[1] for n in x[1] if n[0] == "var")
                for n in x[1]:
                    if n[0] == "app" and n[3] == "idx" and n[1][0] == "var":
                        fams.setdefault(n[1][1], ("num", "0"))  # a sequence a_(i): every numeric member
            elif x[0] == "def" and x[1][0] == "var":
                own.add(x[1][1])
            elif x[0] == "def" and x[1][0] == "app" and x[1][3] == "idx" and x[1][1][0] == "var":
                fams.setdefault(x[1][1][1], ("num", "0"))  # a family defined by a formula, e_(i) := t
            for y in x[1:]:
                collect(y)
        elif isinstance(x, (list, tuple)):
            for y in x:
                collect(y)

    def read(x):
        if isinstance(x, tuple) and x and isinstance(x[0], str):
            if x[0] == "var":
                m = DIGIT_NAME.fullmatch(x[1])
                f = m and m.group(1) + m.group(3)
                if m and f in fams and x[1] not in own:
                    lo = fams[f]
                    if lo[0] != "num" or int(m.group(2)) >= int(float(lo[1])):
                        return ("app", ("var", f), (("num", m.group(2)),), "idx")
                return x
            return (x[0],) + tuple(read(y) for y in x[1:])
        if isinstance(x, list):
            return [read(y) for y in x]
        if isinstance(x, tuple):
            return tuple(read(y) for y in x)
        return x

    collect(trees)
    return read(trees) if fams else trees


def conclusion_groups(items):
    """(the given items, [(key, items)]): the items of each conclusion, its continuation lines (key -) included,
    the first one under the key of the conclusion"""
    given, groups, key = [], [], None
    for k, q in items:
        if k != "-":
            key = k
        if key == "given":
            given.append((k, q))
            continue
        kk = key or "(1)"
        if groups and groups[-1][0] == kk:
            groups[-1][1].append((k, q))
        else:
            groups.append((kk, [(kk, q)]))
    # an operator definition of the result (\sit{parallel sum}{a par b := R}) is not a conclusion: every item reads
    # it, like the given clauses
    defs, kept = [], []
    for kk, its in groups:
        rest = []
        for k, q in its:
            (defs if op_def_item(q) else rest).append((k, q))
        if rest:
            kept.append((kk, [(kk, rest[0][1])] + rest[1:]))
    return given + [("given", q) for _, q in defs], kept


def op_def_item(q):
    """the item q (Q++) is formal and holds only operator definitions"""
    try:
        if T.is_formal(q) is False:
            return False
        parts = T.parse_qpp_item(q)
    except (ValueError, T.Hole):
        return False
    return bool(parts) and all(is_op_def(p) for p in parts)


def item_tag(label, k):
    """the tag of the item k of a result: lem:x(1), lem:x(sums)"""
    return label + (k if k.startswith("(") else f"({k})")


def item_ident(k):
    """the Lean name of the item k of a result: (1) is item_1, (2a) item_2a, then item_then"""
    return "item_" + (re.sub(r"[^A-Za-z0-9]+", "_", k.strip("()")).strip("_") or "1")


is_core = T.is_core


def core_only(items):
    """every conclusion among the items is a core item (is_core)"""
    keys, key = set(), None
    for k, _q in items:
        if k != "-":
            key = k
        if key != "given":
            keys.add(key)
    return bool(keys) and all(is_core(k) for k in keys)


def stand_alone(items):
    """the items, without the given when every conclusion among them is a core item (core_only); the operator
    definitions of the given (a par b := R) stay, as notation"""
    if not core_only(items):
        return list(items)
    out, key = [], None
    for k, q in items:
        if k != "-":
            key = k
        if key == "given" and not op_def_item(q):
            continue
        out.append(("given" if key == "given" else k, q))
    return out


def given_without_holes(items):
    """(items, holes): the clauses of the given with a hole taken out (a part between semicolons with a hole, or the
    clauses between commas with a hole within such a part, the formal ones kept in their order), and those clauses
    in Q++; a row of the given left empty is left out, and the row that continues it takes the key given"""
    out, holes, key, last = [], [], None, None
    for k, q in items:
        if k != "-":
            key = k
        if key == "given" and T.is_formal(q) is False:
            kept = []
            for part in split_parts(q):
                if T.is_formal(part) is not False:
                    kept.append(part)
                    continue
                pieces = split_parts(part, ",")
                holes += [x for x in pieces if T.is_formal(x) is False]
                rest = ", ".join(x for x in pieces if T.is_formal(x) is not False)
                if rest:
                    kept.append(rest)
            q = "; ".join(kept)
            if not q:
                continue
        out.append((key if k == "-" and last != key else k, q))
        last = key
    return out, holes


def hole_drops(parsed, holes):
    """the LaTeX of the clauses with a hole (given_without_holes) that the statement leaves out; Skip when a
    conclusion uses a name such a clause mentions (it may declare or define it) that no formal clause of the given
    declares (then the clause only adds hypotheses on it)"""
    formal = {key_base(n) for k, ps in parsed if k == "given" for n in names_declared(ps)}
    used = {key_base(n) for k, ps in parsed if k != "given" for p in ps for n in free_vars(p)}
    out = []
    for h in holes:
        tex = h[2:-1] if h.startswith("?{") and h.endswith("}") else h
        tex = re.sub(r"^(?:\\\s|\s)+", "", tex)
        clash = sorted((tex_bases(tex) & used) - formal)
        if clash:
            raise Skip(f"item given has a hole that mentions {', '.join(clash)}, which a conclusion uses")
        out.append(tex)
    return out


def statement(items, vocab=None):
    """(binders, hypotheses, conclusions) in Lean, from the statement items (conventions v1); style warnings in
    STMT_WARN. Core items stand alone (stand_alone). A clause of the given with a hole is left out, so the statement
    is stronger than the paper's, when no conclusion needs a name it mentions (hole_drops); so is a clause of the
    given that does not compile; both are listed in STMT_DROPPED"""
    try:
        return read_statement(items, vocab)
    except Skip as e:
        if str(e).startswith("undeclared") and core_only(items):
            raise Skip(f"{e} (a core item stands alone, without the given: it declares its names before its colon)")
        raise


def read_statement(items, vocab=None):
    """statement, read"""
    STMT_WARN.clear()
    STMT_DROPPED.clear()
    T.LEAN_CLASSICAL[0] = False
    env = Env(vocab or dict(T.PRELUDE))
    binders, hyps, concl = [], [], []
    key = None
    parsed = []
    items, holes = given_without_holes(stand_alone(items))
    for k, q in items:
        if k != "-":
            key = k
        if T.is_formal(q) is False:
            raise Skip(f"item {key} has a hole")
        try:
            parsed.append((key, T.parse_qpp_item(q)))
        except ValueError as e:
            raise Skip(f"item {key}: {e}")
    if holes:
        STMT_DROPPED.extend(hole_drops(parsed, holes))
    parsed = family_digits(parsed)
    parsed = with_op_defs(parsed, env.vocab)
    if any(minmax_in(p) for _, ps in parsed for p in ps):
        STMT_WARN.append("a min or a max in the statement: the semifield form (trop, par, or a bound with its "
                         "witness) shows more structure")
    # the context of the paper (rows \sit{context}{n in Z>=1}): a row that declares a name the statement uses is
    # read whole, first (its declarations, and its other clauses once their names are in scope)
    ctx = env.vocab.get("#context", [])
    if ctx:
        used = used_names([p for _, ps in parsed for p in ps], env.vocab)
        used -= names_declared([p for _, ps in parsed for p in ps])  # a name the statement declares shadows the context
        for part in ctx:
            for c in context_row(part, used, env):
                lean_hyp(c, env, binders, hyps)
    GIVEN_NAMES.clear()
    GIVEN_NAMES.update(n for key, ps in parsed if key == "given" for p in ps for c in flatten(p) if c[0] == "decl"
                       for n in names_declared([c]))
    later = set(GIVEN_NAMES) | {seq_key(n) for n in GIVEN_NAMES}
    used_concl = with_vectors({n for k, ps in parsed if k != "given" for p in ps for n in free_vars(p)})
    for key, parts in parsed:
        if key == "given":
            for part in parts:
                for c in flatten(part):
                    snap = (len(binders), len(hyps), dict(env.vars))
                    try:
                        if r1_clause(c):
                            raise Skip(R1_REASON)
                        if c[0] == "rel":
                            # a formal clause on names declared nowhere (p = 1, w_0 = (a^0, t^* 1)) cannot elaborate
                            missing = (free_vars(c) - set(env.vars) - later - bound_vars(c)
                                       - {n for n in free_vars(c) if is_index_name(n)})
                            missing -= components(missing, env.vars)
                            if len(c[1]) == 1 and c[1][0] in ("subseteq", "subset") and c[2][0][0] == "var":
                                missing.discard(c[2][0][1])  # S subseteq X declares S
                            if missing:
                                raise Skip(f"undeclared {sorted(missing)}")
                        if c[0] not in ("decl", "def", "ctx", "rel") and not family_decl(c) and not (
                                c[0] == "imp" and c[2][0] == "def"):
                            check_scope(c, env)
                        lean_hyp(c, env, binders, hyps)
                    except (Skip, T.Hole, ValueError, KeyError):
                        # a clause of the given that does not compile is left out, as a clause with a hole, when no
                        # conclusion uses a name it declares, defines or mentions that is not declared before it
                        del binders[snap[0]:]
                        del hyps[snap[1]:]
                        env.vars.clear()
                        env.vars.update(snap[2])
                        own = with_vectors(free_vars(c) | names_declared([c]) | defined_keys(c)) - with_vectors(set(snap[2]))
                        if c[0] == "def" and c[1][0] == "app":
                            own -= {a[1] for a in c[1][2] if a[0] == "var"}  # u_(h) := E: h is bound by the definition
                        if own & used_concl:
                            raise
                        STMT_DROPPED.append(T.to_qpp(c))
            continue
        if key is None or key in ("then",):
            key = key or "(1)"
        for part in parts:
            check_scope_part(part, env)
            if concl and concl[-1][0] == key:
                concl[-1] = (key, concl[-1][1] + [part])
            else:
                concl.append((key, [part]))
    out = []
    for k, ps in concl:
        ss = [lean_prop(p, env) for p in ps]
        out.append((k, " \u2227 ".join(f"({s})" for s in ss) if len(ss) > 1 else ss[0]))
    bs = " ".join(f"({n} : {typ})" for n, typ in group_binders(binders))
    HYP_PREFIX[0] = hyp_prefix([n for n, _ in binders])
    hs = " ".join(f"({hyp_name(i + 1)} : {h})" for i, h in enumerate(hyps))
    LAST_ENV[0] = env
    LAST_HYPS[:] = hyps
    return bs, hs, out


LAST_ENV = [None]
GIVEN_NAMES = set()  # the names that the given of the statement being read declares (in any of its clauses)
LAST_HYPS = []  # the Lean hypotheses of the last statement, h_1, h_2, ... in order
HYP_PREFIX = ["h"]  # the prefix of the hypothesis names of the last statement


def hyp_prefix(names):
    """h, unless a name of the statement is h with subscript digits (B and C name units and maps h_1, h_2): then a
    prefix no name has, so that a hypothesis never shadows a variable"""
    for cand in ("h", "hyp", "hh", "hyp'"):
        if not any(re.fullmatch(re.escape(cand) + "[\u2080-\u2089]+", n) for n in names):
            return cand
    raise Skip("no free prefix for the names of the hypotheses")


def hyp_name(i):
    return HYP_PREFIX[0] + str(i).translate(T.SUB_DIGITS)
LAST_WARNINGS = []  # (label, warning) of the last generated file


def names_declared(trees):
    """the names that the trees declare or bind anywhere (x in S, x := t, forall x, exists x)"""
    out = set()
    for t in trees:
        for y in T.subterms(t):
            if y[0] == "decl":
                out.update(n[1] if n[0] in ("var", "family") else n[1][1] if n[0] == "app" else None for n in y[1])
            elif y[0] == "def" and y[1][0] == "var":
                out.add(y[1][1])
            elif y[0] in ("exists", "forall"):
                out.update(v[1] for v in y[1] if v[0] == "var")
            elif y[0] == "rel" and y[1] in (("subseteq",), ("subset",)) and y[2][0][0] == "var":
                out.add(y[2][0][1])  # S subseteq X declares S
    out.discard(None)
    return out


def context_row(part, used, env):
    """the clauses of a context row that a statement reads: all of them when the row declares a name the statement
    uses (used), nothing otherwise; a clause whose names are not in scope blocks the statement (it is a hypothesis)"""
    cs = flatten(part)

    def subset_decl(c):
        return c[0] == "rel" and c[1] in (("subseteq",), ("subset",)) and c[2][0][0] == "var"
    if not any((c[0] == "decl" and any(n[0] == "var" and n[1] in used for n in c[1]))
               or (subset_decl(c) and c[2][0][1] in used) for c in cs):
        return []
    out, scope = [], set(env.vars)
    for c in cs:
        if subset_decl(c):
            out.append(c)  # O subseteq Q^d declares O
            scope.add(c[2][0][1])
            continue
        if c[0] in ("decl", "def") or family_decl(c):
            out.append(c)
            scope |= declared_in(("imp", c, ("tuple", ())))
            if c[0] == "def" and c[1][0] == "var":
                scope.add(c[1][1])
            if family_decl(c):
                scope |= {seq_key(n) for n in family_decl(c)[2]}
            continue
        missing = free_vars(c) - scope - free_index_vars(c) - bound_vars(c)
        if missing:
            # dropping a clause of the setting would drop a hypothesis (e : Q>0 -> Z without its spec is any e)
            raise Skip(f"a clause of the context names {sorted(missing)}, which the context does not declare")
        out.append(c)
    return out


def used_names(trees, vocab, seen=None):
    """the free names of the trees and of the definitions they use (word sets, relation rows), transitively"""
    seen = set() if seen is None else seen
    acc = set()
    rows = vocab.get("#rel", [])

    def walk(x):
        if not isinstance(x, tuple) or not x:
            return
        if x[0] == "word" and x[1] not in seen and isinstance(vocab.get(x[1]), dict) and "set" in vocab[x[1]]:
            seen.add(x[1])
            acc.update(used_names([vocab[x[1]]["set"]], vocab, seen))
        if x[0] in ("textrel", "rel") and ("rel", x[1]) not in seen:
            for row in rows:
                d = row[2] if row[0] == "ctx" else row
                lhs = d[1]
                if (x[0] == "textrel" and lhs[0] == "textrel" and lhs[1] == x[1]) or (
                        x[0] == "rel" and lhs[0] == "rel" and lhs[1]
                        and (set(x[1]) & set(ORDER) or lhs[1][0] in x[1])):
                    seen.add(("rel", x[1]))
                    pv = set()
                    for a in lhs[2]:
                        free_vars(a, pv)
                    acc.update(used_names([d[2]], vocab, seen) - pv - bound_vars(d[2]))
        for y in kids(x):
            walk(y)
    for t in trees:
        free_vars(t, acc)
        walk(t)
    return acc


def check_scope_part(part, env):
    """the free names of a conclusion are declared in it or in given, or are indices"""
    local = set(env.vars)

    def decls(x):
        if x[0] in ("imp", "ctx"):
            for c in flatten(x[1]):
                if c[0] == "decl":
                    for n in c[1]:
                        local.add(n[1] if n[0] == "var" else seq_key(n[1] if n[0] == "family" else n[1][1]))
                elif c[0] == "def" and c[1][0] == "var":
                    local.add(c[1][1])
                elif c[0] == "def" and c[1][0] == "app" and c[1][1][0] == "var":
                    # rho(t) := E, sigma_(a, b) := E in a context: the name, and its parameters bound by the definition
                    local.add(seq_key(c[1][1][1]) if c[1][3] == "idx" else c[1][1][1])
                    local.update(a[1] for a in c[1][2] if a[0] == "var")
                elif family_decl(c):
                    local.update(seq_key(n) for n in family_decl(c)[2])
                elif c[0] == "rel" and c[1] in (("subseteq",), ("subset",)) and c[2][0][0] == "var":
                    local.add(c[2][0][1])  # S subseteq X declares S
                elif c[0] == "rel":
                    for a in c[2]:
                        if a[0] == "var" and is_index_name(a[1]):
                            local.add(a[1])
            decls(x[2])
        elif x[0] in ("exists", "forall"):
            for v in x[1]:
                if v[0] == "var":
                    local.add(v[1])
            decls(x[3])
        elif x[0] == "and":
            for c in x[1]:
                decls(c)
    decls(part)
    undeclared = free_vars(part) - local - index_vars(part) - bound_vars(part)
    undeclared -= components(undeclared, local)
    if undeclared:
        raise Skip(f"undeclared {sorted(undeclared)}")


def group_binders(binders):
    out = []
    for n, typ in binders:
        if out and out[-1][1] == typ:
            out[-1] = (out[-1][0] + " " + n, typ)
        else:
            out.append((n, typ))
    return out


def quantified(t, decl, wrap=True):
    s = T.to_lean(t)
    idx = sorted(index_vars(t) - set(decl))
    if idx:
        return f"\u2200 {' '.join(T.lean_name(i) for i in idx)}, {s}"
    return s


# ---------------------------------------------------------------------------------------------------------
# words

WTOK = re.compile(r"\s*(\[|\]|\(|\)|;|,|\^v|\bo\b|[A-Za-z][A-Za-z0-9_']*(?::[A-Za-z0-9_:\-]+)?(?:\(\d+\))?)")


def split_data(w, i):
    depth, j = 0, i
    while j < len(w):
        if w[j] == "[":
            depth += 1
        elif w[j] == "]":
            depth -= 1
            if depth == 0:
                return w[i + 1:j], j + 1
        j += 1
    raise Skip("unbalanced data")


def lean_key(s):
    """a Lean proposition up to spaces and outer parentheses"""
    s = re.sub(r"\s+", " ", s.strip())
    while s.startswith("(") and s.endswith(")") and balanced(s[1:-1]):
        s = s[1:-1].strip()
    return s


def balanced(s):
    depth = 0
    for ch in s:
        depth += ch in "([{\u27e8"
        depth -= ch in ")]}\u27e9"
        if depth < 0:
            return False
    return depth == 0


FLIP = {"<=": ">=", ">=": "<=", "<": ">", ">": "<"}


def hyp_by_content(c, hyps):
    """the Lean name of the hypothesis that reads as the claim c (the same Lean proposition, x >= 0 and 0 <= x
    alike), or None; hyps: [(name, proposition)]"""
    if c[0] == "rel" and len(c[1]) > 1:
        return None  # a chain is several hypotheses, one per link: a citation names one link
    forms = [c]
    if c[0] == "rel" and c[1][0] in FLIP:
        forms.append(("rel", (FLIP[c[1][0]],), (c[2][1], c[2][0])))
    keys = set()
    for f in forms:
        try:
            keys.add(lean_key(lean_prop(f, LAST_ENV[0])))
        except (Skip, T.Hole, KeyError, ValueError):
            pass
    found = [n for n, h in hyps if lean_key(h) in keys]
    return found[0] if found else None


def by_content(t, hyps):
    """certificate data with its citations resolved: a parenthesized relation (x preceq y) in the data of a word
    is the hypothesis that reads the same, eq[(x preceq y) + 2 * (y preceq z)] is eq[h_1 + 2 * h_2]; a
    citation that matches no hypothesis is an error (a typo must not turn into a claim); a relation without
    parentheses is a claim, proved first"""
    if not (isinstance(t, tuple) and t):
        return t
    if isinstance(t[0], str):
        if t[0] == "cite":
            name = hyp_by_content(t[1], hyps)
            if name is None:
                raise Skip(f"the citation ({T.to_qpp(t[1])}) matches no hypothesis")
            return ("leanraw", name)
        return (t[0],) + tuple(by_content(y, hyps) for y in t[1:])
    return tuple(by_content(y, hyps) for y in t)


def in_scope(n, scope):
    """a Q++ name of a claim is in scope: declared by the statement, introduced by the proof, or built in"""
    env = LAST_ENV[0]
    if n in env.vars or seq_key(n) in env.vars or ("b_" + n) in env.vars:
        return True
    if ("var", n) in BUILTIN_FUNS or n in env.vocab:
        return True
    return T.lean_name(n.rstrip("[]")) in scope or env.lean(n) in scope


def word_to_lean(w, hyps=(), scope=None):
    """(haves, final word, uses search) for a Q++ word: claims hoisted into haves, data translated to Lean; hyps,
    the hypotheses in scope [(name, proposition)], resolve the citations; scope, the Lean names a claim may use"""
    if "{" in w or ":" in re.sub(r"\[[^\]]*\]", "", w).replace(":=", ""):
        raise Skip("formulas or a gloss between the factors")
    out, haves, i = [], [], 0
    claims = []
    while i < len(w):
        if w[i] == "[":
            data, i = split_data(w, i)
            T.DATA_MODE[0] = True  # a parenthesized relation is a citation
            try:
                terms = T.parse_qpp_list(data)
            except ValueError as e:
                raise Skip(f"data: {e}")
            finally:
                T.DATA_MODE[0] = False
            terms = [by_content(t, hyps) for t in terms]
            if all(T.is_claim(t) for t in terms):
                head = out[-1] if out else None
                if head == "^v" and len(out) >= 2:
                    head = out[-2] + "^v"
                if not head or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*(\^v)?", head):
                    raise Skip("claim without a verb")
                if head.startswith(("ind_", "iota_")):
                    raise Skip(f"{head}[claim]: induction needs the word it runs, {head}(word)")
                if scope is not None:
                    for c in terms:
                        out_of_scope = sorted(n for n in free_names(c) if not in_scope(n, scope))
                        if out_of_scope:
                            raise Skip(f"the claim {T.to_qpp(c)} uses {', '.join(out_of_scope)}, which the statement "
                                       f"does not declare (a name of the proof)")
                links = []
                for c in terms:  # a chain claim is one claim per link, as a chain hypothesis is
                    if c[0] == "rel" and len(c[1]) > 1:
                        links += [("rel", (op,), (a, b)) for op, a, b in zip(c[1], c[2], c[2][1:])]
                    else:
                        links.append(c)
                claims.append((len(out) - 1, head, [T.to_lean(c) for c in links]))
            elif any(T.is_claim(t) for t in terms):
                raise Skip("data mixing claims and certificates")
            else:
                out[-1] += "[" + ", ".join(T.to_lean(t) for t in terms) + "]"
            continue
        m = WTOK.match(w, i)
        if not m or m.end() == i:
            if w[i].isspace():
                i += 1
                continue
            raise Skip(f"word: cannot read {w[i:i + 12]!r}")
        tok = m.group(1)
        if ":" in tok:
            raise Skip(f"reference {tok} (no Lean name yet)")
        out.append(tok)
        i = m.end()
    search = bool(claims)
    # claims are proved by their verb, in the order of the word read forward (right to left); the factor that
    # carries a claim leaves the word, which then closes the goal from the claims
    for pos, head, props in sorted(claims, key=lambda c: -c[0]):
        for prop in props:
            haves.append(f"have : {prop} := by qpp! {head}")
        out[pos] = None
    rest = []
    for n, tok in enumerate(out):
        if tok is None:
            if rest and rest[-1] == "o":
                rest.pop()
            nxt = next((x for x in out[n + 1:] if x is not None), None)
            if (not rest or rest[-1] in (";", ",", "(")) and (nxt is None or nxt in (";", ",", ")")):
                rest.append("eq")  # the claim alone closes its part (a law of the symbols)
            continue
        if tok == "o" and (not rest or rest[-1] in ("o", ";", ",", "(")):
            continue
        rest.append(tok)
    while rest and rest[-1] == "o":
        rest.pop()
    out = rest
    if not out:
        out = ["eq"]
    final = " ".join(out)
    final = re.sub(r"\s+([;,])", r" \1", final).replace("( ", "(").replace(" )", ")")
    final = re.sub(r"\s+\^v", "^v", final)
    return haves, final, search


def intro_names(c, hyps=None):
    """the names to introduce for the leading binders and hypotheses of a Lean proposition (hypotheses: _), and
    the propositions of those hypotheses (appended to hyps)"""
    names = []
    hyps = [] if hyps is None else hyps
    while True:
        c = c.strip()
        if c.startswith("\u2200 "):
            head, rest = split_comma(c[2:])
            if head is None:
                break
            head = re.sub(r":[^()]*\)", ")", head)
            head = re.sub(r":[^()]*$", "", head)
            names += [n for n in head.replace("(", " ").replace(")", " ").split()]
            c = rest
            continue
        a, rest = split_arrow(c)
        if a is None:
            break
        names.append("_")
        hyps.append(a.strip())
        c = rest
    INTRO_GOAL[0] = c
    return names


INTRO_GOAL = [""]  # the goal that intro_names leaves


def conjuncts(goal):
    """the number of top-level conjuncts of a Lean proposition"""
    depth, n = 0, 1
    for ch in goal:
        if ch in "([{\u27e8":
            depth += 1
        elif ch in ")]}\u27e9":
            depth -= 1
        elif ch == "\u2227" and depth == 0:
            n += 1
        elif ch in "\u2203\u2200\u2192\u2228\u2194" and depth == 0:
            return 1
    return n


def split_comma(s):
    depth = 0
    for i, ch in enumerate(s):
        if ch in "([{\u27e8":
            depth += 1
        elif ch in ")]}\u27e9":
            depth -= 1
        elif ch == "," and depth == 0:
            return s[:i], s[i + 1:]
    return None, s


def split_arrow(s):
    depth = 0
    for i, ch in enumerate(s):
        if ch in "([{\u27e8":
            depth += 1
        elif ch in ")]}\u27e9":
            depth -= 1
        elif ch == "\u2192" and depth == 0:
            return s[:i], s[i + 1:]
        elif ch in ",\u2203\u2200" and depth == 0:
            return None, s
    return None, s


def intros_needed(concl, k):
    """the names to introduce for conclusion k (hypotheses: _), and the hypotheses introduced, in order"""
    c = dict((key.strip("()"), s) for key, s in concl)[k]
    hyps = []
    return intro_names(c, hyps), hyps


def proof(lines, concl):
    if not lines:
        raise Skip("no proof lines")
    byitem = {k.strip("()"): w for k, w in lines}
    keys = [k.strip("()") for k, _ in concl]
    missing = [k for k in keys if k not in byitem]
    if missing:
        raise Skip(f"no line for {missing}")
    blocks = []
    for k in keys:
        ns, more = intros_needed(concl, k)
        n = len(LAST_HYPS)
        ns = [x if x != "_" else hyp_name(n + 1 + ns[:j].count("_")) for j, x in enumerate(ns)]
        hyps = [(hyp_name(i + 1), h) for i, h in enumerate(list(LAST_HYPS) + more)]
        scope = {v["lean"] for v in LAST_ENV[0].vars.values()} | {x for x in ns if x != "_"}
        goal = INTRO_GOAL[0]
        haves, final, search = word_to_lean(byitem[k], hyps, scope)
        if final == "eq" and conjuncts(goal) > 1:
            final = " ; ".join(["eq"] * conjuncts(goal))  # the claims close a conjunction link by link
        blocks.append(([f"intro {' '.join(ns)}"] if ns else []) + [*haves, f"qpp{'!' if search else ''} {final}"])
    if len(blocks) == 1:
        return ["  " + s for s in blocks[0]]
    out = ["  refine \u27e8" + ", ".join("?_" for _ in blocks) + "\u27e9"]
    for b in blocks:
        out.append("  \u00b7 " + b[0])
        out += ["    " + s for s in b[1:]]
    return out


def item_results(r, vocab):
    """the conclusions of a result, one by one, each with the given clauses: (key, (bs, hs, concl) or None, why),
    yielded right after its statement is read (LAST_ENV and LAST_HYPS are its own); none for a single conclusion.
    An item stands when it and the given are formal and it uses no name of another item."""
    given, groups = conclusion_groups(r["items"])
    if len(groups) < 2:
        return
    for k, its in groups:
        try:
            st = statement(given + its, vocab)
            if not st[2]:
                raise Skip("no conclusion")
        except Skip as e:
            yield k, None, str(e)
            continue
        except (T.Hole, ValueError, KeyError) as e:
            yield k, None, f"term outside the Lean printer: {e}"
            continue
        yield k, st, ""


LAST_ITEMS = {}  # label -> {"stated": [keys], "proved": [keys], "not": {key: why}}: results generated item by item
LAST_DROPPED = {}  # tag -> the clauses of the given with a hole that its match example leaves out
LAST_CORE = set()  # the tags of the match examples whose conclusions are all core items (is_core)


def dropped_note():
    """the clauses of the given that the statement just read leaves out (a stronger statement than the paper's)"""
    if not STMT_DROPPED:
        return ""
    def short(t):
        t = " ".join(t.split()).replace("-/", "- /")
        return t if len(t) <= 80 else t[:77] + "..."
    return "; without the given clauses with a hole (a stronger statement): " + " | ".join(short(t) for t in STMT_DROPPED)


def generate(text, namespace=None):
    q = read_qpp(text)
    ns = namespace or f"Qpp.{q['paper'] or 'Paper'}"
    out = ["import QPP", "", "/-! Generated by qpp/qpp2lean.py from the Q++ file of the paper; do not edit. -/", "",
           "set_option linter.unusedVariables false", "", "open QPP", "", f"namespace {ns}", ""]
    made, skipped, stated, proved, warns = [], [], [], [], []
    LAST_ITEMS.clear()

    def emit(tag, ident, bs, hs, concl, lines):
        """the statement and, when its proof generates, the theorem; None or the reason the proof is not"""
        goal = " \u2227 ".join(f"({c})" if len(concl) > 1 else c for _, c in concl)
        warns.extend((tag, w) for w in dict.fromkeys(STMT_WARN) if (tag, w) not in warns)
        start = len(out)
        if T.LEAN_CLASSICAL[0]:
            out.append("open Classical in")  # a filter by membership in a set (decidable classically)
        out.append(f"/-- [{tag}] the statement{dropped_note()} -/")
        out.append(f"abbrev {ident}.statement : Prop :=")
        out.append(f"  \u2200 {' '.join(x for x in (bs, hs) if x)}, {goal}".replace("  \u2200 , ", "  "))
        out.append("")
        stated.append((tag, start + 1, len(out)))
        try:
            with names(LAST_ENV[0]):
                body = proof(lines, concl)
        except Skip as e:
            return str(e)
        except (T.Hole, ValueError, KeyError) as e:
            return f"term outside the Lean printer: {e}"
        start = len(out)
        if T.LEAN_CLASSICAL[0]:
            out.append("open Classical in")
        out.append(f"/-- [{tag}] -/")
        out.append(f"theorem {ident} {bs} {hs} :".replace("  ", " "))
        out.append(f"    {goal} := by")
        out.extend(body)
        out.append("")
        made.append(tag)
        proved.append((tag, start + 1, len(out)))
        return None

    for r in q["results"]:
        if r["kind"] in ("proof",) and not r["items"]:
            skipped.append((r["label"], "proof without a statement in the file"))
            continue
        ident = lean_ident(r["label"])
        try:
            bs, hs, concl = statement(r["items"], q["vocab"] or None)
            if not concl:
                raise Skip("no numbered conclusion")
        except Skip as e:
            whole = str(e)
        except (T.Hole, ValueError, KeyError) as e:
            whole = f"term outside the Lean printer: {e}"
        else:
            why = emit(r["label"], ident, bs, hs, concl, r["lines"])
            if why is None:
                continue
            # the whole statement stands but its proof is not generated: the items whose proofs generate, one by one
            done = {"stated": [], "proved": [], "not": {}}
            for k, st, w in item_results(r, q["vocab"] or None) if len(concl) > 1 else ():
                if st is None:
                    continue
                try:
                    with names(LAST_ENV[0]):
                        proof(r["lines"], st[2])
                except (Skip, T.Hole, ValueError, KeyError) as e:
                    done["not"][k] = f"proof: {e}"
                    continue
                if emit(item_tag(r['label'], k), f"{ident}.{item_ident(k)}", *st, r["lines"]) is None:
                    done["stated"].append(k)
                    done["proved"].append(k)
            if done["proved"]:
                LAST_ITEMS[r["label"]] = done
            skipped.append((r["label"], f"stated; proof: {why}" + (
                f"; items proved: {', '.join(done['proved'])}" if done["proved"] else "")))
            continue
        # the whole statement does not stand: its conclusions one by one, each with the given clauses
        done = {"stated": [], "proved": [], "not": {}}
        for k, st, w in item_results(r, q["vocab"] or None):
            if st is None:
                done["not"][k] = w
                continue
            done["stated"].append(k)
            w2 = emit(item_tag(r['label'], k), f"{ident}.{item_ident(k)}", *st, r["lines"])
            if w2 is None:
                done["proved"].append(k)
            else:
                done["not"][k] = f"stated; proof: {w2}"
        if not done["stated"]:
            skipped.append((r["label"], whole))
            continue
        LAST_ITEMS[r["label"]] = done
        skipped.append((r["label"], "items: stated " + ", ".join(done["stated"]) + "; "
                        + "; ".join(f"{k} {w}" for k, w in done["not"].items())))
    out.append(f"end {ns}")
    out.append("")
    out.append("/-! Not generated (" + str(len(skipped)) + "):")
    for lab, why in skipped:
        out.append(f"* {lab}: {why}")
    out.append("-/")
    if warns:
        out.append("")
        out.append("/-! Warnings (" + str(len(warns)) + "), the statements are generated as they read:")
        for lab, w in warns:
            out.append(f"* {lab}: {w}")
        out.append("-/")
    LAST_WARNINGS[:] = warns
    LAST_SPANS.clear()
    LAST_SPANS.update({"stated": stated, "proved": proved})
    return "\n".join(out) + "\n", made, skipped


MATCH_MAX = 8  # declarations tried per conclusion


def match_try(d):
    """one attempt to prove the goal by the declaration d: by elimination (the hypotheses as they are), or by
    applying d and closing its premises (memberships of index ranges read as bounds); each with a small budget"""
    return (f"(set_option maxHeartbeats 40000 in (apply {d} <;> first | assumption | "
            f"(refine \u27e8?_, ?_\u27e9 <;> assumption) | positivity | linarith | "
            f"(intros; simp_all [Finset.mem_Icc]; done)))")


def count_binders(s):
    """the names that a string of binders (x u : Q) (h_1 : forall i : N, ...) binds: the names before the first
    colon of each top-level group, not the names inside the types"""
    n, depth, start = 0, 0, 0
    for i, ch in enumerate(s):
        if ch in "([{\u27e8":
            if depth == 0:
                start = i + 1
            depth += 1
        elif ch in ")]}\u27e9":
            depth -= 1
            if depth == 0:
                n += len(s[start:i].split(" : ", 1)[0].split())
    return n


def generate_match(text, refs, imports, namespace=None, premises=None, kernel=()):
    """the match check: each formal statement, proved by a hand-written declaration tagged with its label (and its
    item, when the tags give items); refs is the label map of qpp/leanrefs.py. kernel lists the (label, item) the
    kernel backend proves (qpp/leanrefs.py, kernel_items): their statement is the row itself, so they are left out. premises (qpp/leanrefs.py,
    cited_premises) gives the cited facts a declaration takes, `structure X : Prop` with no parameters: the example
    takes them as hypotheses, `example (hc_1 : X) : lem_x.statement`, so that it reads "given the cited theorem, the
    statement of the paper follows from the declaration", and `assumption` closes the premise that `apply` leaves"""
    premises = premises or {}
    kernel = {(lab, (item or "").strip("()")) for lab, item in kernel}
    q = read_qpp(text)
    ns = (namespace or f"Qpp.{q['paper'] or 'Paper'}") + ".Match"

    def kerneled(label, k):
        return (label, (k or "").strip("()")) in kernel
    out = ["import QPP"] + [f"import {m}" for m in imports] + [
        "", "/-! Generated by qpp/qpp2lean.py: the statements of the paper's LaTeX, proved by the hand-written Lean"
        " declarations that carry their labels. -/", "", "set_option linter.unusedVariables false",
        "-- the alternatives tried by the match are not all used", "set_option linter.unusedTactic false",
        "set_option linter.unreachableTactic false", "set_option linter.unnecessarySeqFocus false",
        "set_option maxHeartbeats 2000000", "",
        "open QPP", "", f"namespace {ns}", ""]
    spans, skipped = [], []
    LAST_DROPPED.clear()
    LAST_CORE.clear()

    def candidates(decls, k):
        """the theorems that may prove the conclusion k: those tagged with the item k first, then those tagged with
        the label alone (no fallback to the declarations of other items: a declaration of item (2) is no candidate
        for item (1)); for a conclusion without an item key, the label-alone ones first"""
        item = k.strip("()") if k else None  # (2), (2a), (sums): the declarations tagged with that item
        thms = [d for d in decls if d[2] in ("theorem", "lemma")]
        tagged = [d[0] for d in thms if item is not None and d[1] is not None and d[1].strip("()") == item]
        alone = [d[0] for d in thms if d[1] is None]
        rest = [d[0] for d in thms if item is None and d[1] is not None]
        return (tagged + alone + rest)[:MATCH_MAX]

    def example(tag, ident, bs, hs, concl, decls):
        """the example of one statement; False (nothing written) when a conclusion has no candidate. First a plain
        type check, `exact D`, for a declaration that states the compiled statement (apply could assign its
        metavariables from the wrong hypothesis); then, on what is left, the conclusions one by one by apply"""
        cands_of = [candidates(decls, k) for k, _ in concl]
        if not all(cands_of):
            return False
        goal = " \u2227 ".join(f"({c})" if len(concl) > 1 else c for _, c in concl)
        start = len(out)
        if T.LEAN_CLASSICAL[0]:
            out.append("open Classical in")  # a filter by membership in a set (decidable classically)
        out.append(f"abbrev {ident}.statement : Prop :=")
        out.append(f"  \u2200 {' '.join(x for x in (bs, hs) if x)}, {goal}".replace("  \u2200 , ", "  "))
        out.append("")
        used = list(dict.fromkeys(d for cs in cands_of for d in cs))
        facts = sorted({p for d in used for p in premises.get(d, [])})
        given = "".join(f" (hc_{i} : {p})" for i, p in enumerate(facts, 1))
        out.append(f"/-- [{tag}] matched by: " + ", ".join(sorted(used))
                   + (f"; given the cited facts {', '.join(facts)}" if facts else "") + dropped_note() + " -/")
        if STMT_DROPPED:
            LAST_DROPPED[tag] = list(STMT_DROPPED)
        if all(is_core(k) for k, _ in concl):
            LAST_CORE.add(tag)  # the example states a core of the result, not its statement
        out.append(f"example{given} : {ident}.statement := by")
        exacts = []
        for d in used[:MATCH_MAX]:
            exacts.append(f"exact {d}")
            if premises.get(d):
                exacts.append(f"exact {d} \u2039_\u203a")  # the cited fact as the first explicit argument
        out.append("  first")
        out.extend(f"  | {e}" for e in exacts)
        out.append("  | skip")
        out.append("  all_goals")
        n_bind = count_binders(bs) + count_binders(hs)
        if n_bind:
            out.append("    intro " + " ".join(["_"] * n_bind))
        if len(concl) > 1:
            out.append("    refine \u27e8" + ", ".join("?_" for _ in concl) + "\u27e9")
        for (k, c), cands in zip(concl, cands_of):
            ns_intro = intro_names(c)
            lead = "    \u00b7 " if len(concl) > 1 else "    "
            body = []
            if ns_intro:
                body.append("intro " + " ".join("_" for _ in ns_intro))
            body.append("first")
            body += [f"  | {match_try(d)}" for d in cands]
            body.append("  | (refine \u27e8?_, ?_\u27e9 <;> first")
            body += [f"      | {match_try(d)}" for d in cands]
            body[-1] += ")"
            out.append(lead + body[0])
            out.extend(("      " if len(concl) > 1 else "    ") + b for b in body[1:])
        out.append("")
        spans.append((tag, start + 1, len(out)))
        return True

    def by_items(r, ident, decls, reason):
        """the conclusions one by one: an item stands with the given clauses, matched by the declarations tagged
        with that item or with the label alone"""
        n, missing = 0, []
        for k, st, w in item_results(r, q["vocab"] or None):
            if kerneled(r["label"], k):
                n += 1  # proved by the kernel
            if st is None or kerneled(r["label"], k):
                continue
            if example(item_tag(r['label'], k), f"{ident}.{item_ident(k)}", *st, decls):
                n += 1
            else:
                missing.append(item_tag(r["label"], k))
        for tag in missing:
            skipped.append((tag, "no declaration tagged with the item or with the label alone"))
        if not n and not missing:
            skipped.append((r["label"], reason))

    for r in q["results"]:
        decls = refs.get(r["label"], [])
        if not decls:
            continue
        ident = lean_ident(r["label"])
        try:
            bs, hs, concl = statement(r["items"], q["vocab"] or None)
            concl = [(k, c) for k, c in concl if not kerneled(r["label"], k)]
            if not concl:
                raise Skip("no numbered conclusion")
        except (Skip, T.Hole, ValueError, KeyError) as e:
            by_items(r, ident, decls, str(e))
            continue
        if not example(r["label"], ident, bs, hs, concl, decls):
            # a conclusion with no candidate: the others are matched one by one
            by_items(r, ident, decls, "a conclusion has no declaration")
    out.append(f"end {ns}")
    out.append("")
    LAST_SPANS.clear()
    LAST_SPANS.update({"matched": spans})
    return "\n".join(out) + "\n", spans, skipped


LAST_SPANS = {}  # the line spans (label, first, last) of the statements and theorems of the last generate()


def generate_statements(text, namespace=None):
    """the statements alone, as a public module of a Lean library (header module / public import Mathlib /
    @[expose] public section): the paper's Lean proves them by hand (theorem lem_x : Stated.lem_x.statement)"""
    q = read_qpp(text)
    ns = namespace or f"Qpp.{q['paper'] or 'Paper'}.Stated"
    lean, made, skipped = generate(text, ns)
    lines = lean.split("\n")
    out = ["module", "", "public import Mathlib", "",
           "/-! Generated by qpp/qpp2lean.py --statements from the Q++ file of the paper; do not edit. -/", "",
           "@[expose] public section", "", "set_option linter.unusedVariables false", "", f"namespace {ns}", ""]
    for _tag, a, b in LAST_SPANS["stated"]:
        out += lines[a - 1:b]
    out += [f"end {ns}", ""]
    return "\n".join(out), [t for t, _, _ in LAST_SPANS["stated"]], skipped


def main(argv):
    if "--kernel" in argv:
        from qpp import kernel
        return kernel.main([a for a in argv if a != "--kernel"])
    src = Path(argv[0])
    ns = argv[argv.index("--namespace") + 1] if "--namespace" in argv else None
    if "--match" in argv:
        from qpp import leanrefs
        root = argv[argv.index("--match") + 1]
        imports = [argv[argv.index("--import") + 1]] if "--import" in argv else []
        text, spans, skipped = generate_match(src.read_text(encoding="utf-8"), leanrefs.label_map(root, kernel=False),
                                              imports, ns, leanrefs.cited_premises(root), leanrefs.kernel_items(root))
        Path(argv[argv.index("-o") + 1]).write_text(text, encoding="utf-8") if "-o" in argv else sys.stdout.write(text)
        print(f"match examples {len(spans)}, not stated {len(skipped)}", file=sys.stderr)
        for full, f in leanrefs.unregistered_facts(root):
            print(f"not a cited fact (no fact: or tab:facts tag): {full} ({f}); a declaration that takes it is not "
                  f"matched", file=sys.stderr)
        return 0
    gen = generate_statements if "--statements" in argv else generate
    text, made, skipped = gen(src.read_text(encoding="utf-8"), ns)
    if "-o" in argv:
        Path(argv[argv.index("-o") + 1]).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    print(f"generated {len(made)}, not generated {len(skipped)}, warnings {len(LAST_WARNINGS)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
