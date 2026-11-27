"""prooftex: the proofs of the article as sentences, transcoded from their Q++ proof words.

A proof line of Q++ is a word: a step `with[CLAUSE by W; W']`, a split `cases[P; W1; W2]`, a chain, an induction, a
witness `take[x := t; W]`, a reference to a result, or a closing word (`V[...]`, `eq`, `logic`, ...). The article
prints each word as the sentence it stands for, in the order of the text, so that every sentence is a step that Lean
checks and nothing in a printed proof is written by hand:

- the clause of each step and each link of a chain is a numbered claim (1), (2), ... in the order of the text, the
  numbers of the names hw1, hw2, ... that the words use; a claim proved by a word of several steps is followed by its
  proof, closed by "This proves (K)";
- a split names its clause (c_K) and its negation (c-bar_K), the K-th split of the line (hcK, hnK);
- the hypotheses of the statement are (H_1), (H_2), ... (h_1, h_2), and a premise introduced from the goal (I_K)
  (hiK);
- a closing word reads as the reason it gives: the facts it combines with their coefficients, a result it applies,
  or the law it uses;
- a step that applies a statement row of the document at values, each hypothesis of the row there being a step closed
  by a linear combination of named facts, reads as one sentence: the row, its values, and the facts its hypotheses
  follow from; those steps are not printed unless a later word names them (call_plan);
- a factor 1 of a product and a divisor 1 are left out, and a step whose two sides then print alike is not printed
  unless a later word names it, when it keeps its factors.

The print of a paper (PAPER, set by qpp2latex.generate for a doc that .github/scripts/paper_cuts.py made) reads
the closing words that only the checker needs in fewer words, and its proof names the Lean declarations once
(qpp2latex.proof_tex):
- a certificate names the facts it combines without their coefficients and their directions, as "a positive
  combination of" them when it has coefficients, products or the signs of names ("by positivity" with only signs);
- a step closed by the facts at hand or by logic reads "directly", and a word `logic[W]` reads as W;
- a witness `take[x := x; W]` that names itself is not printed, and a claim proved by a witness and a closing word
  reads as one sentence, "taking x = t".

The printing that the checks read back (qpp2latex --full) prints the words as they are; this module serves the
article only.
"""
import re

from . import texmath as T

# the closing words of the kernel and of the generator: the reason each one gives
LEAF = {
    "eq": "by expanding",
    "I": "by substitution",
    "neq": "since no mass is less than itself",
    "logic": "by logic",
    "mono": "by monotonicity",
    "sum": "term by term",
    "unfold": "by the definitions",
    "box": "by counting the points of the box",
    "Scale": "by the dyadic scale",
    "Arch": "by the Archimedean step of the dyadic scale",
    "Floor": "by the floor of the dyadic scale",
    "ind": "by induction on the range of the sums",
    "pascal": "by the bound of the binomial sums",
    "choose": "by the bound of the binomial coefficient",
    "simplex": "by the count of the lattice points of a simplex",
    "parity": "by the even and the odd points of a box",
    "dyadic": "by the dyadic interval of a mass",
    "choice": "by a witness at each coordinate",
    "enum": "by the lattice points of the box",
    "powdiff": "by the bounds of a power difference",
    "dual": "by weak duality",
    "cells": "by the weights of the boxes",
    "reindex": "by the sum over the listed points read as the sum over the box",
    "inj": "by an injective relation from the points of one count to those of the other",
    "trichotomy": "splitting the cell at each point by the three cases of one comparison",
    "same": "reading the clauses of the two cells as one",
}
# the alias lines of the document being printed, {NAME: WORD} (qpp2latex.generate): an alias reads as its word
ALIASES = {}
# the statement rows of the document being printed, {LABEL(KEY): TEXT} (qpp2latex.generate): a step that applies one
# of them at values reads with the steps that only state its hypotheses folded into it (call_plan)
ROWS = {}
# the line being printed, whose steps are numbered on the page in the order they are printed
CUR = [None]
# True while a paper is printed (qpp2latex.generate): the closing words of the checker in fewer words (the docstring)
PAPER = [False]
ONE = ("num", "1")
BINDERS = {"sum", "prod", "forall", "exists"}
# words that prove their goal by a word of their data: the phrase that leads the reason of that word
LEAD = {"logic": "by logic and", "sum": "term by term,", "unfold": "by the definitions,", "box": "counting the points "
        "of the box,", "trichotomy": "splitting the cell at each point by the three cases of one comparison, the parts "
        "left out empty", "same": "reading the clauses of the two cells as one"}
REL_FLIP = {"<=": ">", "<": ">=", ">=": "<", ">": "<=", "=": "!="}
HEAD = re.compile(r"\s*([A-Za-z][A-Za-z0-9_']*(?::[A-Za-z0-9_:\-]+)?)")
HYP = re.compile(r"(?:h_[A-Za-z0-9_']+|hw\d+(?:_\w+)?|hi\d+|ih_[A-Za-z0-9_']+)")


class Line:
    """the counters of one proof line: steps (hwK) and splits (hcK, hnK), in the order of the text, and the number on
    the page of each printed step (a step folded into a call, or one whose two sides print alike, has none)"""

    def __init__(self, dry=False):
        self.hw = 0
        self.hc = 0
        self.shown = 0
        self.num = {}
        self.dry = dry

    def number(self):
        """the next step, printed: its number on the page"""
        self.hw += 1
        self.shown += 1
        self.num[self.hw] = self.shown
        return self.shown

    def page(self, k):
        """the number on the page of the step hwK"""
        if self.dry:
            return k
        if k not in self.num:
            raise ValueError(f"a reference to the step hw{k}, which is not printed")
        return self.num[k]


def balanced(s, i, o, c):
    """(inside, end) of the bracket o opened at s[i]"""
    depth = 0
    for j in range(i, len(s)):
        depth += (s[j] == o) - (s[j] == c)
        if depth == 0:
            return s[i + 1:j], j + 1
    raise ValueError(f"an unclosed {o} in {s!r}")


def split_top(s, sep):
    """the parts of s at sep outside brackets, braces and parentheses"""
    out, depth, cur = [], 0, ""
    for ch in s:
        depth += (ch in "([{") - (ch in ")]}")
        if ch == sep and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    return [x.strip() for x in out + [cur]]


def top_by(x):
    """the place of the first ` by ` of x outside brackets, or None"""
    depth = 0
    for k, ch in enumerate(x):
        depth += (ch in "([{") - (ch in ")]}")
        if depth == 0 and x.startswith(" by ", k):
            return k
    return None


def items(w):
    """the words of a list `W1, W2, ...` or `(W1, W2, ...)`; one word is a list of one"""
    w = w.strip()
    if w.startswith("(") and balanced(w, 0, "(", ")")[1] == len(w):
        inner = split_top(w[1:-1], ",")
        return inner if len(inner) > 1 else items(w[1:-1])
    return split_top(w, ",")


def split_word(w):
    """(head, key, data, rest) of a word `head`, `head[data]`, `label(key)[data]` or `h_1(i)[data]`; rest is the
    text after the word"""
    m = HEAD.match(w)
    if not m:
        raise ValueError(f"a word: {w[:40]!r}")
    head, i, key, data = m.group(1), m.end(), None, None
    if i < len(w) and w[i] == "(" and (":" in head or HYP.fullmatch(head)):
        key, i = balanced(w, i, "(", ")")
    if i < len(w) and w[i] == "[":
        data, i = balanced(w, i, "[", "]")
    return head, key, data, w[i:].strip()


def math(tex):
    return f"\\({tex}\\)"


def drop_repeats(x):
    """a parsed clause with each conjunction kept once per conjunct: a step that instantiates a row of two
    conjuncts at equal arguments states the same conjunct twice, and the page prints it once"""
    if isinstance(x, list):
        return [drop_repeats(y) for y in x]
    if not isinstance(x, tuple):
        return x
    if len(x) == 2 and x[0] == "and" and isinstance(x[1], tuple):
        kept = []
        for y in x[1]:
            y = drop_repeats(y)
            if y not in kept:
                kept.append(y)
        return kept[0] if len(kept) == 1 else ("and", tuple(kept))
    return tuple(drop_repeats(y) for y in x)


def drop_ones(x):
    """a parsed term or clause with each factor 1 of a product and each divisor 1 left out: a row applied at the
    value 1 of a weight writes 1 * w, and the page prints w"""
    if isinstance(x, list):
        return [drop_ones(y) for y in x]
    if not isinstance(x, tuple):
        return x
    x = tuple(drop_ones(y) for y in x)
    if len(x) == 4 and x[0] == "bin" and x[1] == "*":
        if x[2] == ONE:
            return x[3]
        if x[3] == ONE:
            return x[2]
    if len(x) == 4 and x[0] == "bin" and x[1] == "/" and x[3] == ONE:
        return x[2]
    return x


def term_tex(x):
    """a parsed term in LaTeX, its factors 1 left out"""
    return T.to_tex(drop_ones(x))


def clause_tex(q):
    """a clause of Q++ in LaTeX"""
    return T.stmt_print(drop_repeats(drop_ones(T.parse_qpp_item(q))), T.to_tex)


def step_tex(q):
    """the clause of a printed step: its factors 1 left out, unless its two sides would then print alike, when the
    step states exactly what they hide"""
    if alike(q):
        return T.stmt_print(drop_repeats(T.parse_qpp_item(q)), T.to_tex)
    return clause_tex(q)


def one_clause(q):
    """the one relation of a clause, parsed, or None"""
    try:
        x = T.parse_qpp_item(q)
    except (ValueError, IndexError, TypeError):
        return None
    if isinstance(x, list):
        if len(x) != 1:
            return None
        x = x[0]
    while isinstance(x, tuple) and x and x[0] == "paren":
        x = x[1]
    return x if isinstance(x, tuple) and x and x[0] == "rel" else None


def alike(q):
    """whether a clause is one equation whose two sides print alike once their factors 1 are left out"""
    x = one_clause(q)
    return (x is not None and tuple(x[1]) == ("=",) and len(x[2]) == 2
            and term_tex(x[2][0]) == term_tex(x[2][1]))


def negation_tex(q):
    """the negation of a clause: a relation of two sides turned, else the clause negated"""
    try:
        x = T.parse_qpp(q)
        while x[0] == "paren":
            x = x[1]
    except (ValueError, IndexError, TypeError):
        x = None
    if x is not None and x[0] == "rel" and len(x[1]) == 1 and x[1][0] in REL_FLIP:
        try:
            return T.to_tex(drop_ones(("rel", [REL_FLIP[x[1][0]]], x[2])))
        except (ValueError, KeyError):
            pass
    return "\\lnot(" + clause_tex(q) + ")"


def fact_label(x):
    """the label on the page of a fact named in data: (K) for hwK (and its part hwK_J), (H_K) for h_K, (c_K) and
    (c-bar_K) for hcK and hnK, (I_K) for hiK, the induction hypothesis for ih_x, the sign of a name for hp(x) and
    the bound of an index for hb(i); None for a term that names no fact"""
    if x[0] == "app" and x[1][0] == "var" and x[3:] == ("call",):
        name, args = x[1][1], ", ".join(T.to_tex(a) for a in x[2])
        if name == "hp":
            return f"the sign of {math(args)}"
        if name == "hb":
            return f"the bound of {math(args)}"
        lab = fact_label(x[1])
        return f"{lab} at {math(args)}" if lab else None
    if x[0] != "var":
        return None
    n = x[1]
    m = re.fullmatch(r"hw(\d+)(?:_(\w+))?", n)
    if m:
        k = CUR[0].page(int(m.group(1))) if CUR[0] is not None else int(m.group(1))
        return f"\\textup{{({k})}}" if m.group(2) is None else f"\\textup{{({k}.{m.group(2)})}}"
    for pat, out in ((r"h_(\d+)", "\\((\\mathrm{{H}}_{{{0}}})\\)"),
                     (r"h_(\d+)_(\w+)", "\\((\\mathrm{{H}}_{{{0}.{1}}})\\)"),
                     (r"h_([A-Za-z][A-Za-z0-9']*)", "\\((\\mathrm{{H}}_{{{0}}})\\)"),
                     (r"hc(\d+)", "\\((\\mathrm{{c}}_{{{0}}})\\)"),
                     (r"hn(\d+)", "\\((\\bar{{\\mathrm{{c}}}}_{{{0}}})\\)"),
                     (r"hi(\d+)", "\\((\\mathrm{{I}}_{{{0}}})\\)"), (r"ih_(\w+)", "the induction hypothesis")):
        m = re.fullmatch(pat, n)
        if m:
            return out.format(*m.groups())
    return None


def factors(x):
    """the factors of a product"""
    return factors(x[2]) + factors(x[3]) if x[0] == "bin" and x[1] == "*" else [x]


def datum_tex(x):
    """one datum of a certificate in words: its coefficient times the fact it names (a product of facts by name)"""
    lab = fact_label(x)
    if lab:
        return lab
    fs = factors(x)
    facts = [f for f in fs if fact_label(f)]
    if not facts:
        return math(term_tex(x))
    coef = [f for f in fs if not fact_label(f)]
    labs = [fact_label(f) for f in facts]
    what = labs[0] if len(labs) == 1 else "the product of " + ", ".join(labs[:-1]) + " and " + labs[-1]
    if not coef:
        return what
    c = coef[0]
    for f in coef[1:]:
        c = ("bin", "*", c, f)
    ct = term_tex(c)
    return what if ct == "1" else f"{math(ct)} times {what}"


def data_terms(d):
    """the terms of the data of a word"""
    T.DATA_MODE[0] = True
    try:
        return T.parse_qpp_list(d)
    finally:
        T.DATA_MODE[0] = False


def data_tex(d):
    """the data of a word that are terms or assignments, printed (an assignment x := t as x = t)"""
    return [term_tex(t).replace(":=", "=") for t in data_terms(d)]


def roman(k):
    """the roman numeral of k >= 1, in lower case"""
    out = ""
    for v, s in ((1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"), (50, "l"), (40, "xl"),
                 (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")):
        while k >= v:
            out, k = out + s, k - v
    return out


def lower(s):
    """a sentence after a colon: its first word in lower case when it is one of the openings of this module"""
    for w in ("The goal", "The parts", "Each part", "Take", "By "):
        if s.startswith(w):
            return s[0].lower() + s[1:]
    return s


def listed(xs):
    return xs[0] if len(xs) == 1 else ", ".join(xs[:-1]) + " and " + xs[-1]


def combination(d):
    """the reason of V or eq with data: the facts it combines with their coefficients, those after `|` read from
    right to left; in a paper, the facts without their coefficients (paper_combination)"""
    if not d.strip():
        return "directly" if PAPER[0] else "from the facts at hand"
    if d.strip() == "0":
        return "by computation"
    parts = split_top(d, "|")
    if PAPER[0]:
        return paper_combination([x for part in parts if part.strip() for x in data_terms(part)])
    written = [datum_tex(x) for x in data_terms(parts[0])] if parts[0] else []
    turned = [datum_tex(x) for x in data_terms(parts[1])] if len(parts) == 2 and parts[1] else []
    if not turned:
        return ("from " if len(written) == 1 else "combining ") + listed(written)
    tail = listed(turned) + " read from right to left"
    return f"combining {listed(written)}, with {tail}" if written else f"from {tail}"


def is_sign(f):
    """True for the fact hp(x), the sign of a name"""
    return f[0] == "app" and f[1] == ("var", "hp") and f[3:] == ("call",)


def paper_combination(terms):
    """the reason of a certificate in a paper: its facts, each once and in order, without coefficients or directions;
    facts that are only added, "from" or "combining" them, one fact "from" it; else "a positive combination of" them;
    the signs of names read as positivity"""
    labs, signs, plain = [], False, True
    for x in terms:
        fs = [x] if fact_label(x) else [f for f in factors(x) if fact_label(f)]
        coef = [f for f in factors(x) if not fact_label(f)] if not fact_label(x) else []
        plain = plain and len(fs) == 1 and all(term_tex(c) == "1" for c in coef)
        for f in fs:
            if is_sign(f):
                signs = True
            elif fact_label(f) not in labs:
                labs.append(fact_label(f))
    labs.sort(key=fact_order)
    if not labs:
        return "by positivity" if signs else "directly"
    if len(labs) == 1 or (plain and not signs):
        return ("from " if len(labs) == 1 else "combining ") + listed(labs) + (" and positivity" if signs else "")
    return ("by positivity and " if signs else "by ") + "a positive combination of " + listed(labs)


def fact_order(lab):
    """the order of the labels of facts in a paper: the steps (K), then the hypotheses (H_K), then the others"""
    m = re.match(r"\\textup\{\((\d+)", lab)
    if m:
        return (0, int(m.group(1)), lab)
    m = re.match(r"\\\(\(\\mathrm\{H\}_\{(\d+)", lab)
    if m:
        return (1, int(m.group(1)), lab)
    return (2, 0, "")


def taken(data):
    """the assignments of a witness take[x := t, ...] as printed; in a paper without those that name themselves"""
    terms = data_terms(data)
    if PAPER[0]:
        terms = [t for t in terms if not (t[0] == "def" and t[1] == t[2])]
    return [term_tex(t).replace(":=", "=") for t in terms]


def reason(w, line):
    """the reason that a closing word gives ("by ..."), or None when the word has steps of its own"""
    ws = items(w)
    w = ws[0] if len(ws) == 1 else w.strip()
    if len(ws) > 1:
        rs = [reason(x, line) for x in ws]
        if not all(rs):
            return None
        if len(set(rs)) == 1:
            return rs[0] + " (each part)"
        return "with its parts " + "; ".join(f"({roman(k + 1)}) {r}" for k, r in enumerate(rs))
    head, key, data, rest = split_word(w)
    if rest:
        if head == "cases" and data is None and re.fullmatch(r"V(\[.*\])?", rest, re.S):
            # cases V[d]: a split on the conditionals of the facts, each case closed by the certificate of its data
            then = combination(rest[2:-1]) if rest != "V" else "by computation"
            return f"by cases on the conditionals of the facts, then {then} in each case"
        raise ValueError(f"two words in a row: {w[:60]!r}")
    if head in ALIASES and key is None and split_word(ALIASES[head])[0] not in ALIASES:
        return reason(ALIASES[head] + (f"[{data}]" if data else ""), line)
    if head in ("with", "cases", "chain", "take", "face") or (head in ("ind", "trichotomy") and data):
        return None
    if head == "V":
        return combination(data or "")
    if head == "eq" and data:
        return combination(data)
    if head in LEAD and data:
        r = reason(data, line)
        if PAPER[0] and head == "logic":
            return r
        return f"{LEAD[head]} {r}" if r else None
    if head in ("pow", "div", "term"):
        parts = split_top(data or "", ";")
        arg = math(", ".join(data_tex(parts[0]))) if parts and parts[0] else ""
        lead = {"pow": f"from the {arg}-th powers", "div": f"dividing by {arg}", "term": f"from the term at {arg}"}[head]
        if len(parts) > 1:
            r = reason(parts[1], line)
            return f"{lead}, {r}" if r else None
        return lead
    if head == "LP":
        return "by the prices " + math(", ".join(data_tex(split_top(data or "", ";")[0]))) + " of the rows"
    if head == "prog":
        parts = split_top(data or "", ";")
        pts = [math(", ".join(data_tex(p))) for p in parts[1:] if p]
        return ("by the prices " + math(", ".join(data_tex(parts[0]))) + " of the rows"
                + (" at the points " + "; ".join(pts) if pts else ""))
    if head in LEAF and not data:
        return "directly" if PAPER[0] and head == "logic" else LEAF[head]
    if ":" in head:
        return ref_reason(head, key, data, line)
    if HYP.fullmatch(head):
        at = [math(key)] if key else []
        at += [math(", ".join(data_tex(data)))] if data else []
        return f"by {fact_label(('var', head))}" + (" at " + ", ".join(at) if at else "")
    raise ValueError(f"a word with no sentence: {head!r}")


def ref_reason(head, key, data, line):
    """the reason of a reference to a result, with its side goals `HYP by W` and the point `at v := t` of a row"""
    out = f"by \\cref{{{head}}}" + (f"({key})" if key else "")
    extra = []
    for s in (split_top(data, ";")[1:] if data is not None else []):
        if re.match(r"at\s", s):
            extra.append("at " + math(", ".join(data_tex(s[3:]))))
            continue
        k = top_by(s)
        if k is None:
            raise ValueError(f"a side goal `HYP by W`: {s!r}")
        r = reason(s[k + 4:], line)
        extra.append(math(clause_tex(s[:k].strip())) + " " + (r if r else "by " + say(s[k + 4:], line).rstrip(".")))
    return out + (" (" + "; ".join(extra) + ")" if extra else "")


FACT = re.compile(r"(?:h_[A-Za-z0-9_']+|hw\d+(?:_\w+)?|hc\d+|hn\d+|hi\d+|ih_[A-Za-z0-9_']+)")


def fact_name(f):
    """the name of the fact that a factor of a datum names (h_1, hw2, hp(x), ...), or None"""
    if f[0] == "app" and f[1][0] == "var" and f[3:] == ("call",):
        n = f[1][1]
        return n if n in ("hp", "hb") or FACT.fullmatch(n) else None
    return f[1] if f[0] == "var" and FACT.fullmatch(f[1]) else None


def subst(x, sub):
    """a parsed clause with its names replaced at once by the terms of sub"""
    if isinstance(x, list):
        return [subst(y, sub) for y in x]
    if not isinstance(x, tuple):
        return x
    if len(x) == 2 and x[0] == "var" and x[1] in sub:
        return sub[x[1]]
    return tuple(subst(y, sub) for y in x)


def binds(x):
    """whether a parsed clause binds a name (a sum, a product, a quantifier)"""
    if not isinstance(x, (list, tuple)):
        return False
    return (isinstance(x, tuple) and bool(x) and x[0] in BINDERS) or any(binds(y) for y in x)


def clause_key(q):
    """a clause as it prints with its factors kept, for matching, or None"""
    x = one_clause(q)
    return T.to_tex(x) if x is not None else None


def law_call(w):
    """(head, key, values, hypotheses) of a word that applies a statement row of the document at values, with the
    hypotheses of the row at those values as they print; None for any other word"""
    ws = items(w)
    if len(ws) != 1:
        return None
    head, key, data, rest = split_word(ws[0])
    if rest or ":" not in head or key is None or not data or len(split_top(data, ";")) != 1:
        return None
    text = ROWS.get(f"{head}({key})")
    if text is None:
        return None
    defs = data_terms(data)
    if not defs or not all(d[0] == "def" and d[1][0] == "var" for d in defs):
        return None
    stmt = T.parse_qpp_item(text)
    if not isinstance(stmt, list) or not stmt or stmt[0][0] != "ctx":
        return None
    ctx = stmt[0][1]
    hyps = ctx[1] if ctx[0] == "and" else (ctx,)
    if any(h[0] not in ("decl", "rel") or binds(h) for h in hyps):
        return None
    sub = {d[1][1]: d[2] for d in defs}
    return head, key, defs, [T.to_tex(subst(h, sub)) for h in hyps if h[0] == "rel"]


def v_sources(w):
    """the facts that a closing word V[...] combines linearly, each a datum's one named factor; None for any other
    word, for a datum that multiplies two facts, and for a bare V (which may read any fact at hand)"""
    ws = items(w)
    if len(ws) != 1:
        return None
    head, key, data, rest = split_word(ws[0])
    if head != "V" or key is not None or rest or data is None:
        return None
    out = []
    for part in split_top(data, "|"):
        if not part.strip() or part.strip() == "0":
            continue
        for x in data_terms(part):
            named = [f for f in factors(x) if fact_name(f)]
            if len(named) != 1:
                return None
            if named[0] not in out:
                out.append(named[0])
    return out


def quiet(f, w):
    """f(w), or None for a word that f cannot read"""
    try:
        return f(w)
    except ValueError:
        return None


def count_hw(w):
    """the number of steps (hwK) that the sentences of a word name"""
    saved, CUR[0] = CUR[0], Line(dry=True)
    try:
        say(w, CUR[0])
        return CUR[0].hw
    finally:
        CUR[0] = saved


def call_plan(w, line):
    """the plan of the chain of steps `with[C by W; ...]` that starts at w, one entry per step: "show" (printed as
    itself), "hide" (not printed) or a call (a step that applies a statement row of the document at values, printed
    with the steps that state its hypotheses folded into it).

    A call is folded when each hypothesis of the row at its values is a step of the chain closed by a linear
    combination of named facts (or a bare V on an equation whose sides print alike); such a step is then not printed,
    and the call names its facts instead, unless a later word names the step, which then stays and is named. A step
    whose two sides print alike once the factors 1 are left out is not printed either, unless a later word names
    it."""
    steps, tail = [], w
    while True:
        ws = items(tail)
        if len(ws) != 1:
            break
        try:
            head, key, data, rest = split_word(ws[0])
        except ValueError:
            break
        if head != "with" or rest or data is None:
            break
        parts = split_top(data, ";")
        k = top_by(parts[0]) if len(parts) == 2 else None
        if k is None:
            break
        steps.append((parts[0][:k].strip(), parts[0][k + 4:].strip()))
        tail = parts[1]
    names, k = [], line.hw
    for _, closer in steps:
        k += 1
        names.append(k)
        k += count_hw(closer)
    index = {n: i for i, n in enumerate(names)}
    keys = [clause_key(c) for c, _ in steps]
    calls = {i: quiet(law_call, c) for i, (_, c) in enumerate(steps)}
    calls = {i: c for i, c in calls.items() if c}
    srcs = {}
    for i, (c, closer) in enumerate(steps):
        if i in calls or count_hw(closer):
            continue
        v = quiet(v_sources, closer)
        if v is None and closer == "V" and alike(c):
            v = []
        if v is not None:
            srcs[i] = v
    folds = {}
    for L, (_, _, _, hyps) in calls.items():
        match = [next((i for i in range(L) if keys[i] == h), None) for h in hyps]
        if None not in match and all(i in srcs for i in match):
            folds[L] = match
    hide = {i for m in folds.values() for i in m if i in srcs}
    hide |= {i for i, (c, closer) in enumerate(steps) if i not in calls and alike(c) and not count_hw(closer)}
    changed = True
    while changed:
        changed = False
        for i in sorted(hide):
            named = re.compile(rf"\bhw{names[i]}(?![0-9])")
            if any(named.search(t) for t in [steps[j][1] for j in range(i + 1, len(steps)) if j not in hide] + [tail]):
                hide.discard(i)
                changed = True

    def facts(i):
        if i not in hide:
            return [("var", f"hw{names[i]}")]
        out = []
        for f in srcs.get(i, []):
            m = re.fullmatch(r"hw(\d+)(?:_\w+)?", fact_name(f))
            out += facts(index[int(m.group(1))]) if m and index.get(int(m.group(1))) in hide else [f]
        return out

    plan, done = ["hide" if i in hide else "show" for i in range(len(steps))], []
    for L, match in sorted(folds.items()):
        if not any(i in hide for i in match):
            continue
        head, key, defs, _ = calls[L]
        same = (head, key, defs) in done
        got = []
        for i in match:
            for f in facts(i):
                if f not in got:
                    got.append(f)
        plan[L] = ("call", head, key, defs, got, same)
        done.append((head, key, defs))
    return plan


def values_tex(defs):
    """the values of a call, x |-> t, the names kept by the call left out"""
    out = []
    for d in defs:
        name, val = T.to_tex(d[1]), term_tex(d[2])
        if name != val:
            out.append(f"{name}\\mapsto {val}")
    return ", ".join(out)


def call_sentence(act):
    """the reason of a call: the row, its values, and the facts its hypotheses follow from"""
    _, head, key, defs, got, same = act
    out = f"by \\cref{{{head}}}({key})"
    if same:
        return out + " at the same values"
    at = values_tex(defs)
    out += f" at {math(at)}" if at else ""
    def order(f):
        n = fact_name(f)
        m = re.fullmatch(r"(hw|h_)(\d+)", n)
        return (0 if n.startswith("hw") else 1 if m else 2, int(m.group(2)) if m else 0, n)
    got = sorted(got, key=order)
    labs, j = [], 0
    while j < len(got):
        m = re.fullmatch(r"h_(\d+)", fact_name(got[j]))
        r = j
        while m and r + 1 < len(got) and fact_name(got[r + 1]) == f"h_{int(m.group(1)) + r + 1 - j}":
            r += 1
        labs.append(f"{fact_label(got[j])} to {fact_label(got[r])}" if r - j >= 2 else fact_label(got[j]))
        j = r + 1 if r - j >= 2 else j + 1
    if not labs:
        return out + ", whose hypotheses there are identities"
    return out + f", whose hypotheses there follow linearly from {listed(labs)}"


def claim(n, tex, w, line):
    """a numbered claim and the word that proves it; in a paper, a claim proved by a witness and a closing word in one
    sentence"""
    head = f"\\textup{{({n})}}~{math(tex)}"
    r = reason(w, line)
    if r is not None:
        return f"{head} {r}."
    t = taking(w, line)
    if t is not None:
        return f"{head}{t}."
    return f"{head}. {say(w, line)} This proves \\textup{{({n})}}."


def taking(w, line):
    """in a paper, the end of the sentence of a witness take[x := t; W] whose W is a closing word: ", taking x = t"
    and the reason of W unless it is "directly"; None for any other word"""
    if not PAPER[0]:
        return None
    ws = items(w)
    head, _key, data, rest = split_word(ws[0]) if len(ws) == 1 else (None, None, None, None)
    if head != "take" or rest or data is None:
        return None
    parts = split_top(data, ";")
    if len(parts) != 2 or len(items(parts[1])) > 1:
        return None
    r = reason(parts[1], line)
    if r is None:
        return None
    binds = taken(parts[0])
    out = f", taking {math(', '.join(binds))}" if binds else ""
    return out + ("" if r == "directly" and binds else f"{',' if binds else ''} {r}")


def say(w, line, plan=None):
    """the sentences of a word that proves the goal in front of it; plan, the plan of the chain of steps that the
    word continues (call_plan)"""
    w = w.strip()
    clauses = split_top(w, ";")
    if len(clauses) > 1:
        return " ".join(f"Clause {k + 1}: {lower(say(c, line))}" for k, c in enumerate(clauses))
    ws = items(w)
    if len(ws) > 1:
        rs = [reason(x, line) for x in ws]
        if all(rs) and len(set(rs)) == 1:
            return f"Each part of the goal follows {rs[0]}."
        if all(rs):
            return "The parts of the goal follow: " + "; ".join(f"({roman(k + 1)}) {r}" for k, r in enumerate(rs)) + "."
        return " ".join(f"Part ({roman(k + 1)}): {lower(say(x, line))}" for k, x in enumerate(ws))
    r = reason(w, line)
    if r is not None:
        return f"The goal follows {r}."
    head, key, data, rest = split_word(ws[0])
    if head in LEAD and data:
        if PAPER[0] and head == "logic":
            return say(data, line)
        if PAPER[0] and split_top(data, ";") == [data] and len(items(data)) == 1 and \
                HEAD.match(data.strip()) and split_word(data.strip())[0] == head:
            return say(data, line)  # the same lead nested in itself (sum[sum[...]]) is said once, by the inner word
        return {"logic": "By logic:", "sum": "Term by term:", "unfold": "By the definitions:",
                "box": "Counting the points of the box:",
                "trichotomy": "Splitting the cell at each point by the three cases of one comparison, each part left "
                "out is empty:", "same": "Reading the clauses of the two cells as one:"}[head] + " " + lower(
                    say(data, line))
    if head in ("pow", "div", "term") and data:
        parts = split_top(data, ";")
        arg = math(", ".join(data_tex(parts[0])))
        lead = {"pow": f"From the {arg}-th powers:", "div": f"Dividing by {arg}:", "term": f"From the term at {arg}:"}
        return lead[head] + " " + lower(say(parts[1], line))
    if head == "with":
        parts = split_top(data, ";")
        k = top_by(parts[0]) if len(parts) == 2 else None
        if k is None:
            raise ValueError(f"with[CLAUSE by W; W']: {data[:60]!r}")
        if not plan:
            plan = call_plan(ws[0], line)
        act, plan = plan[0], plan[1:]
        clause, closer = parts[0][:k].strip(), parts[0][k + 4:]
        if act == "hide":
            line.hw += 1
            return say(parts[1], line, plan)
        n = line.number()
        if act != "show":
            return f"\\textup{{({n})}}~{math(clause_tex(clause))} {call_sentence(act)}. " + say(parts[1], line, plan)
        return claim(n, step_tex(clause), closer, line) + " " + say(parts[1], line, plan)
    if head == "chain":
        parts = split_top(data, ";")
        last = parts.pop() if parts and top_by(parts[-1]) is None else None
        out, prev = [], None
        for j, p in enumerate(parts):
            k = top_by(p)
            if j == 0:
                q = p[:k].strip()
            else:
                m = re.match(r"(<=|>=|<|>|=)\s*", p)
                lhs = T.to_qpp(prev)
                q = f"({lhs}) {m.group(1)} {p[m.end():k].strip()}" if prev[0] in ("sum", "prod") else \
                    f"{lhs} {m.group(1)} {p[m.end():k].strip()}"
            x = T.parse_qpp(q)
            while x[0] == "paren":
                x = x[1]
            prev = x[2][-1]
            out.append(claim(line.number(), clause_tex(q), p[k + 4:], line))
        tail = say(last, line) if last is not None else "The goal follows by composing the links."
        return " ".join(out) + " " + tail
    if head == "cases":
        parts = split_top(data, ";")
        if len(parts) != 3:
            raise ValueError(f"cases[P; W1; W2]: {data[:60]!r}")
        line.hc += 1
        n = line.hc
        return (f"Case \\((\\mathrm{{c}}_{{{n}}})\\) {math(clause_tex(parts[0]))}: {lower(say(parts[1], line))} "
                f"Case \\((\\bar{{\\mathrm{{c}}}}_{{{n}}})\\) {math(negation_tex(parts[0]))}: "
                f"{lower(say(parts[2], line))}")
    if head == "take":
        parts = split_top(data, ";")
        t = taking(w, line)
        if t is not None:
            return f"The goal follows{t}."
        binds = taken(parts[0])
        rest = say(parts[1], line) if len(parts) > 1 else ""
        return f"Take {math(', '.join(binds))}. " + rest if binds else rest
    if head == "ind":
        parts = split_top(data, ";")
        if len(parts) != 3:
            raise ValueError(f"ind[n; W; W']: {data[:60]!r}")
        return (f"By induction on {math(T.to_tex(T.parse_qpp(parts[0])))}. Base: {lower(say(parts[1], line))} "
                f"Step: {lower(say(parts[2], line))}")
    if head == "face":
        parts = split_top(data, ";")
        out = [f"By the face of the program. The value: {lower(say(parts[0], line))}"]
        for p in parts[1:]:
            k = top_by(p)
            if k is None:
                out.append(f"The gap: {lower(say(p, line))}")
                continue
            lhs, ws = p[:k].strip(), p[k + 4:].strip()
            what = (f"At the point {math(', '.join(data_tex(lhs)))}" if ":=" in lhs
                    else f"The ties {math(clause_tex(lhs.replace(', ', '; ')))}")
            r = reason(ws, line)
            out.append(f"{what}: the rows hold {r}." if r else f"{what}: {lower(say(ws, line))}")
        return " ".join(out)
    raise ValueError(f"a word with no sentence: {head!r}")


def line_prose(text):
    """the sentences of one proof line"""
    saved, CUR[0] = CUR[0], Line()
    try:
        return say(text, CUR[0])
    finally:
        CUR[0] = saved


def tex_group(s, i):
    """(inside, end) of the LaTeX group opened by the brace at s[i]; an escaped brace \\{ or \\} is no brace"""
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        depth += (c == "{") - (c == "}")
        if depth == 0:
            return s[i + 1:j], j + 1
        j += 1
    raise ValueError(f"an unclosed brace in {s!r}")


def text_of(hole):
    """a row written as LaTeX in math mode with its words in \\text{...} (an origin row), in text mode: the words as
    text, the mathematics between them in \\( \\), so that the row breaks across lines as prose does"""
    out, i, buf = [], 0, ""

    def flush(m):
        lead = re.match(r"(?:\s|\\ )+", m)
        trail = re.search(r"(?:\s|\\ )+$", m)
        core = m[lead.end() if lead else 0:trail.start() if trail else len(m)]
        if not core:
            return " " if m else ""
        return (" " if lead else "") + math(core) + (" " if trail else "")

    while i < len(hole):
        if hole.startswith("\\text{", i):
            out.append(flush(buf))
            buf = ""
            inner, i = tex_group(hole, i + 5)
            out.append(inner)
        else:
            buf += hole[i]
            i += 1
    out.append(flush(buf))
    return re.sub(r"  +", " ", "".join(out)).strip()
