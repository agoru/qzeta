"""Parser and checker of proof words written in LaTeX.

A proof line is \\eit{item}{expr}. The parser reads expr at top level, outside the data brackets [...]:

  verbs       eq (a law of the symbols), the comparators neq, ind (\\gEq, \\gNeq, \\gInd; the symbols 1, +,
              \\div are in the formulas),
              the derived words I, V, and the synonyms alpha (= eq), iota (= ind) and beta (= Scale, Arch, Floor),
              with a place subscript (V_p, beta_p), an induction variable (ind_k, iota_chain) and the dual mark ^\\vee
  aliases     the patterns P1-P9 and K, the combinators Tot and Euclid, and the named expressions a source defines
              (\\gX, \\Bx{X}, \\Cx{X}), with their parameters in brackets
  references  cited results (\\cref, \\eqref, \\ref), items (k) of the result at hand,
              named conditions such as (U1) or (N_p)
  combinators \\circ (then, right to left), ; and , (independent items), [p:=v] (data), ( ) (grouping),
              ':' (the gloss: what the line concludes, free text)

Everything else at top level, before the gloss, is a formula. A line is
  G  syntax:   a word of verbs, aliases and references, then at most a gloss
  R  reference: references only (no verb, no alias)
  M  mixed:     a word with formulas between its factors
  F  formula:   no verb, alias or reference at all

The checker reports, for each source (a LaTeX file under a name): the classes of its lines; the aliases it uses
against those it defines (with an expansion), declares by reference, or neither (the rule: every source defines the
aliases it uses); the expansion of every alias to atoms (nested aliases are expanded recursively, and a cycle is an
error); and the typing rules of rules().

Usage: python3 -m qpp.syntax [--json OUT] [--mine] NAME=PATH ...
       --mine prints the Re-Pair rules of the normal forms (the patterns that survive normalization)
A table with the header 'name & fact & reference' declares its first column as cited facts, and a row
'templates' declares templates in words: both are opaque leaves of the expansion (cite:NAME, tpl:NAME).
Exit status 1 if a rule reports a finding (T5 and T6 are reports for review, counted too).
"""
import collections
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------------------------------------
# Lexer

# eq (a law of the symbols), the comparators neq, ind; the derived words I, V; the synonyms alpha (= eq), iota (= ind),
# beta (= Scale, Arch, Floor), which rule T8 reports
VERBS = {"eq", "neq", "ind", "I", "V", "Scale", "Arch", "Floor", "alpha", "beta", "iota"}
# the derived words of the dyadic scale: words of the core like I and V, never an alias of a source
SCALE_WORDS = {"Scale", "Arch", "Floor"}
# the words of the generator (qpp/kernel.py), printed \mathrm{cases}, \mathrm{sum}[W], \mathrm{pow}[j; W],
# \mathrm{div}[c; W], \mathrm{LP}[p_1, ..., p_J; extra], \mathrm{prog}[w_1, ..., w_J; v := t, ...; ...],
# \mathrm{take}[x := t, ...; W], \mathrm{logic}[W], \mathrm{with}[CLAUSE \text{by} W; W'], \mathrm{term}[J; W]
# \mathrm{face}[W; x := t, ... \text{by} W, ...; ...; TIES \text{by} W; W']
KERNEL_WORDS = {"cases", "sum", "pow", "div", "LP", "prog", "take", "logic", "with", "chain", "unfold", "term",
                "face"}
COMPARATOR_MACROS = {"gEq": "eq", "gNeq": "neq", "gInd": "ind"}
INDUCTION = ("ind", "iota")
SYNONYMS = {"alpha": "use eq", "iota": "use ind", "beta": "use Scale, Arch or Floor"}
MACRO_ALIAS = {"gEu": "Euclid", "gSwap": "Swap", "gPig": "Pig", "gPF": "PF", "gHen": "Hensel", "gTot": "Tot",
               "gWind": "Wind", "gHalf": "Half", "gDouble": "Double", "gBez": "Bez", "gCRT": "CRT",
               "gMult": "Mult", "gEuler": "Euler"}
MATHRM_ALIAS = {"Tot", "Euclid", "Pig", "Swap", "Carry", "Fib", "Tower", "Pivot", "Exist", "Root", "Scale", "Arch",
                "Floor"}
REF_MACROS = {"cref": "", "Cref": "", "eqref": "", "ref": ""}
NOISE = re.compile(r"\\(textstyle|displaystyle|big|Big|bigg|Bigg|left|right|quad|qquad)(?![A-Za-z])|\\[,;!> ]|~")
COND = re.compile(r"^\(\s*(?:\\text\{)?\s*\(?([A-Z][A-Za-z]{0,3}\d{0,2}(?:_\{?[^)]{0,12}\}?)?)\s*\)?\s*\}?\s*\)$")
SELF = re.compile(r"^\((?:\d+|[a-z]|[ivx]+|\d+[a-z]?(?:\s*,\s*\d+[a-z]?)*|[a-z]+(?:\s*,\s*[a-z]+)*|\\[a-z]+)\)$")


class Tok:
    __slots__ = ("kind", "name", "sub", "dual", "part", "text", "labels")

    def __init__(self, kind, name="", sub="", dual=False, part="", text="", labels=()):
        self.kind, self.name, self.sub, self.dual, self.part = kind, name, sub, dual, part
        self.text, self.labels = text, tuple(labels)

    def __repr__(self):
        s = self.name or self.text[:20]
        return f"{self.kind}:{s}{'_' + self.sub if self.sub else ''}{'^v' if self.dual else ''}"


def balanced(s, i, o, c):
    """s[i] == o; return (inner, index after the matching c), counting the three bracket kinds."""
    depth = 0
    j = i
    while j < len(s):
        ch = s[j]
        if ch == "\\":
            j += 2
            continue
        if ch == o:
            depth += 1
        elif ch == c:
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    return s[i + 1:], len(s)


def unwrap_text(s):
    """\\text{\\cref{x}} -> \\cref{x}; \\text{(U1)} -> (U1); \\textup{...} likewise, when the text is a reference."""
    out = []
    i = 0
    while i < len(s):
        m = re.compile(r"\\(text|textup|mbox)\{").match(s, i)
        if m:
            inner, j = balanced(s, m.end() - 1, "{", "}")
            if re.match(r"\s*(\\(cref|Cref|eqref|ref|cite)\b|\(\s*[A-Z][A-Za-z]{0,3}\d{0,2}\s*\))", inner):
                out.append(inner)
            else:
                out.append(s[i:j])
            i = j
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


def read_sub(s, i):
    """A subscript _x or _{...} at s[i:], and a dual mark ^\\vee or ^{\\vee}; returns (sub, dual, i)."""
    sub, dual = "", False
    for _ in range(2):
        if s.startswith("^\\vee", i):
            dual, i = True, i + 5
        elif s.startswith("^{\\vee}", i):
            dual, i = True, i + 7
        elif i < len(s) and s[i] == "_":
            i += 1
            if i < len(s) and s[i] == "{":
                sub, i = balanced(s, i, "{", "}")
            elif s.startswith("\\", i):
                m = re.compile(r"\\[A-Za-z]+").match(s, i)
                if m:
                    sub, i = m.group(0), m.end()
                else:
                    sub, i = s[i:i + 2], i + 2
            elif i < len(s):
                sub, i = s[i], i + 1
    sub = re.sub(r"\\rm\s*|\\mathrm\{([^}]*)\}", lambda m: m.group(1) or "", sub).strip()
    return sub, dual, i


def lex(expr):
    s = NOISE.sub(" ", unwrap_text(expr))
    toks = []
    i = 0
    n = len(s)

    def prev_sig():
        return toks[-1].kind if toks else None

    while i < n:
        ch = s[i]
        if ch.isspace():
            i += 1
            continue
        if ch == "[":
            inner, i = balanced(s, i, "[", "]")
            toks.append(Tok("DATA", text=inner))
            continue
        if ch == "(":
            inner, j = balanced(s, i, "(", ")")
            whole = s[i:j]
            if prev_sig() == "REF" and re.match(r"^\([^()]{0,20}\)$", whole) and not toks[-1].part:
                toks[-1].part = inner.strip()
                i = j
                if s.startswith("^\\vee", i):
                    toks[-1].dual, i = True, i + 5
                continue
            if COND.match(whole):
                toks.append(Tok("COND", name=COND.match(whole).group(1)))
            elif SELF.match(whole):
                toks.append(Tok("SELF", name=inner.strip()))
            else:
                toks.append(Tok("PAREN", text=inner))
            i = j
            if s.startswith("^\\vee", i) and toks[-1].kind in ("PAREN", "SELF"):
                toks[-1].dual, i = True, i + 5
            continue
        if ch == "{":
            inner, i = balanced(s, i, "{", "}")
            toks.append(Tok("MATH", text="{" + inner + "}"))
            continue
        if ch == ";":
            toks.append(Tok("SEMI"))
            i += 1
            continue
        if ch == ",":
            toks.append(Tok("COMMA"))
            i += 1
            continue
        if ch == ":" and not s.startswith(":=", i):
            toks.append(Tok("GLOSS", text=s[i + 1:].strip()))
            break
        if ch == "\\":
            m = re.compile(r"\\([A-Za-z]+)").match(s, i)
            if not m:
                toks.append(Tok("MATH", text=s[i:i + 2]))
                i += 2
                continue
            name, i = m.group(1), m.end()
            if name == "circ":
                toks.append(Tok("O"))
                continue
            if name in ("alpha", "beta", "iota"):
                sub, dual, j = read_sub(s, i)
                rest = s[j:].lstrip()
                # a definition (\beta_*:=...) or a member of a list of terms (\kappa_c,\ \beta,\ c_N) is a constant
                # of the source named beta, not the synonym
                atom_next = (rest == "" or rest[0] in "[;,:)(" or rest.startswith("\\circ")
                             or rest.startswith("\\big") or rest.startswith("\\Big")) and not rest.startswith(":=")
                atom_prev = prev_sig() in (None, "O", "SEMI") or (
                    prev_sig() == "COMMA" and not (len(toks) > 1 and toks[-2].kind == "MATH"))
                if name == "beta" and rest.startswith("("):
                    # \beta(\kappa,n): the function beta of the constants, unless the group holds words
                    arg, _ = balanced(rest, 0, "(", ")")
                    if not re.search(r"\\circ|\\g[A-Z]|\\(?:alpha|beta|iota)(?![A-Za-z])|\\mathrm\{", arg):
                        atom_next = False
                if name == "iota" or (atom_next and atom_prev):
                    toks.append(Tok("VERB", name=name, sub=sub, dual=dual))
                else:
                    toks.append(Tok("MATH", text="\\" + name))
                i = j
                continue
            if name in ("gI", "gV"):
                sub, dual, i = read_sub(s, i)
                toks.append(Tok("VERB", name=name[1], sub=sub, dual=dual))
                continue
            if name in COMPARATOR_MACROS:
                sub, dual, i = read_sub(s, i)
                toks.append(Tok("VERB", name=COMPARATOR_MACROS[name], sub=sub, dual=dual))
                continue
            if name == "Pt":
                m2 = re.compile(r"\s*\{?(\d)\}?").match(s, i)
                if m2:
                    i = m2.end()
                    sup = ""
                    m3 = re.compile(r"\^\{\\rm\s*(in|out)\}").match(s, i)
                    if m3:
                        sup, i = m3.group(1), m3.end()
                    part = ""
                    m4 = re.compile(r"\((\d)\)").match(s, i)
                    if m4:
                        part, i = m4.group(1), m4.end()
                    sub, dual, i = read_sub(s, i)
                    toks.append(Tok("ALIAS", name="P" + m2.group(1), sub=sup or sub, dual=dual, part=part))
                    continue
            if name == "Kt":
                part = ""
                m4 = re.compile(r"\((\d)\)").match(s, i)
                if m4:
                    part, i = m4.group(1), m4.end()
                sub, dual, i = read_sub(s, i)
                toks.append(Tok("ALIAS", name="K", dual=dual, part=part))
                continue
            if name in MACRO_ALIAS:
                sub, dual, i = read_sub(s, i)
                toks.append(Tok("ALIAS", name=MACRO_ALIAS[name], sub=sub, dual=dual))
                continue
            if name in ("Bx", "Cx", "mathrm", "operatorname"):
                if i < n and s[i] == "{":
                    inner, j = balanced(s, i, "{", "}")
                    if re.fullmatch(r"P\d|K", inner) and name == "mathrm":
                        # \mathrm{P3}, \mathrm{K}: the spelled-out macros \Pt3, \Kt (a pattern and the constants)
                        part = ""
                        m4 = re.compile(r"\((\d)\)").match(s, j)
                        if m4:
                            part, j = m4.group(1), m4.end()
                        sub, dual, j = read_sub(s, j)
                        toks.append(Tok("ALIAS", name=inner, sub=sub if inner != "K" else "", dual=dual, part=part))
                        i = j
                        continue
                    if inner in SCALE_WORDS or inner in KERNEL_WORDS:
                        sub, dual, j = read_sub(s, j)
                        toks.append(Tok("VERB", name=inner, sub=sub, dual=dual))
                        i = j
                        continue
                    if name in ("Bx", "Cx") or inner in MATHRM_ALIAS:
                        sub, dual, j = read_sub(s, j)
                        toks.append(Tok("ALIAS", name=inner, sub=sub, dual=dual))
                        i = j
                        continue
                    toks.append(Tok("MATH", text="\\mathrm{" + inner + "}"))
                    i = j
                    continue
            if name in REF_MACROS or name == "cite":
                part = ""
                if i < n and s[i] == "[":
                    part, i = balanced(s, i, "[", "]")
                    part = part.strip("()")
                if i < n and s[i] == "{":
                    inner, i = balanced(s, i, "{", "}")
                else:
                    inner = ""
                ns = REF_MACROS.get(name, "cite:")
                labs = [ns + x.strip() for x in inner.split(",") if x.strip()]
                sub, dual, i = read_sub(s, i)
                toks.append(Tok("REF", name=name, labels=labs, part=part, dual=dual))
                continue
            toks.append(Tok("MATH", text="\\" + name))
            continue
        # plain characters: a run of math
        j = i
        while j < n and not s[j].isspace() and s[j] not in "[]{}();,:\\":
            j += 1
        if j == i:
            j = i + 1
        toks.append(Tok("MATH", text=s[i:j]))
        i = j
    return toks


# ---------------------------------------------------------------------------------------------------------
# Parser: items (separated by ; and ,) of chains (separated by \circ) of factors

class Factor:
    __slots__ = ("head", "data", "body")

    def __init__(self, head, data=None, body=None):
        self.head, self.data, self.body = head, data or [], body

    def __repr__(self):
        b = f"({self.body})" if self.body else ""
        return f"{self.head!r}{b}"


def parse(expr):
    """Return (items, gloss, nmath): items is a list of chains, a chain a list of Factor or 'MATH'.

    A line 'case: word' (a case, a hypothesis or a claim before the colon, the expression after it) is read as
    the word, with the case as its gloss; parse_line() records which way the colon was used."""
    return parse_line(expr)[:3]


def parse_line(expr):
    toks = lex(expr)
    gloss = ""
    if toks and toks[-1].kind == "GLOSS":
        gloss = toks.pop().text
    items, nmath = _parse_toks(toks)
    keyed = False
    if gloss and not has_word(items):
        g_items, g_gloss, g_math, g_keyed = parse_line(gloss)
        if has_word(g_items):
            keyed = True
            return g_items, expr.split(":")[0], g_math, keyed
    return items, gloss, nmath, keyed


def _parse_toks(toks):
    items, chain = [], []
    nmath = 0
    k = 0
    while k < len(toks):
        t = toks[k]
        if t.kind in ("SEMI", "COMMA"):
            if chain:
                items.append(chain)
            chain = []
        elif t.kind == "O":
            pass
        elif t.kind in ("VERB", "ALIAS", "REF", "SELF", "COND"):
            f = Factor(t)
            while k + 1 < len(toks) and toks[k + 1].kind in ("DATA", "PAREN"):
                nxt = toks[k + 1]
                if nxt.kind == "DATA":
                    f.data.append(nxt.text)
                else:
                    sub_items, _, sub_math = parse(nxt.text)
                    if has_word(sub_items):
                        f.body = sub_items
                        nmath += sub_math
                    else:
                        break
                k += 1
            chain.append(f)
        elif t.kind == "PAREN":
            sub_items, _, sub_math = parse(t.text)
            if has_word(sub_items):
                chain.append(Factor(Tok("GROUP", dual=t.dual), body=sub_items))
                nmath += sub_math
            else:
                chain.append("MATH")
                nmath += 1
        elif t.kind == "DATA":
            chain.append("MATH")
            nmath += 1
        else:
            chain.append("MATH")
            nmath += 1
        k += 1
    if chain:
        items.append(chain)
    return items, nmath


def has_word(items):
    return any(isinstance(f, Factor) for ch in items for f in ch)


def factors(items):
    for ch in items:
        for f in ch:
            if isinstance(f, Factor):
                yield f
                if f.body:
                    yield from factors(f.body)


def classify(items, nmath, keyed=False):
    """G syntax, K case then syntax ('case: word'), R references only, M word with formulas, F formulas."""
    fs = list(factors(items))
    heads = [f for f in fs if f.head.kind in ("VERB", "ALIAS", "GROUP")]
    if not fs:
        return "F"
    if nmath:
        return "M"
    if keyed:
        return "K"
    return "G" if heads else "R"


# ---------------------------------------------------------------------------------------------------------
# Corpus: proof lines and alias definitions

def paper_dir(paper, root=ROOT):
    """the folder of a paper: PAPER/ at the root"""
    return Path(root) / paper


def paper_tex(paper, root=ROOT):
    """the LaTeX of a paper that the checks read (latex2qpp, the status page): the full printing
    PAPER/qpp/PAPER.full.tex of a paper with a Q++ 0.2 source, which keeps the `core` rows and the fixtures that the
    article leaves out (qpp2latex --full), else the paper's LaTeX PAPER/latex/PAPER.tex (PAPER the folder of
    paper_dir)"""
    full = paper_dir(paper, root) / "qpp" / f"{paper}.full.tex"
    return full if full.exists() else paper_dir(paper, root) / "latex" / f"{paper}.tex"


def strip_comments(src):
    return re.sub(r"(?<!\\)%[^\n]*", "", src)


def proof_spans(src):
    spans = []
    for m in re.finditer(r"\\begin\{proof\}(\[[^\n]*?\])?(.*?)\\end\{proof\}", src, re.S):
        head = m.group(1) or ""
        lab = re.findall(r"\\cref\{([^}]*)\}", head)
        if lab:
            label = lab[0].split(",")[0]
        else:
            # the result before the proof, by its first label (\label{lem:slab}\label{lem:persist} is lem:slab)
            envs = list(RESULT_BEGIN.finditer(src, 0, m.start()))
            lab = re.search(r"\\label\{([^}]*)\}", src[envs[-1].end():m.start()]) if envs else None
            if lab is None:
                ls = re.findall(r"\\label\{([^}]*)\}", src[:m.start()])
                label = ls[-1] if ls else "?"
            else:
                label = lab.group(1)
        spans.append((m.start(), m.end(), label))
    return spans


RESULT_BEGIN = re.compile(r"\\begin\{(?:theorem|lemma[A-Za-z]*|proposition|corollary|definition[A-Za-z]*|construction"
                          r"|example[A-Za-z]*|remark|problem)\}")


def lines_of(src, paper):
    src = strip_comments(src)
    spans = proof_spans(src)
    out = []
    for e in re.finditer(r"\\eit\{", src):
        item, j = balanced(src, e.end() - 1, "{", "}")
        while j < len(src) and src[j] in " \n":
            j += 1
        if j >= len(src) or src[j] != "{":
            continue
        expr, _ = balanced(src, j, "{", "}")
        pos = e.start()
        lab = next((l for a, b, l in spans if a <= pos < b), None)
        if lab is None:
            continue  # expression lines outside proofs (syntax sections, tables) are not proof lines
        out.append({"paper": paper, "label": lab, "item": item, "expr": expr,
                    "line": src.count("\n", 0, pos) + 1})
    return out


DEF_RE = re.compile(r"\\\(\s*((?:\\g[A-Za-z]+|\\[BC]x\{[A-Za-z]+\}|\\mathrm\{[A-Za-z][A-Za-z0-9]*\}|\\beta|\\gV)(?:_\{?[^\s\[\\:{}]*\}?|_\\[A-Za-z]+)?)"
                    r"(\[[^\]]*\])?\s*:=")


def alias_defs(src, paper):
    """Definitions NAME[slots]:=RHS in the paper (outside proofs) and the rows of its alias tables."""
    src = strip_comments(src)
    spans = proof_spans(src)
    defs = {}
    for m in DEF_RE.finditer(src):
        if any(a <= m.start() < b for a, b, _ in spans):
            continue
        # the RHS runs to the closing \) of this inline math
        k = src.find("\\)", m.end())
        rhs = src[m.end():k]
        rhs = re.split(r",\s*\\(?:text|emph)", rhs)[0]
        name = head_name(m.group(1))
        if m.group(1).startswith("\\beta") and not any(t.kind in ("VERB", "ALIAS") for t in lex(rhs)):
            continue  # \beta_T:=n_y+2+...: a constant of the source named beta, not the synonym
        if name and name not in defs:
            defs[name] = {"rhs": rhs, "slots": (m.group(2) or "")[1:-1], "line": src.count("\n", 0, m.start()) + 1}
    for m in re.finditer(r"^\\\(\s*\\([BC])x\{([A-Za-z]+)\}(\[[^\]]*\])?\s*\\\)\s*&\s*\\\((.*?)\\\)", src, re.M):
        name = m.group(2)
        if name not in defs:
            defs[name] = {"rhs": m.group(4), "slots": (m.group(3) or "")[1:-1],
                          "line": src.count("\n", 0, m.start()) + 1}
    for m in re.finditer(r"\\[se]it\{templates\}\{", src):
        # a row 'templates': entries NAME[slots]: words, separated by ';' (a template given in words, no atoms)
        body, _ = balanced(src, m.end() - 1, "{", "}")
        for entry in split_top(body, ";"):
            head = split_top(entry, ":")[0]
            t = lex(head)
            if t and t[0].kind == "ALIAS" and t[0].name not in defs:
                defs[t[0].name] = {"rhs": "", "slots": "", "words": entry[len(head) + 1:].strip(),
                                   "line": src.count("\n", 0, m.start()) + 1}
    for m in re.finditer(r"^\\\(\s*(\\Pt\{?\d\}?|\\Kt)\s*\\\)\s*&\s*([^&]*)&", src, re.M):
        t = lex(m.group(1))
        if t and t[0].kind == "ALIAS" and t[0].name not in defs:
            defs[t[0].name] = {"rhs": "", "slots": "", "words": m.group(2).strip(),
                               "line": src.count("\n", 0, m.start()) + 1}
    return defs


def split_top(s, sep):
    """s split at the separator sep outside braces, brackets and parentheses."""
    out, depth, cur = [], 0, []
    esc = False
    for ch in s:
        if esc or ch == "\\":
            esc = not esc and ch == "\\"
            cur.append(ch)
            continue
        if ch in "{[(":
            depth += 1
        elif ch in "}])":
            depth -= 1
        if ch == sep and depth == 0:
            out.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    out.append("".join(cur))
    return out


def head_name(tex):
    toks = lex(tex)
    if not toks:
        return None
    t = toks[0]
    if t.kind == "VERB":
        return t.name + ("_" + t.sub if t.sub else "")
    if t.kind == "ALIAS":
        return t.name + ("_" + t.sub if t.sub and t.name not in ("P6",) else "")
    return None


MENTION = re.compile(r"\\Pt\{?(\d)|\\(Kt)(?![A-Za-z])|\\(g[A-Z][A-Za-z]*)|\\[BC]x\{([A-Za-z]+)\}|\\mathrm\{(Tot|Euclid)\}")


def alias_mentions(text):
    out = set()
    for m in MENTION.finditer(text):
        if m.group(1):
            out.add("P" + m.group(1))
        elif m.group(2):
            out.add("K")
        elif m.group(3):
            if m.group(3) in MACRO_ALIAS:
                out.add(MACRO_ALIAS[m.group(3)])
        else:
            out.add(m.group(4) or m.group(5))
    return out


FACTS_HEADER = re.compile(r"^\s*name\s*&\s*fact\s*&\s*reference\b[^\n]*\\\\", re.I | re.M)
RANGE = re.compile(r"\\(Pt|Rf)\{?(\d)\}?\s*\\?\)?\s*(?:--|\\text\{--\})\s*\\?\(?\s*\\\1\{?(\d)\}?")


def cited_by_table(src):
    """Names declared by citation: the first column of a table whose header is 'name & fact & reference'. These are
    standard facts cited, not proved, so they get no expansion in atoms: the expander reads each as one opaque leaf
    ('cite:NAME'). A range \\Pt1--\\Pt4 declares P1, ..., P4; a macro is read by the lexer (\\Kt is K); a bare word
    (S, Bands, LP) is the name itself, as written in \\mathrm{...} in the proofs."""
    src = strip_comments(src)
    out = set()
    for h in FACTS_HEADER.finditer(src):
        end = src.find("\\end{tabular}", h.end())
        body = src[h.end():end if end >= 0 else len(src)]
        for row in re.split(r"\\\\", body):
            row = re.sub(r"\\hline", "", row).strip()
            if not row or "&" not in row:
                continue
            cell = row.split("&", 1)[0]
            for m in RANGE.finditer(cell):
                lo, hi = int(m.group(2)), int(m.group(3))
                out |= {("P" if m.group(1) == "Pt" else "R") + str(k) for k in range(lo, hi + 1)}
            cell = RANGE.sub(" ", cell)
            out |= alias_mentions(cell)
            if re.search(r"\\Mf(?![A-Za-z])", cell):
                out.add("M")
            for m in re.finditer(r"\\Rf\{?(\d)\}?", cell):
                out.add("R" + m.group(1))
            bare = re.sub(r"\\\(.*?\\\)|\\[A-Za-z]+(\{[^{}]*\})?", " ", cell)
            out |= set(re.findall(r"(?<![A-Za-z\\])[A-Z][A-Za-z0-9]*(?![A-Za-z0-9])", bare))
    return out


# ---------------------------------------------------------------------------------------------------------
# Expansion of aliases to atoms (nested aliases expand recursively; a cycle is an error)

class Expander:
    def __init__(self, defs):
        self.defs = defs
        self.cache = {}

    def key(self, f):
        h = f.head
        cands = []
        if h.kind == "ALIAS":
            if h.part:
                cands.append(f"{h.name}({h.part})")
            if h.sub:
                cands.append(f"{h.name}_{h.sub}")
            cands.append(h.name)
        elif h.kind == "VERB" and h.sub:
            cands.append(f"{h.name}_{h.sub}")
        if h.sub and re.fullmatch(r"\d+", h.sub):
            cands.append(f"{h.name}_p")  # an instance at a given prime: Name_2 = Name_p[p:=2]
        return next((c for c in cands if c in self.defs), None)

    def word(self, items, stack=()):
        """The atom word of an expression: a list of atoms and markers, items separated by ';'."""
        out = []
        for ch in items:
            if out:
                out.append(";")
            first = True
            for f in ch:
                if not isinstance(f, Factor):
                    continue
                if not first:
                    out.append("o")
                first = False
                out += self.factor(f, stack)
        return out

    def factor(self, f, stack):
        h = f.head
        w = []
        if h.kind == "GROUP":
            w = ["("] + self.word(f.body, stack) + [")"]
        elif h.kind == "VERB":
            k = self.key(f)
            if k and k not in ("I", "V") and k not in stack:
                w = ["("] + self.expand(k, stack) + [")"]
            else:
                base = h.name + ("_" + PLACE.get(h.sub, "x") if h.name in INDUCTION and h.sub else "")
                w = [base]
            if f.body:
                w += ["("] + self.word(f.body, stack) + [")"]
        elif h.kind == "ALIAS":
            k = self.key(f)
            if k is None:
                w = ["?" + h.name]
            elif k in stack:
                raise ValueError("alias cycle: " + " -> ".join(stack + (k,)))
            else:
                w = ["("] + self.expand(k, stack) + [")"]
        else:
            w = ["ref"]
        if h.dual:
            w = ["dual", "("] + w + [")"]
        return w

    def expand(self, k, stack=()):
        if k in self.cache:
            return self.cache[k]
        d = self.defs[k]
        if d.get("cited") or (not d["rhs"].strip() and d.get("words")):
            # a cited fact or a template given in words: one opaque leaf
            self.cache[k] = [("cite:" if d.get("cited") else "tpl:") + k]
            return self.cache[k]
        items, _, _ = parse(d["rhs"])
        w = self.word(items, stack + (k,))
        self.cache[k] = w
        return w


PLACE = {"chain": "chain", "k": "level", "L": "level", "d": "degree", "N": "count", "n": "dim", "r": "rank"}


# ---------------------------------------------------------------------------------------------------------
# Typing rules

formal_integral = {}
CONTINUUM = re.compile(r"\\(int|lim|liminf|limsup|log|ln|exp|sup|inf|Leb|mathbb\{R\}|R)(?![A-Za-z])")


def minmax_kind(e, k):
    """What a min or max at e[k] does: the least element (iota), a readout (an identity of exponents),
    a threshold in a hypothesis (a list of inequalities), a chosen constant, or other."""
    before = e[:k]
    last_open = max(before.rfind("["), before.rfind("{"))
    seg = before[last_open + 1:] if last_open >= 0 else before
    seg = re.split(r",|;", seg)[-1]
    if re.search(r"\\(?:iota|gInd)[^\[]{0,30}\[\s*$", before[:last_open + 1]) or re.search(r"least|\\min\\\{k", e[k - 5:k + 12]):
        return "least element"
    if re.search(r":=\s*$|:=[^=]*$", seg):
        return "chosen constant"
    if re.search(r"(=)\s*$", seg) or re.search(r"=\s*\\(min|max)", e[k - 3:k + 5]):
        return "readout"
    if re.search(r"(\\le|\\ge|<|>|\\lt|\\gt)\s*[^\\]{0,4}$", seg):
        return "threshold"
    return "other"


def rules():
    return {
        "T1": "every alias a source uses is defined in it, with an expansion or in words, or cited",
        "T2": "the dual mark ^vee is applied to an estimate, never to an identity I (alpha^vee is order reflection)",
        "T3": "ind (iota) names its induction (a subscript or data); a bare ind does not say what is well-founded",
        "T4": "V reads something: an identity, data or a cited result to its right in the chain",
        "T5": "min and max (semifield rule): reported by use, the least element, a readout, a threshold (a list of "
              "inequalities), a chosen constant (such as a parallel sum), or other",
        "T6": "no continuum notion (limit, sup, inf, Lebesgue, R, exp, ln, a log that is not the ceiling of log_2, an "
              "integral in a source without the formal integral) in a proof line",
        "T7": "the alias expansions terminate (no cycle among nested aliases)",
        "T8": "the synonyms alpha, iota and beta of eq, ind_x and Scale, Arch or Floor: reported, with the word to "
              "use",
    }


def check_line(rec, items, gloss, nmath):
    issues = []
    paper = rec["paper"]
    for ch in items:
        facs = [f for f in ch if isinstance(f, Factor)]
        for idx, f in enumerate(facs):
            h = f.head
            if h.dual and h.kind == "VERB" and h.name == "I":
                issues.append(("T2", "I^vee"))
            if h.kind == "VERB" and h.name in INDUCTION and not h.sub and not f.data and not f.body:
                issues.append(("T3", "bare " + h.name))
            if h.kind == "VERB" and h.name in SYNONYMS:
                issues.append(("T8", h.name + " (" + SYNONYMS[h.name] + ")"))
            if h.kind == "VERB" and h.name == "V" and not f.data and idx == len(facs) - 1 and len(ch) == len(facs):
                issues.append(("T4", "V with nothing to read"))
    for m in re.finditer(r"\\(min|max)(?![A-Za-z])", rec["expr"]):
        issues.append(("T5", m.group(1) + ": " + minmax_kind(rec["expr"], m.start())))
    e = rec["expr"]
    for m in CONTINUUM.finditer(e):
        w = m.group(1)
        before = e[:m.start()]
        if w == "int" and formal_integral.get(paper):
            continue  # the source defines the formal integral of a polynomial
        if w == "log" and e.startswith("_2", m.end()) and before.count("\\lceil") + before.count("\\lfloor") > \
                before.count("\\rceil") + before.count("\\rfloor"):
            continue  # ceil(log_2 x): the exponent of a mass
        issues.append(("T6", w))
    return issues


# ---------------------------------------------------------------------------------------------------------
# Normal forms and mining: the patterns that survive normalization, ranked by compression gain

KIND = {"chain": "chain", "{\\rm chain}": "chain", "k": "level", "L": "level", "q": "level", "d": "degree",
        "N": "count", "n": "dim", "r": "rank", "x": "x", "i": "index", "j": "index", "l": "index", "t": "level",
        "s": "level", "\\rm halving": "halving", "halving": "halving"}


def sym(f, expand=None):
    """The symbol of a factor: verbs keep their place and their induction kind, aliases their name (or, with
    expand, their atom word), references become ref; the dual mark is kept."""
    h = f.head
    if h.kind == "VERB":
        base = h.name
        if h.name in INDUCTION:
            base += "_" + KIND.get(h.sub, "x") if h.sub else ""
        elif h.sub:
            base += "_" + ("p" if h.sub in ("p", "q") else "C" if h.sub in ("\\C", "C") else h.sub)
        if f.body:
            base += "(" + " o ".join(chain_syms(f.body[0], expand)) + ")"
    elif h.kind == "ALIAS":
        if expand is not None:
            k = expand.key(f)
            w = expand.expand(k) if k else ["?" + h.name]
            base = "(" + " ".join(w) + ")" if len(w) > 1 else w[0]
        else:
            base = h.name + (f"({h.part})" if h.part else "") + (f"^{h.sub}" if h.name == "P6" and h.sub else "")
    elif h.kind == "GROUP":
        base = "(" + " ; ".join(" o ".join(chain_syms(c, expand)) for c in f.body) + ")"
    elif h.kind in ("SELF", "COND"):
        base = "self" if h.kind == "SELF" else "cond"
    else:
        base = "ref"
    return base + ("^v" if h.dual else "")


def chain_syms(chain, expand=None):
    return [sym(f, expand) for f in chain if isinstance(f, Factor)]


COLLAPSE = [  # second-order rules used as rewrite rules on the skeleton (left to right, to a fixed point)
    (("V", "V"), ("V",)),          # Lemma S composes (K(1) for the constants)
    (("I", "I"), ("I",)),          # identities compose by substitution
    (("alpha", "I"), ("I",)),      # an identity checked by the semifield laws is an identity
    (("I", "alpha"), ("I",)),
    (("eq", "I"), ("I",)),
    (("I", "eq"), ("I",)),
    (("ref", "ref"), ("ref",)),    # two cited results in sequence are one cited derivation
]


def collapse(seq):
    seq = list(seq)
    changed = True
    while changed:
        changed = False
        for (a, b), rep in COLLAPSE:
            for i in range(len(seq) - 1):
                if seq[i] == a and seq[i + 1] == b:
                    seq[i:i + 2] = list(rep)
                    changed = True
                    break
    # (V o I) o (V o I) -> V o I: estimates compose
    i = 0
    while i + 3 < len(seq):
        if seq[i:i + 4] == ["V", "I", "V", "I"]:
            seq[i:i + 4] = ["V", "I"]
        else:
            i += 1
    return seq


def repair(seqs, rounds=40, min_count=4):
    """Re-Pair: replace the most frequent adjacent pair by a new symbol, round by round. A rule used c times
    saves c - 2 symbols (c pairs become c symbols, the rule costs 2): the gain of a pattern."""
    seqs = [list(s) for s in seqs]
    rules_ = []
    for r in range(rounds):
        cnt = collections.Counter()
        for s_ in seqs:
            for a, b in zip(s_, s_[1:]):
                cnt[(a, b)] += 1
        if not cnt:
            break
        (a, b), c = cnt.most_common(1)[0]
        if c < min_count:
            break
        name = f"R{r + 1}"
        rules_.append((name, a, b, c))
        for s_ in seqs:
            i = 0
            while i < len(s_) - 1:
                if s_[i] == a and s_[i + 1] == b:
                    s_[i:i + 2] = [name]
                i += 1
    return rules_


def unfold(sym_, table):
    if sym_ in table:
        a, b = table[sym_]
        return unfold(a, table) + " o " + unfold(b, table)
    return sym_

# ---------------------------------------------------------------------------------------------------------
# Driver

def analyse(srcs):
    report = {"rules": rules(), "papers": {}}
    for p, src in srcs.items():
        own = alias_defs(src, p)
        defs = dict(own)
        # cited facts (a 'name & fact & reference' table) and templates (a 'templates' row) are opaque leaves:
        # no expansion in atoms
        cited = cited_by_table(src)
        for name in cited:
            defs.setdefault(name, {"rhs": "", "slots": "", "line": 0, "cited": True})
        defs = {k: (v if isinstance(v, dict) else {"rhs": v, "slots": "", "line": 0}) for k, v in defs.items()}
        ex = Expander(defs)
        cycle = []
        for k in defs:
            try:
                ex.expand(k)
            except ValueError as e:
                cycle.append(str(e))
        formal_integral[p] = bool(re.search(r"formal (integral|antiderivative)", src))
        recs = lines_of(src, p)
        classes = collections.Counter()
        used = collections.Counter()
        issues = []
        words = []
        for r in recs:
            items, gloss, nmath, keyed = parse_line(r["expr"])
            c = classify(items, nmath, keyed)
            r["class"] = c
            classes[c] += 1
            for f in factors(items):
                if f.head.kind == "ALIAS":
                    used[ex.key(f) or f.head.name] += 1
                elif f.head.kind == "VERB" and f.head.sub and ex.key(f):
                    used[ex.key(f)] += 1
            for code, what in check_line(r, items, gloss, nmath):
                issues.append({"rule": code, "what": what, "label": r["label"], "item": r["item"], "line": r["line"]})
            try:
                w = ex.word(items)
            except ValueError as e:
                w = []
                cycle.append(str(e))
            r["word"] = " ".join(w)
            words.append(w)
        own_names = set(own)
        undefined = sorted(k for k in used if k not in defs and k.split("(")[0].split("_")[0] not in defs)
        base = lambda k: k.split("(")[0]
        no_row = sorted({base(k) for k in used} - {base(k) for k in own_names | cited})
        inner = set()
        for k in own_names:
            inner |= alias_mentions(own[k]["rhs"])
        unused = sorted(k for k in own_names if base(k) not in {base(u) for u in used} and k.split("_")[0] not in inner
                        and k not in inner)
        for k in undefined:
            issues.append({"rule": "T1", "what": k, "label": "", "item": "", "line": 0})
        for c in cycle:
            issues.append({"rule": "T7", "what": c, "label": "", "item": "", "line": 0})
        report["papers"][p] = {
            "lines": len(recs), "classes": dict(classes),
            "aliases_used": dict(used.most_common()),
            "defined_here": sorted(own_names), "cited": sorted(cited),
            "undefined": undefined, "used_without_definition_here": no_row, "defined_not_used": unused,
            "expansions": {k: " ".join(ex.expand(k)) for k in defs if k not in cycle},
            "issues": issues, "records": recs,
        }
    return report


def mine(srcs, min_count=5, rounds=30):
    """Normal forms (aliases expanded to atoms, collapsed) of every chain, and the Re-Pair rules on them,
    each with its uses, its gain and its occurrences by paper and by result."""
    view = []
    for p, src in srcs.items():
        defs = dict(alias_defs(src, p))
        defs = {k: (v if isinstance(v, dict) else {"rhs": v, "slots": "", "line": 0}) for k, v in defs.items()}
        ex = Expander(defs)
        for r in lines_of(src, p):
            items, _, _, _ = parse_line(r["expr"])
            cur = []
            for t in ex.word(items) + [";"]:
                if t == ";":
                    if cur:
                        view.append((p, r["label"], collapse(cur)))
                    cur = []
                elif t not in ("(", ")", "o"):
                    cur.append(t)
    rules_ = repair([s_ for _, _, s_ in view], rounds=rounds, min_count=min_count)
    table = {n: (a, b) for n, a, b, c in rules_}
    out = []
    for n, a, b, c in rules_:
        toks = unfold(n, table).split(" o ")
        occ, res = collections.Counter(), set()
        for p, lab, s_ in view:
            for i in range(len(s_) - len(toks) + 1):
                if s_[i:i + len(toks)] == toks:
                    occ[p] += 1
                    res.add((p, lab))
        out.append({"rule": n, "expansion": " o ".join(toks), "uses": c, "gain": c - 2,
                    "papers": dict(occ), "results": len(res)})
    return out


def main(argv):
    out = None
    if "--json" in argv:
        i = argv.index("--json")
        out = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    flags = [a for a in argv if a.startswith("--")]
    srcs = {}
    for a in argv:
        if a.startswith("--") or "=" not in a:
            continue
        p, path = a.split("=", 1)
        srcs[p] = Path(path).read_text()
    if not srcs:
        print("usage: python3 -m qpp.syntax [--json OUT] [--mine] NAME=PATH ...", file=sys.stderr)
        return 2
    if "--mine" in flags:
        for r in mine(srcs):
            print(f"{r['rule']:4} uses {r['uses']:4} gain {r['gain']:4} results {r['results']:4} {r['papers']}  "
                  f"{r['expansion']}")
        return 0
    rep = analyse(srcs)
    bad = 0
    for p, d in rep["papers"].items():
        cl = d["classes"]
        tot = d["lines"] or 1
        print(f"{p}: {d['lines']} proof lines; G {cl.get('G', 0)} ({100 * cl.get('G', 0) // tot}%), "
              f"K {cl.get('K', 0)}, R {cl.get('R', 0)}, M {cl.get('M', 0)}, F {cl.get('F', 0)} "
              f"({100 * cl.get('F', 0) // tot}%)")
        print(f"   aliases used: {', '.join(f'{k} {v}' for k, v in d['aliases_used'].items())}")
        print(f"   defined here: {', '.join(d['defined_here']) or '-'}; cited: {', '.join(d['cited']) or '-'}; "
              f"undefined: {', '.join(d['undefined']) or '-'}")
        print(f"   strict rule (an expansion in this source): used without one: "
              f"{', '.join(d['used_without_definition_here']) or '-'}; defined, not used in proofs: "
              f"{', '.join(d['defined_not_used']) or '-'}")
        by = collections.Counter(i["rule"] for i in d["issues"])
        print(f"   issues: {dict(sorted(by.items()))}")
        bad += len(d["issues"])
    if out:
        Path(out).write_text(json.dumps(rep, indent=1))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
