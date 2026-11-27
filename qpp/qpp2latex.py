"""qpp2latex: a Q++ 0.2 file to its LaTeX and its bibliography.

The LaTeX is the body of the section, in the conventions that latex2qpp reads (`stmt` displays of `\\sit` rows,
`expr` displays of `\\eit` lines), with no layout of its own: prose as paragraphs, each item in its environment with
its description, each proof after its item. A cited fact (`cit`) is a `fact` whose source is cited in its title. In
the article each proof line is transcoded into the sentences that its words stand for (qpp/prooftex.py), and the
origin of a result is printed as text.

The bibliography is printed from the citations: it holds the entry of every key that the printed LaTeX cites (\\cite
and its relatives, in the prose, the rows and the frame), and nothing else. A key is taken from the store that the
`bib` line names (modules/references.bib for the modules); the key of a `cit` item is the key of the store's entry
with its DOI when there is one, else a key made from the DOI with a minimal entry. A cited key that is neither, and a
`bib` line that names no file, are errors.

A paper (a doc that .github/scripts/paper_cuts.py made, `article`) is printed for a reader, not for the checks: its
proofs read the closing words of the checker in fewer words (qpp/prooftex.py, PAPER) and each names its Lean
declarations once (proof_tex), and its rows, proofs and vocabulary print the names of PAPER_NAMES as their symbols.
It prints no origin line: a cited fact prints its sources after its statement, as one sentence of citations with
their locators (paper_sources), and every other item prints none, what it cites being in its prose and its proof.
The modules and qpp/examples print as before.

The article leaves out what only the checks read: the `core` rows (the algebraic cores that Lean proves), the proof
lines keyed `core`, and the fixtures (`\\FIX`). With --full PATH the full printing, which keeps them, is written too:
it is the LaTeX that latex2qpp, the status page and the round trip of the migration read.

Usage: python3 -m qpp.qpp2latex SRC.qpp [-o OUT.tex] [--bib OUT.bib] [--full FULL.tex]

The vocabulary lines print at their place, consecutive lines as one `stmt` display with one row each keyed by its
kind (word, define, type, relation, given relation for a context, alias); each row is read back by latex2qpp
(vocab_row) and must give the terms of its line (vocab_tree), else the printing fails.

The bibliography is written to OUT.bib (OUT.tex with the suffix .bib) unless --bib names another file. With a `frame`
line (a paper) the body goes into the frame, whose \\bibliography names that file, and each cited DOI must have its
entry in the store. The skeleton of a paper, papers/NAME/skeleton.tex (qpp/source.py, read_skeleton), is printed as
NAME.tex next to it unless -o names another file: the skeleton with each line `% qpp: include sec:x` replaced by the
section sec:x, printed from its module.
"""
import re
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    __package__ = "qpp"

from . import prooftex as X
from . import source as S
from . import texmath as T

ENV = {"cit": "fact"}
VERB_TEX = {"eq": "\\gEq", "neq": "\\gNeq", "ind": "\\gInd", "I": "\\gI", "V": "\\gV"}
SCALE_TEX = {"Scale", "Arch", "Floor"}


def split_parts(q, sep=";"):
    """the parts of a row, split at the separators outside braces, brackets and parentheses"""
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


def hole_tex(part):
    """the LaTeX of a part that is a hole ?{...}, or None"""
    if part.startswith("?{") and part.endswith("}"):
        return part[2:-1]
    return None


def whole_hole(text):
    """the LaTeX of a row or a line that is one hole ?{...} (its braces matched as LaTeX's: \\{ and \\} are not
    braces), or None"""
    if not text.startswith("?{"):
        return None
    depth, i = 0, 1
    while i < len(text):
        c = text[i]
        if c == "\\":
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return text[2:i] if i == len(text) - 1 else None
        i += 1
    return None


def part_tex(part):
    h = hole_tex(part)
    if h is not None:
        return h
    return T.stmt_print(T.parse_qpp_item(part), T.to_tex)


def row_tex(q):
    """the LaTeX of a statement row: its parts, formal ones printed from their terms, holes as they are"""
    h = whole_hole(q)
    if h is not None:
        return h
    out = ""
    for i, p in enumerate(split_parts(q)):
        t = part_tex(p)
        if i:
            out += ";" if t.startswith("\\ ") else ";\\ "
        out += t
    return out


WORD_TOK = re.compile(r"\s*(\[|\{|\(|\)|;|,|:(?!=)|\^v|\bo\b|[A-Za-z][A-Za-z0-9_']*(?::[A-Za-z0-9_:\-]+)?)")


def balanced(s, i, o, c):
    depth, j = 0, i
    while j < len(s):
        if s[j] == o:
            depth += 1
        elif s[j] == c:
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    raise ValueError(f"unbalanced {o} in {s!r}")


def split_top_parts(d):
    """the parts of reference data at `;` outside brackets, the first kept even when empty"""
    out, depth, cur = [], 0, ""
    for ch in d:
        depth += (ch in "{[(") - (ch in "}])")
        if ch == ";" and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    return out + [cur]


def side_tex(x):
    """a side goal of a reference, `HYP by W`: the clause, then the word that proves it"""
    depth = 0
    for k, ch in enumerate(x):
        depth += (ch in "{[(") - (ch in "}])")
        if depth == 0 and x.startswith(" by ", k):
            return part_tex(x[:k].strip()) + "\\ \\text{by}\\ " + word_tex(x[k + 4:].strip())
    raise ValueError(f"a side goal `HYP by W`: {x!r}")


CHAIN_REL = {"<=": "\\le", ">=": "\\ge", "<": "<", ">": ">", "=": "="}


def has_by(x):
    """whether x has ` by ` at top level"""
    depth = 0
    for k, ch in enumerate(x):
        depth += (ch in "{[(") - (ch in "}])")
        if depth == 0 and x.startswith(" by ", k):
            return True
    return False


def top_by(x):
    """the place of the first ` by ` of x at top level, or None"""
    depth = 0
    for k, ch in enumerate(x):
        depth += (ch in "{[(") - (ch in "}])")
        if depth == 0 and x.startswith(" by ", k):
            return k
    return None


def link_tex(x):
    """a later link of a chain, `R C by W`: the relation, the right side, then the word that proves the link"""
    m = re.match(r"(<=|>=|<|>|=)\s*", x)
    if not m:
        raise ValueError(f"a link of a chain `R C by W`: {x!r}")
    rest = x[m.end():]
    depth = 0
    for k, ch in enumerate(rest):
        depth += (ch in "{[(") - (ch in "}])")
        if depth == 0 and rest.startswith(" by ", k):
            return (CHAIN_REL[m.group(1)] + " " + T.to_tex(T.parse_qpp(rest[:k].strip())) + "\\ \\text{by}\\ "
                    + word_tex(rest[k + 4:].strip()))
    raise ValueError(f"a link of a chain `R C by W`: {x!r}")


def at_tex(x):
    """the point of the reading of a program row, `at v := t, ...`: \\text{at} and the assignments"""
    return "\\text{at}\\ " + data_tex(re.sub(r"^\s*at\s+", "", x))


def is_at(x):
    return re.match(r"\s*at\s", x) is not None


def bar_parts(d):
    """the data of V[written | turned] at the `|` outside brackets: [written, turned], or [d] with no `|`"""
    depth = 0
    for i, ch in enumerate(d):
        depth += (ch in "([{") - (ch in ")]}")
        if ch == "|" and depth == 0:
            return [d[:i].strip(), d[i + 1:].strip()]
    return [d]


def data_tex(d):
    T.DATA_MODE[0] = True
    try:
        terms = T.parse_qpp_list(d)
    finally:
        T.DATA_MODE[0] = False
    return ",".join(T.to_tex(t) for t in terms)


def word_tex(w):
    """the LaTeX of a proof word: verbs as their macros, references as \\cref, data and formulas printed from their
    terms"""
    out, i, last = [], 0, None
    while i < len(w):
        if w[i].isspace():
            i += 1
            continue
        if w[i] == "[":
            d, i = balanced(w, i, "[", "]")
            # the data of `sum` is the word of one term (of `logic` and `unfold` a word); that of `pow` and `div` a
            # term, then a word after `;`
            if last in ("sum", "logic", "unfold"):
                out.append("[" + word_tex(d) + "]")
            elif last == "trichotomy":
                # trichotomy: the word that empties each part left out, after `;`
                out.append("[" + ";\\ ".join(word_tex(x) for x in split_parts(d)) + "]")
            elif last == "with":
                # with: a clause and the word that proves it, then the word on the goal after `;`
                parts = split_parts(d)
                out.append("[" + side_tex(parts[0]) + "".join(";\\ " + word_tex(x) for x in parts[1:]) + "]")
            elif last == "chain":
                # chain: the first link a clause and its word, each later link a relation, a right side and its word,
                # then the word on the goal after `;` (V when it is left out)
                parts = split_parts(d)
                out.append("[" + ";\\ ".join(side_tex(parts[0]) if k == 0 else link_tex(x) if has_by(x) else word_tex(x)
                                              for k, x in enumerate(parts)) + "]")
            elif last == "cases":
                # cases: the clause, then the words of the two cases after `;`
                parts = split_parts(d)
                out.append("[" + part_tex(parts[0].strip()) + "".join(";\\ " + word_tex(x) for x in parts[1:]) + "]")
            elif last == "face":
                # face: the word of the value; each point as assignments and the words of its rows; the ties
                # and their word; at m = 2 the word of the gap
                segs = []
                for n_, x in enumerate(split_parts(d)):
                    x = x.strip()
                    k = top_by(x) if n_ else None
                    if k is None:
                        segs.append(word_tex(x))
                    elif ":=" in x[:k]:
                        segs.append(data_tex(x[:k]) + "\\ \\text{by}\\ " + word_tex(x[k + 4:].strip()))
                    else:
                        segs.append(side_tex(x))
                out.append("[" + ";\\ ".join(segs) + "]")
            elif last == "V" and len(bar_parts(d)) == 2:
                # the equations after `|` are read from their other side (the proof writes the side)
                written, turned = bar_parts(d)
                out.append("[" + (data_tex(written) if written else "") + "\\mid " + data_tex(turned) + "]")
            elif last in ("LP", "prog"):
                # the LP certificate: the prices of the rows, then further data after `;`; prog: the prices, then
                # each point as assignments
                out.append("[" + ";\\ ".join(data_tex(x) for x in split_parts(d)) + "]")
            elif last in ("pow", "div", "take", "term", "ind"):
                # take: the witnesses as assignments, then the word on the rest after `;`; ind: the binder, then the
                # words of the first case and of the step
                parts = split_parts(d)
                out.append("[" + data_tex(parts[0]) + "".join(";\\ " + word_tex(x) for x in parts[1:]) + "]")
            elif len(split_top_parts(d)) > 1 and all(" by " in x or is_at(x) for x in split_top_parts(d)[1:]):
                # a reference (or an alias) with side goals after `;`: `HYP by W`, a clause and the word that proves
                # it; or the point of the reading of a program row, `at v := t, ...`
                head, *sides = [x.strip() for x in split_top_parts(d)]
                out.append("[" + (data_tex(head) if head else "") + "".join(
                    ";\\ " + (at_tex(x) if is_at(x) else side_tex(x)) for x in sides) + "]")
            elif len(split_top_parts(d)) > 1:
                bad = next(x.strip() for x in split_top_parts(d)[1:] if " by " not in x and not is_at(x))
                raise ValueError(f"the data [{d}]: a part after `;` is a side goal `HYP by W`, not {bad!r}")
            else:
                out.append("[" + data_tex(d) + "]")
            continue
        if w[i] == "{":
            f, i = balanced(w, i, "{", "}")
            out.append(" " + (hole_tex(f) if hole_tex(f) is not None else part_tex(f)) + " ")
            continue
        m = WORD_TOK.match(w, i)
        if not m or m.end() == i:
            raise ValueError(f"word: cannot read {w[i:i + 12]!r}")
        tok, i = m.group(1), m.end()
        last = tok
        if tok == ":":
            out.append(":\\ " + row_tex(w[i:].strip()))
            break
        if tok == "o":
            out.append("\\circ ")
        elif tok in (";", ","):
            out.append(tok + "\\ ")
        elif tok in ("(", ")", "^v"):
            out.append({"^v": "^\\vee"}.get(tok, tok))
        elif ":" in tok:
            label, part = tok, ""
            m2 = re.match(r"^(.*?)\((\w+)\)$", tok)
            if m2:
                label, part = m2.group(1), m2.group(2)
            out.append(f"\\cref{{{label}}}" + (f"({part})" if part else ""))
            j = i
            if j < len(w) and w[j] == "(":
                p, i = balanced(w, j, "(", ")")
                out[-1] += f"({p})"
        else:
            base, _, sub = tok.partition("_")
            if out and re.search(r"(\\mathrm\{\w+\}|\\g[A-Za-z]+)(_\{\w*\})?$", out[-1]):
                out.append("\\,")  # two words in a row (cases V): a thin space, which latex2qpp reads past
            if base in VERB_TEX:
                out.append(VERB_TEX[base] + (f"_{{{sub}}}" if sub else ""))
            elif base in SCALE_TEX:
                out.append(f"\\mathrm{{{base}}}" + (f"_{{{sub}}}" if sub else ""))
            else:
                out.append(f"\\mathrm{{{base}}}" + (f"_{{{sub}}}" if sub else ""))
    s = "".join(out)
    return re.sub(r"\s+", " ", s).strip()


# a citation: \cite and its relatives, with up to two optional arguments and several keys
CITE = re.compile(r"\\(?:[cC]ite|[cC]itep|[cC]itet|citealp|citealt|citeauthor|citeyear|citeyearpar|parencite|"
                  r"[tT]extcite|autocite|footcite|nocite)\*?\s*(?:\[[^\]]*\]\s*){0,2}\{([^{}]*)\}")
ENTRY = re.compile(r"@\w+\{([^,\s]+),.*?\n\}", re.S)


def store_text(path):
    """the text of the store (the .bib file of the `bib` line); no `bib` line is an empty store, a `bib` line that
    names no file is an error"""
    if not path:
        return ""
    if not Path(path).is_file():
        raise ValueError(f"the bibliography {path} is not a file")
    return Path(path).read_text(encoding="utf-8")


def bib_entries(path):
    """{doi (lower case): (key, entry text)} of a .bib file"""
    out = {}
    for m in ENTRY.finditer(store_text(path)):
        d = re.search(r"\bdoi\s*=\s*\{([^}]*)\}", m.group(0))
        if d:
            out[d.group(1).strip().lower()] = (m.group(1), m.group(0))
    return out


def bib_keys(path):
    """{key: entry text} of a .bib file"""
    return {m.group(1): m.group(0) for m in ENTRY.finditer(store_text(path))}


def cited_keys(tex):
    """the keys that a LaTeX text cites, outside its comments"""
    text = re.sub(r"(?<!\\)%[^\n]*", "", tex)
    return {k.strip() for m in CITE.finditer(text) for k in m.group(1).split(",") if k.strip() not in ("", "*")}


def doi_key(doi):
    return "doi_" + re.sub(r"[^A-Za-z0-9]", "_", doi)


def cite_of(it, bib):
    """(key, entry) of the source of a cited fact"""
    doi = it.row("doi").text.strip()
    if doi.lower() in bib:
        return bib[doi.lower()]
    key = doi_key(doi)
    return key, f"@misc{{{key},\n  doi  = {{{doi}}},\n  note = {{cited by its DOI}}\n}}"


def code_tex(name):
    """a Mathlib name in typewriter type, which may break after each dot and each underscore"""
    return "\\texttt{" + name.replace("_", "\\_\\allowbreak ").replace(".", ".\\allowbreak ") + "}"


REF_WORD = re.compile(r"(?<![\w:])([A-Za-z]+:[A-Za-z0-9:_\-]+)(?:\((\w+(?: \w+)*)\))?")  # as kernel.refs_in

# the names of rows that a paper prints as symbols: the two halves (x^+, x^-) of a pair of positive rationals,
# the constant point \bar m whose coordinates are m, and the second index l' of the coordinates of a point. A name is
# here only where its symbol is not a name of the same row: gP, gM and zP, zM share a row with g and z, so they print
# as gamma and xi; kk shares rows with k and l, so it prints as l'
PAPER_NAMES = {
    "psiP": "\\psi^{+}", "psiM": "\\psi^{-}", "gP": "\\gamma^{+}", "gM": "\\gamma^{-}", "nuP": "\\nu^{+}",
    "nuM": "\\nu^{-}", "zP": "\\xi^{+}", "zM": "\\xi^{-}", "yP": "y^{+}", "yM": "y^{-}", "vP": "v^{+}", "vM": "v^{-}",
    "epsP": "\\varepsilon^{+}", "epsM": "\\varepsilon^{-}", "op": "o^{+}", "om": "o^{-}", "oP": "o^{+}", "oM": "o^{-}",
    "cP": "c^{+}", "cM": "c^{-}", "dP": "d^{+}", "dM": "d^{-}", "KP": "K^{+}", "KM": "K^{-}", "TP": "T^{+}",
    "TM": "T^{-}", "mb": "\\bar{m}", "kk": "l'"}
PAPER_NAME = re.compile(r"\\mathrm\{(" + "|".join(PAPER_NAMES) + r")\}(?=([\^']?))")


def paper_names(line):
    """a printed line of a paper with the names of PAPER_NAMES as their symbols, braced before a superscript"""
    return PAPER_NAME.sub(lambda m: "{" + PAPER_NAMES[m.group(1)] + "}" if m.group(2) else PAPER_NAMES[m.group(1)],
                          line)


def lean_decl(label, key):
    """the name of the Lean theorem of the row KEY of an item, as qpp/kernel.py names it (ident, key_ident)"""
    k = re.sub(r"[^A-Za-z0-9_]", "_", key.strip("()")) or "row"
    return re.sub(r"[^A-Za-z0-9_]", "_", label) + "_" + k


def cited_cores(doc, aliases):
    """{(label, key)} of the rows that only the checks read (texmath.checks_only) and that a printed proof line cites:
    by their key (lem:x(core name)), through an alias (alias Chart := lem:x(core)), or with no key where such a row is
    the one row of its item (fact:gap, whose one row is core). The article prints them in their items, so that a
    printed proof cites only printed rows; their proofs, the lines keyed by them, stay in the Lean"""
    rows = {it.label: [r.key for r in it.rows if r.key not in S.SPECIAL and r.key != "origin"] for it in doc.items()}
    out = set()
    for p in doc.proofs().values():
        for line in p.lines:
            if T.checks_only(line.key):
                continue
            text = line.text
            for name, target in aliases.items():
                text = re.sub(rf"(?<![\w:.']){name}(?![\w:('])", target, text)
            for m in REF_WORD.finditer(text):
                label, key = m.group(1), m.group(2)
                keys = rows.get(label, [])
                if key is None:
                    key = "(1)" if "(1)" in keys or len(keys) != 1 else keys[0]
                elif not T.checks_only(key):
                    key = f"({key})"
                if key in keys and T.checks_only(key):
                    out.add((label, key))
    return out


ONE_CITE = re.compile(r"\\cite(?:\[[^\]]*\])?\{[^}]*\}")  # one \cite[LOCATOR]{KEY} of an origin
# the version of a source that a locator follows, right after its citation: ", numbered as in its arXiv version ..."
VERSION = re.compile(r",\s*(?:numbered as in|read in|in) its arXiv version [^,;]*?(?:,\s*pp\.~[^,;]*?)?(?=[,;]|$)")


def paper_sources(it, printed=frozenset()):
    """the sentence of the sources of a cited fact in a paper: the citations of its origin, each with its locator and
    the version of the source that the locator follows, in their order and once each, but those whose keys the item
    already prints (printed: the keys of its heading and its statement), so that each source shows once; for a fact
    that only Mathlib proves, its declarations; None for an item that is no cited fact, or whose origin cites nothing
    that the item does not already print"""
    if it.kind != "cit":
        return None
    if getattr(it, "mathlib_origin", False):
        names = it.row("mathlib").text.strip().split(" (")[0].split(", ")
        return "Standard; in Mathlib as " + ", ".join(code_tex(n) for n in names) + "."
    o = it.row("origin")
    hole = whole_hole(o.text) if o is not None else None
    if hole is None:
        return None
    text = X.text_of(hole)
    cites = []
    for m in ONE_CITE.finditer(text):
        v = VERSION.match(text, m.end())
        c = m.group(0) + (v.group(0) if v else "")
        if c not in cites and not cited_keys(c) <= printed:
            cites.append(c)
    if not cites:
        return None
    return (", ".join(cites[:-1]) + " and " + cites[-1] if len(cites) > 1 else cites[0]) + "."


def item_tex(it, bib, full=True, shown=frozenset()):
    """the item in its environment; without full, its rows but those that only the checks read, except the core rows
    in shown (cited_cores)"""
    env = ENV.get(it.kind, it.kind)
    opt = it.title
    mathlib = None
    if it.kind == "cit" and it.row("doi"):
        key, _ = cite_of(it, bib)
        st = it.row("stmt")
        c = f"\\cite[{st.text}]{{{key}}}" if st else f"\\cite{{{key}}}"
        opt = f"{opt}, {c}" if opt else c
    elif it.kind == "cit":
        # a fact that Mathlib proves, with no DOI: its Mathlib name, in its title; a paper (.github/scripts/paper_cuts.py
        # marks its items mathlib_origin) titles the fact in words and names the declaration on an origin line
        names = it.row("mathlib").text.strip().split(" (")[0].split(", ")
        c = "Mathlib " + ", ".join(code_tex(n) for n in names)
        if full or not opt or not getattr(it, "mathlib_origin", False):
            opt = f"{opt}, {c}" if opt else c
        else:
            mathlib = f"\\tit{{origin}}{{cited: {c}}}"
    paper = X.PAPER[0] and not full
    if paper:
        mathlib = None  # the sentence of its sources (paper_sources) names the declarations
    lines = [f"\\begin{{{env}}}" + (f"[{{{opt}}}]" if opt else "") + f"\\label{{{it.label}}}"]
    lines += it.prose
    fixes = {}
    for i, fid in it.fix_rows:
        fixes.setdefault(i, []).append(fid)
    whole = [fid for k, fid, _ in it.fixes if k is None]
    rows = [(i, r) for i, r in enumerate(it.rows) if r.key not in S.SPECIAL and
            (full or not T.checks_only(r.key) or (it.label, r.key) in shown) and not (paper and r.key == "origin")]
    if rows:
        lines.append("\\begin{stmt}")
        for n, (i, r) in enumerate(rows):
            key = "" if r.key == "-" else r.key
            fx = "".join(f"\\FIX{{{f}}}" for f in fixes.get(i, []) + (whole if n == len(rows) - 1 else []))
            fx = fx if full else ""
            if not full and r.key == "origin" and whole_hole(r.text) is not None:
                # the article prints the origin of a result as text, which breaks across lines
                lines.append(f"\\tit{{{key}}}{{{X.text_of(whole_hole(r.text))}}}")
                continue
            lines.append(f"\\sit{{{key}}}{{{row_tex(r.text)}}}{fx}")
        if mathlib:
            lines.append(mathlib)
        lines.append("\\end{stmt}")
    elif mathlib:
        lines += ["\\begin{stmt}", mathlib, "\\end{stmt}"]
    sources = paper_sources(it, cited_keys("\n".join(lines))) if paper else None
    if sources:
        lines.append(f"\\par\\noindent {sources}")
    lines += it.after()
    lines.append(f"\\end{{{env}}}")
    return lines


def line_tex(text):
    """the LaTeX of a proof line: a hole as it stands, a word printed"""
    h = whole_hole(text)
    return h if h is not None else word_tex(text)


REF_DATA = re.compile(r"(?<![\w:])[a-z]+:[A-Za-z0-9]+(?:\([^()\[\]]*\))?\[")


def close_of(text, i):
    """the index of the bracket that closes the one opened at text[i]"""
    depth = 0
    for j in range(i, len(text)):
        depth += {"[": 1, "]": -1}.get(text[j], 0)
        if depth == 0:
            return j
    raise ValueError(f"an unclosed bracket in {text!r}")


def split_top(text, sep):
    """the parts of text at the separator sep outside brackets and parentheses"""
    parts, depth, cur = [], 0, ""
    for ch in text:
        depth += {"[": 1, "(": 1, "]": -1, ")": -1}.get(ch, 0)
        if ch == sep and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    return parts + [cur]


def without_data(text):
    """a proof line as the article prints it (for economy): every claim and every
    reference kept, the data of a reference dropped, its instantiation `[x := t, ...]` (Lean holds it); the
    hypotheses that a reference proves after the instantiation, `[...; C by W]`, stay"""
    out, i = "", 0
    while True:
        m = REF_DATA.search(text, i)
        if not m:
            return out + text[i:]
        j = close_of(text, m.end() - 1)
        parts = split_top(text[m.end():j], ";")
        head = ""
        if not all(":=" in a for a in split_top(parts[0], ",") if a.strip()):
            head = parts[0]  # not an instantiation: kept
        rest = ";".join(without_data(x) for x in parts[1:]).strip()
        # the side goals after `;` keep their place after the head, an empty head when the instantiation is dropped
        out += text[i:m.end() - 1] + (f"[{head.strip()}; {rest}]" if rest else f"[{head.strip()}]" if head.strip()
                                      else "")
        i = j + 1


def proof_tex(p, full=True, paper=False):
    """the proof; without full, none if it has only lines that the checks read (texmath.checks_only), and the
    lines without the data of their references (without_data); in a paper, the Lean theorems of its printed lines
    named once, after them"""
    rows = [r for r in p.lines if full or not T.checks_only(r.key)]
    # the article reads each line from its words, which print no instantiation but that of a call (qpp/prooftex.py)
    words = {(r.key, r.line): r.text for r in rows}
    if not full:
        rows = [S.Row(r.key, without_data(r.text) if whole_hole(r.text) is None else r.text, r.line) for r in rows]
    if not full and not rows and p.lines and not "".join(p.prose).strip():
        return []
    lines = ["\\begin{proof}" + (f"[{{{p.title}}}]" if p.title else "")] + p.prose
    if rows and not full:
        # the article: each line transcoded into the sentences of its words (qpp/prooftex.py)
        lines.append("\\begin{plines}")
        for r in rows:
            h = whole_hole(r.text)
            try:
                body = f"\\({h}\\)" if h is not None else X.line_prose(words[(r.key, r.line)])
            except ValueError as e:
                raise ValueError(f"line {r.line}: proof {p.label} {r.key}: {e}") from None
            lines.append(f"\\pline{{{r.key}}}{{{body}}}")
        if paper:
            names = [code_tex(lean_decl(p.label, r.key)) for r in rows]
            lines.append("\\par\\noindent Lean: " + (names[0] if len(names) == 1 else
                                                     ", ".join(names[:-1]) + " and " + names[-1]) + ".")
        lines.append("\\end{plines}")
    elif rows:
        lines.append("\\begin{expr}")
        for r in rows:
            try:
                lines.append(f"\\eit{{{r.key}}}{{{line_tex(r.text)}}}")
            except ValueError as e:
                raise ValueError(f"line {r.line}: proof {p.label}" + (f" {r.key}" if r.key.startswith("(") else f" \"{r.key}\""
                                                                if r.key else "") +
                                 f": {e}") from None
        lines.append("\\end{expr}")
    lines.append("\\end{proof}")
    return lines


# ---------------------------------------------------------------------------------------------------------
# the vocabulary lines: one row each of a stmt display at their place, keyed by their kind, that latex2qpp reads back

VOCAB_KEY = {"word": "word", "define": "define", "type": "type", "relation": "relation", "context": "given relation",
             "alias": "alias"}
# the type former `pair`: its carrier, pairs (l, m) and top (the order and the sum are those of the language)
PAIR_TEX = "(\\Q_{\\ge0}\\times\\N_{\\ge1})\\cup\\{\\top\\}"
SIG = re.compile(r"([a-z][A-Za-z0-9]*)\((.*)\)\s*:\s*(\S.*)")
TYPE_LHS = re.compile(r"([A-Z][A-Za-z0-9]*)(?:\((.*)\))?")
CURRIED = re.compile(r"([a-z][A-Za-z0-9]*)\(([^()]*)\)\(([^()]*)\)(?:_\(([^()]*)\))?\s*:=\s*(\S.*)")


def vocab_tree(raw):
    """the meaning of a vocabulary line as Q++ trees, which its LaTeX must read back to: a set word (name, set), a
    typed word (name, declarations of its arguments, result type), a define, a type row (name, parameters, type or
    "pair"), a relation (pattern, clauses), a context (name, declarations), an alias (name, word)"""
    head, _, rest = raw.strip().partition(" ")
    rest = rest.strip()
    if head == "word":
        name, _, meaning = rest.partition(":=")
        sig = SIG.fullmatch(name.strip())
        if sig:
            return ("word", sig.group(1), T.parse_qpp_item(sig.group(2)), T.parse_qpp(sig.group(3)))
        return ("word", name.strip(), T.parse_qpp(meaning.strip()))
    if head == "define":
        m = CURRIED.fullmatch(rest)
        if m:  # the body of a typed word at a point: f(K, K')(x, y) := t, or at a coordinate, f(n, N)(u)_(j) := t
            out = ("define", m.group(1), T.parse_qpp_list(m.group(2)), T.parse_qpp_list(m.group(3)),
                   T.parse_qpp(m.group(5)))
            return out + (T.parse_qpp(m.group(4)),) if m.group(4) else out
        return ("define", T.parse_qpp_item(rest))
    if head == "type":
        lhs, _, val = rest.partition(":=")
        m = TYPE_LHS.fullmatch(lhs.strip())
        params = tuple(q.strip() for q in m.group(2).split(",")) if m.group(2) else ()
        val = val.strip()
        if val.startswith("{") and val.endswith("}"):
            return ("type", m.group(1), params, bundle_tree(val[1:-1]))
        return ("type", m.group(1), params, "pair" if val == "pair" else T.parse_qpp("(" + val + ")"))
    if head == "relation":
        pat, _, body = rest.partition(":=")
        return ("relation", T.parse_qpp_item(pat.strip()), T.parse_qpp_item(body.strip()))
    if head == "context":
        m = re.fullmatch(r"([a-z][A-Za-z0-9]*)\((.*)\)", rest)
        return ("context", m.group(1), T.parse_qpp_item(m.group(2)))
    if head == "alias":
        name, _, w = rest.partition(":=")
        return ("alias", name.strip(), " ".join(w.split()))
    raise ValueError(f"not a vocabulary line: {raw!r}")


def bundle_tree(body):
    """the tree of the body of a bundle {P, N in X, op in Y}: ('bundle', ((names, type), ...))"""
    ctx = T.parse_qpp_item(body + " : 0 = 0")
    if len(ctx) != 1 or ctx[0][0] != "ctx":
        raise ValueError(f"a bundle is {{x, y in X, z in Y, ...}}: {body!r}")
    out = []
    for c in (ctx[0][1][1] if ctx[0][1][0] == "and" else (ctx[0][1],)):
        if c[0] != "decl":
            raise ValueError(f"a bundle is {{x, y in X, z in Y, ...}}, declarations only: {body!r}")
        out.append((tuple(v[1] for v in c[1]), c[2]))
    return ("bundle", tuple(out))


def type_tex(t):
    """the LaTeX of a type: a named type \\mathrm{Loss}(n), a set \\Q_{\\ge0}, a power (X)^{n}, the sets of points
    \\mathcal{P}(X), a function type X\\to Y"""
    k = t[0]
    if k == "paren":
        return type_tex(t[1])
    if k == "bundle":
        # {P,N\in X,\ op\in Y}: the parts of a bundle
        return "\\{" + ",\\ ".join(",".join(T.to_tex(("var", n)) for n in ns) + "\\in " + type_tex(ty)
                                     for ns, ty in t[1]) + "\\}"
    if k == "fun":
        a = type_tex(t[1])
        return f"{'(' + a + ')' if t[1][0] == 'fun' else a}\\to {type_tex(t[2])}"
    if k == "app" and t[1] == ("var", "set") and len(t[2]) == 1:
        return f"\\mathcal{{P}}({type_tex(t[2][0])})"
    if k == "pow":
        b = type_tex(t[1])
        return f"{b if t[1][0] == 'var' else '(' + b + ')'}^{{{T.to_tex(t[2])}}}"
    if k == "app" and t[1][0] == "var" and t[3] == "call":
        return f"\\mathrm{{{t[1][1]}}}({','.join(T.to_tex(a) for a in t[2])})"
    if k == "var":
        return f"\\mathrm{{{t[1]}}}"
    if k == "set":
        return T.to_tex(t)
    raise ValueError(f"no LaTeX for the type {T.to_qpp(t)}")


def vocab_tex(raw):
    """(key, LaTeX) of the row of a vocabulary line"""
    v = vocab_tree(raw)
    k = v[0]
    if k == "word" and len(v) == 3:
        return "word", f"\\text{{{v[1].replace('_', ' ')}}}:={T.to_tex(v[2])}"
    if k == "word":
        return "word", f"\\mathrm{{{v[1]}}}({T.stmt_print(v[2], T.to_tex)})\\in {type_tex(v[3])}"
    if k == "define" and len(v) in (5, 6):
        args = lambda xs: ",".join(T.to_tex(x) for x in xs)
        coord = f"_{{{T.to_tex(v[5])}}}" if len(v) == 6 else ""
        return "define", f"\\mathrm{{{v[1]}}}({args(v[2])})({args(v[3])}){coord}:={T.to_tex(v[4])}"
    if k == "define":
        return "define", T.stmt_print(v[1], T.to_tex)
    if k == "type":
        lhs = f"\\mathrm{{{v[1]}}}" + (f"({','.join(v[2])})" if v[2] else "")
        return "type", f"{lhs}:={PAIR_TEX if v[3] == 'pair' else type_tex(v[3])}"
    if k == "relation":
        return "relation", f"{T.stmt_print(v[1], T.to_tex)}:\\iff {T.stmt_print(v[2], T.to_tex)}"
    if k == "context":
        return "given relation", f"\\mathrm{{{v[1]}}}({T.stmt_print(v[2], T.to_tex)})"
    return "alias", f"\\mathrm{{{v[1]}}}:={word_tex(v[2])}"


def flat_idx(t):
    """t with each index of an index merged into one application, x_(k)_(i) as x_(k, i): the LaTeX prints both as
    x_{ki} and reads that as one subscript of two indices; in a typed row the kernel reads only the first (the
    coordinate of a member or of a row) and refuses the second, so the two trees mean the same there. A name with a
    numeral at its end is the name with the numeral below, N0 as N_0 and u0_(j) as u_(0, j), as they print. The word
    binom(n, k) prints as \\tbinom{n}{k}, which reads back as choose(n, k): the two are one word"""
    if t == ("var", "choose"):
        return ("var", "binom")
    if isinstance(t, list):
        return [flat_idx(a) for a in t]
    if isinstance(t, str):
        # each part of a bundle name too: St.N0 as St.N_0
        return ".".join(f"{nb[0]}_{nb[1]}" if nb else c for c in t.split(".") for nb in [T.numbered(c)])
    if not isinstance(t, tuple):
        return t
    t = tuple(flat_idx(a) for a in t)
    if len(t) == 4 and t[0] == "app" and t[3] == "idx" and isinstance(t[1], tuple) and len(t[1]) == 4 \
            and t[1][0] == "app" and t[1][3] == "idx":
        return ("app", t[1][1], t[1][2] + t[2], "idx")
    if len(t) == 4 and t[0] == "app" and t[3] == "idx" and t[1][:1] == ("var",) and isinstance(t[1][1], str):
        m = re.fullmatch(r"([A-Za-z]+)_(\d+)", t[1][1])
        if m:
            return ("app", ("var", m.group(1)), (("num", m.group(2)),) + tuple(t[2]), "idx")
    return t


def vocab_display(lines, maps, textrels=()):
    """the stmt display of consecutive vocabulary lines; each row is read back (latex2qpp.vocab_row) and must give
    the line's meaning (vocab_tree), else ValueError: the LaTeX says what the line says. maps: the names of the type
    rows of functions, updated by the type rows of these lines; textrels: the patterns of the relation rows of the
    document (_ w1 _ w2 _), by which a relation that is a clause of another one is read back, as latex2qpp reads it"""
    from . import latex2qpp as L
    out = ["\\begin{stmt}"]
    for line, raw in lines:
        key, tex = vocab_tex(raw)
        want = vocab_tree(raw)
        if want[0] == "type" and want[3] != "pair" and want[3][0] == "fun":
            maps.add(want[1])
        known = T.VOCAB.get("#textrel")
        T.VOCAB["#textrel"] = list(known or []) + [t for t in textrels if t not in (known or [])]
        try:
            got = L.vocab_row(key, tex, maps)
        except (T.Hole, ValueError) as e:
            got = f"unread ({e})"
        finally:
            if known is None:
                del T.VOCAB["#textrel"]
            else:
                T.VOCAB["#textrel"] = known
        if flat_idx(got) != flat_idx(want):
            raise ValueError(f"line {line}: the vocabulary line {raw!r} prints as \\sit{{{key}}}{{{tex}}}, which "
                             f"reads back as {got!r}")
        out.append(f"\\sit{{{key}}}{{{tex}}}")
    out.append("\\end{stmt}")
    return out


BODY = "% qpp: body"


def top_arrow(t):
    """a Lean type with an arrow outside parentheses: a function type"""
    depth = 0
    for i, ch in enumerate(t):
        depth += {"(": 1, ")": -1}.get(ch, 0)
        if depth == 0 and (t.startswith("->", i) or ch == "\u2192"):
            return True
    return False


def generate(doc, bib_path=None, source="", frame=None, full=False):
    """(tex, bib) of a Doc; with frame (the text of the frame file), the body goes in place of its line
    `% qpp: body`; full: the printing that keeps the rows and lines that only the checks read"""
    bib = bib_entries(bib_path)
    paper = bool(getattr(doc, "article", False)) and not full
    X.PAPER[0] = paper
    names = paper_names if paper else (lambda line: line)
    out = [f"% generated by qpp/qpp2latex.py from {source or doc.path}; do not edit", ""]
    # the contexts (relations that are parameters): their applications are clauses, here and for latex2qpp
    rels = [raw.split(None, 1)[1].split("(")[0].strip() for _, raw in getattr(doc, "vocab", [])
            if raw.startswith("context ")]
    if rels:
        T.CLAUSE_APPS.update(rels)
        out[1:1] = [f"% qpp: relations {' '.join(rels)}"]
    # the relation rows (x w y := ...): their pattern, which latex2qpp reads their clauses by (printed as prose)
    pats = []
    for _, raw in getattr(doc, "vocab", []):
        if raw.startswith("relation "):
            pat = T.parse_qpp_item(raw[len("relation "):].partition(":=")[0].strip())
            if len(pat) == 1 and pat[0][0] == "textrel":
                words = " _ ".join(pat[0][1])
                pats.append(f"% qpp: textrel _ {words} _")
    out[1:1] = pats
    # the type rows of functions (lean A -> B): their objects are applied, K(w), which latex2qpp reads by them
    maps = [m.group(1) for _, raw in getattr(doc, "vocab", [])
            for m in [re.fullmatch(r"type\s+([A-Z][A-Za-z0-9]*)(?:\([^)]*\))?\s*:=\s*(?:lean\s+)?(.*)", raw.strip())]
            if m and top_arrow(m.group(2))]
    if maps:
        out[1:1] = [f"% qpp: maps {' '.join(maps)}"]
    # the alias lines (alias Chart := fact:pieces(1)): in a transcoded proof an alias reads as the word it names
    X.ALIASES.clear()
    for _, raw in getattr(doc, "vocab", []):
        m = re.fullmatch(r"alias\s+([A-Z][A-Za-z0-9]*)\s*:=\s*(\S.*?)\s*", raw.strip())
        if m:
            X.ALIASES[m.group(1)] = m.group(2)
    # the statement rows: in a transcoded proof a step that applies one at values names the facts of its hypotheses
    X.ROWS.clear()
    for b in doc.blocks:
        if isinstance(b, S.Item):
            for r in b.stmt_rows():
                X.ROWS[b.label + r.key] = r.text
    cited = {}
    shown = frozenset() if full else cited_cores(doc, X.ALIASES)
    pending = sorted(getattr(doc, "vocab", []))
    seen_maps = set()
    joined = {}
    for b in doc.blocks + [None]:
        # the vocabulary lines before this block, at their place: one display
        here = [v for v in pending if b is None or v[0] < b.line]
        if here:
            out += [names(x) for x in vocab_display(here, seen_maps, [tuple(p.split()[3:]) for p in pats])] + [""]
            pending = pending[len(here):]
        if b is None:
            break
        if isinstance(b, S.Prose):
            out += b.lines + [""]
        elif isinstance(b, S.Section):
            cmd = "section" if b.level == 1 else "subsection"
            out += [f"\\{cmd}{{{b.title}}}\\label{{{b.label}}}", ""]
        elif isinstance(b, S.Item):
            T.JOINED = joined[b.label] = T.joined_names([r.text for r in b.rows])
            out += [names(x) for x in item_tex(b, bib, full, shown)] + [""]
            T.JOINED = frozenset()
            if b.kind == "cit" and b.row("doi"):
                key, entry = cite_of(b, bib)
                cited[key] = entry
        elif isinstance(b, S.Proof):
            T.JOINED = joined.get(b.label, frozenset())
            pt = [names(x) for x in proof_tex(b, full, paper)]
            T.JOINED = frozenset()
            out += pt + [""] if pt else []
    X.PAPER[0] = False
    tex = "\n".join(out).rstrip() + "\n"
    if frame is not None and doc.parts:
        tex = fill(frame, out)
    elif frame is not None:
        head, sep, tail = frame.partition(BODY + "\n")
        if not sep:
            raise ValueError(f"the frame has no line {BODY!r}")
        tex = out[0] + "\n" + head + "\n".join(out[2:]).rstrip() + "\n" + tail
    bib_out = f"% generated by qpp/qpp2latex.py from {source or doc.path}; do not edit\n\n" + \
        "\n\n".join(e for _k, e in sorted(bibliography(tex, bib_path, cited).items())) + "\n"
    return tex, bib_out


def fill(skeleton, out):
    """the text of a skeleton, each line `% qpp: include sec:x` replaced by its part of the printed body out (the lines
    after the prose line `% qpp: part K` of the K-th of them); the comments that head the body come first"""
    head, parts = [], []
    for line in out:
        if line.startswith(S.PART + " "):
            parts.append([])
        elif parts:
            parts[-1].append(line)
        elif line:
            head.append(line)
    lines = skeleton.split("\n")
    places = sum(1 for line in lines if S.PLACE.match(line))
    if places != len(parts):
        raise ValueError(f"the skeleton has {places} lines `% qpp: include` and the body {len(parts)} parts")
    parts.reverse()
    text = ["\n".join(parts.pop()).strip("\n") if S.PLACE.match(line) else line for line in lines]
    return "\n".join(head + text).rstrip() + "\n"


def bibliography(tex, bib_path, cited=None):
    """{key: entry} of every key that tex cites: the entry of a `cit` item (cited, made by generate) or of the store"""
    store, cited = bib_keys(bib_path), cited or {}
    return {k: cited.get(k) or store[k] for k in cited_keys(tex) if k in cited or k in store}


def missing_keys(tex, bib):
    """the keys that tex cites and that the bibliography bib (the text generate writes) has no entry for"""
    return sorted(cited_keys(tex) - {m.group(1) for m in ENTRY.finditer(bib)})


def main(argv):
    if not argv:
        print(__doc__)
        return 2
    src = Path(argv[0])
    doc = S.read_file(src)
    out = Path(argv[argv.index("-o") + 1]) if "-o" in argv else \
        src.with_name(f"{doc.paper}.tex") if doc.parts else src.with_suffix(".tex")
    if out.resolve() == src.resolve():
        print(f"qpp2latex: {src}: the output would overwrite the source")
        return 1
    bib_out = Path(argv[argv.index("--bib") + 1]) if "--bib" in argv else out.with_suffix(".bib")
    bib_path = (src.parent / doc.bib) if doc.bib else None
    frame = (src.parent / doc.frame).read_text(encoding="utf-8") if doc.frame else None
    try:
        tex, bib = generate(doc, bib_path, source=str(src), frame=frame)
    except ValueError as e:
        print(f"qpp2latex: {src}: {e}")
        return 1
    missing = missing_keys(tex, bib)
    if missing:
        store = bib_path or "the bibliography (no `bib` line)"
        print(f"qpp2latex: {src}: {store} has no entry for the cited keys {', '.join(missing)}")
        return 1
    if doc.frame:
        # a paper: every cited DOI must have its entry in the store
        known = bib_entries(bib_path)
        missing = [it.label for it in doc.items() if it.kind == "cit" and it.row("doi")
                   and it.row("doi").text.lower() not in known]
        if missing:
            print(f"qpp2latex: {src}: no entry of {bib_path} has the DOI of {', '.join(missing)}")
            return 1
    out.write_text(tex, encoding="utf-8")
    if "--full" in argv:
        full = Path(argv[argv.index("--full") + 1])
        full.write_text(generate(doc, bib_path, source=str(src), frame=frame, full=True)[0], encoding="utf-8")
        print(f"qpp2latex: {src} -> {full} (full)")
    bib_out.write_text(bib, encoding="ascii")
    print(f"qpp2latex: {src} -> {out}, {bib_out}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
