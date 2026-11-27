"""status: the status page of a paper, from its LaTeX, the label map of its Lean library (qpp/leanrefs.py) and its
cited-fact hypotheses (the `structure ... : Prop` of the library). It replaces a dependency graph: per numbered
label of the LaTeX, the declarations that state it (with their items), whether it is formalized, and, apart, the
external cited leaves, each with the hypothesis structure or the Lean theorem that stands for it.

A label is
  formalized       a theorem or lemma of the library is tagged with it (the items it covers are listed);
  defined          only definitions (def, abbrev, structure, inductive, instance) are tagged with it;
  cited            a fact (fact:...): CITED, with its Lean side: a hypothesis structure (never an axiom), a theorem
                   (Mathlib or proved), or none;
  not formalized   no declaration is tagged with it.
The match check (qpp2lean --match) is a separate gate: it compiles the stmt lines and checks that the tagged
declaration proves them.

A declaration tagged with a marker (step ...) formalizes a line of a proof, not the statement: it is counted in the
column "proof steps", not in "declarations", and a label with nothing else is "proof steps only".

The column "compiled" counts the match examples of the label: its statement (or each of its items) compiles to Lean
(latex2qpp, qpp2lean) and a tagged declaration is to prove it; whether the proof goes through is the match check in
CI (.github/scripts/check_match.sh), not this page. "2 (1 without given clauses)": one of the examples leaves out
clauses of the given with a hole (qpp2lean drops them when no conclusion uses a name they mention), so it states
more than the paper; the match example's docstring lists them. "1 (core only)": the example states a core item of
the result (key core, core0, core 1: it stands alone, without the given), not the result's statement, so the match
covers the core only; "3 (1 core only)": one of three is such an example.

The table of external cited leaves checks each structure registered as a cited fact (leanrefs.registers_fact)
against the LaTeX: a fact:x tag needs a fact environment labelled fact:x that cites a reference, a tab:facts tag
the name of a cited row of the table of facts in the docstring (column "registered by"); the page lists the
structures that fail. The registration stays a docstring tag; a person checks once that the structure says what
the cited paper says.

The page lives in the paper's folder, PAPER/qpp/status.md, and its writer regenerates it with the paper; --check
compares the page with a file and fails when the file is stale (CI).

Usage: python3 -m qpp.status PAPER [-o OUT.md | --check FILE.md]     (the LaTeX of syntax.paper_tex and PAPER/lean;
       from the repository root)
"""
import re
import sys
from pathlib import Path

from qpp import latex2qpp, leanrefs, qpp2lean, syntax

ENVS = ("theorem", "lemma", "proposition", "corollary", "definition", "construction", "example", "remark",
        "problem", "conjecture", "fact")
BEGIN = re.compile(r"\\begin\{(" + "|".join(ENVS) + r")\}")
# the page is ASCII: the Unicode of Lean docstrings in their usual spelling
ASCII = {"\u2211": "sum", "\u220f": "prod", "\u2264": "<=", "\u2265": ">=", "\u2260": "!=", "\u2192": "->",
         "\u2194": "<->", "\u2200": "forall", "\u2203": "exists", "\u2208": "in", "\u2227": "and", "\u2228": "or",
         "\u00ac": "not", "\u2218": "o", "\u22c5": "*", "\u00b7": "*", "\u00d7": "x", "\u2016": "||",
         "\u2026": "...", "\u2014": "--", "\u2013": "-", "\u2019": "'", "\u211a": "Q", "\u2124": "Z",
         "\u2115": "N", "\u211d": "R"}
PROP_STRUCT = re.compile(r"/--((?:(?!-/).)*)-/\s*structure\s+([^\s(:{\[]+)[^\n]*?:\s*Prop\s+where", re.S)


def results(tex):
    """[(label, environment)] of the numbered results of a LaTeX source, in order"""
    out = []
    lines = tex.split("\n")
    for i, line in enumerate(lines):
        code = re.sub(r"(?<!\\)%.*", "", line)
        m = BEGIN.search(code)
        if not m:
            continue
        for j in range(i, min(i + 8, len(lines))):
            lab = re.search(r"\\label\{([^}]*)\}", lines[j][m.end():] if j == i else lines[j])
            if lab:
                out.append((lab.group(1), m.group(1)))
                break
            if j > i and re.search(r"\\end\{" + m.group(1) + r"\}", lines[j]):
                break
    return out


def hypotheses(lean_root):
    """[(structure name, file, first sentence of its docstring, tags, docstring)]: the cited-fact hypotheses of a
    library"""
    out = []
    for f in sorted(Path(lean_root).rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        for m in PROP_STRUCT.finditer(f.read_text(encoding="utf-8")):
            full = doc = " ".join(m.group(1).split())
            tags = [lab for _, lab, _ in leanrefs.read_tags(doc)]
            doc = re.sub(r"^(\[[^\]]*\]\s*(\([^()]*\)\s*)*)+", "", doc)
            first = re.split(r"(?<=\.)\s(?=[A-Z`])", doc.replace("**", ""), maxsplit=1)[0]
            first = first if len(first) <= 160 else first[:157].rstrip() + "..."
            first = "".join(ASCII.get(c, c if ord(c) < 128 else "?") for c in first)
            out.append((m.group(2), str(f.relative_to(lean_root)), first, tags, full))
    return out


FACT_BLOCK = re.compile(r"\\begin\{fact\}(.*?)\\end\{fact\}", re.S)


def fact_sources(tex):
    """({label of a fact environment: whether it cites a reference}, {name in the first column of the table of facts
    (header name & fact & reference): whether its row cites a reference}) of the LaTeX"""
    src = latex2qpp.syn.strip_comments(tex)
    envs, rows = {}, {}
    for m in FACT_BLOCK.finditer(src):
        lab = re.search(r"\\label\{([^}]*)\}", m.group(1))
        if lab:
            envs[lab.group(1)] = "\\cite" in m.group(1)
    for h in latex2qpp.syn.FACTS_HEADER.finditer(src):
        end = src.find("\\end{tabular}", h.end())
        for row in re.split(r"\\\\", src[h.end():end if end >= 0 else len(src)]):
            row = re.sub(r"\\hline", "", row).strip()
            if "&" not in row:
                continue
            bare = re.sub(r"\\\(.*?\\\)|\\[A-Za-z]+(\{[^{}]*\})?", " ", row.split("&", 1)[0])
            for w in re.findall(r"(?<![A-Za-z\\])[A-Z][A-Za-z0-9]*(?![A-Za-z0-9])", bare):
                rows[w] = rows.get(w, False) or "\\cite" in row
    return envs, rows


def registration(tags, doc, envs, rows):
    """(text, ok): how the LaTeX backs a structure registered as a cited fact (leanrefs.registers_fact). A tag
    fact:x needs a fact environment labelled fact:x that cites a reference; the tag tab:facts needs the name of a
    row of the table of facts, a row that cites a reference, in the docstring. ("-", True) for a structure that is
    not registered"""
    out, ok = [], True
    for lab in tags:
        if lab.startswith("fact:"):
            if lab not in envs:
                out.append(f"{lab}: no fact environment")
                ok = False
            elif not envs[lab]:
                out.append(f"{lab}: no citation")
                ok = False
            else:
                out.append(lab)
        elif lab == "tab:facts":
            named = [w for w in rows if re.search(r"(?<![A-Za-z0-9])" + re.escape(w) + r"(?![A-Za-z0-9])", doc)]
            if not named:
                out.append("tab:facts: names no row")
                ok = False
            elif not any(rows[w] for w in named):
                out.append(f"tab:facts row {', '.join(named)}: no citation")
                ok = False
            else:
                out.append(f"tab:facts row {', '.join(w for w in named if rows[w])}")
    return ("; ".join(out) or "-"), ok


def tex_name(paper):
    """the path, from the root, of the LaTeX of the paper that the checks read (syntax.paper_tex)"""
    return syntax.paper_tex(paper).relative_to(syntax.ROOT).as_posix()


def compiled(paper, tex, lean):
    """{label: number of match examples}: the statements, or items, of the label that compile to Lean and that a
    declaration tagged with the label is to prove"""
    text, _report = latex2qpp.convert(tex, paper, tex_name(paper))
    _lean, spans, _skipped = qpp2lean.generate_match(text, leanrefs.label_map(lean, kernel=False), [], None,
                                                     leanrefs.cited_premises(lean))
    out = {}
    for tag, _a, _b in spans:
        lab = tag.split("(", 1)[0]
        out[lab] = out.get(lab, 0) + 1
    for tag in qpp2lean.LAST_DROPPED:
        lab = tag.split("(", 1)[0]
        DROPPED[lab] = DROPPED.get(lab, 0) + 1
    for tag in qpp2lean.LAST_CORE:
        lab = tag.split("(", 1)[0]
        CORE[lab] = CORE.get(lab, 0) + 1
    return out


def statements(paper, tex):
    """[(label, statement items, compiled, Lean)]: per result with statement items (latex2qpp.counted, the counting
    convention), how many are compiled (formal and same), and whether qpp2lean states it in Lean, which of its items,
    or the reason it does not (the rest of the full compilation, listed by reason)"""
    text, report = latex2qpp.convert(tex, paper, tex_name(paper))
    _lean, _made, skipped = qpp2lean.generate(text)
    stated = {}
    for tag, _a, _b in qpp2lean.LAST_SPANS.get("stated", []):
        lab, _, item = tag.partition("(")
        stated.setdefault(lab, []).append("(" + item if item else "")
    why = dict(skipped)
    rows, seen = [], {}
    for it in latex2qpp.counted(report):
        n, c = seen.get(it["label"], (0, 0))
        seen[it["label"]] = (n + 1, c + (it["formal"] and it["same"]))
    for lab, (n, c) in seen.items():
        if lab in stated and "" in stated[lab]:
            lean = "stated"
        elif lab in stated:
            lean = "items " + " ".join(stated[lab]) + " stated"
        else:
            lean = why.get(lab, "-")
        lean = " ".join(lean.split()).replace("|", "/")
        lean = "".join(ASCII.get(ch, ch if ord(ch) < 128 else "?") for ch in lean)
        rows.append((lab, n, c, lean if len(lean) <= 150 else lean[:147].rstrip() + "..."))
    return rows


DROPPED = {}  # label -> the match examples of the label that leave out a clause of the given with a hole
CORE = {}  # label -> the match examples of the label that state a core item, not the statement


def compiled_cell(label, made):
    """the column compiled: the match examples, with how many state only a core item and how many leave out given
    clauses"""
    n = made.get(label)
    if not n:
        return "-"
    notes = []
    if CORE.get(label):
        notes.append("core only" if CORE[label] == n else f"{CORE[label]} core only")
    if DROPPED.get(label):
        notes.append(f"{DROPPED[label]} without given clauses")
    return f"{n} ({'; '.join(notes)})" if notes else str(n)


def kernel_line(kernel):
    if not kernel:
        return ""
    n = sum(len(v) for v in kernel.values())
    return (f" Rows proved in the kernel of Q++ (generated by qpp/kernel.py, so no match to check): {n} "
            f"({len(kernel)} label{'s' if len(kernel) > 1 else ''}).")


def kernel_cell(cell, items):
    """the column compiled, with the rows proved in the kernel of Q++ ("kernel (core)")"""
    if not items:
        return cell
    k = f"kernel {' '.join(items)}"
    return k if cell == "-" else f"{cell}; {k}"


def page(paper, root=Path(".")):
    tex = syntax.paper_tex(paper, root).read_text(encoding="utf-8")
    lean = syntax.paper_dir(paper, root) / "lean"
    refs = leanrefs.label_map(lean, paper)
    steps = leanrefs.label_map(lean, paper, steps=True)
    # the rows proved by the Lean that the kernel backend generates (qpp/kernel.py): covered, with no match to check
    outside = leanrefs.label_map(lean, paper, kernel=False)
    kernel = {lab: sorted({i or "-" for d in ds if d not in outside.get(lab, []) for _, i, k, _ in [d]
                           if k in ("theorem", "lemma")}) for lab, ds in refs.items()}
    kernel = {lab: v for lab, v in kernel.items() if v}
    DROPPED.clear()
    CORE.clear()
    made = compiled(paper, tex, lean)
    hyps = hypotheses(lean)
    res = results(tex)
    props = {name for name, _, _, _, _ in hyps}
    envs, rows_of_facts = fact_sources(tex)
    rows, counts = [], {}
    for label, env in res:
        decls = refs.get(label, [])
        kinds = {k for _, _, k, _ in decls}
        items = sorted({i for _, i, _, _ in decls if i})
        if label.startswith("fact:") or env == "fact":
            hs = sorted({n.split(".")[-1] for n, _, k, _ in decls if k == "structure" and n.split(".")[-1] in props})
            side = ("hypothesis " + ", ".join(hs) if hs else "theorem" if kinds & {"theorem", "lemma"} else
                    "definitions only" if decls else "none")
            status = f"cited ({side})"
        elif kinds & {"theorem", "lemma"}:
            status = "formalized"
        elif decls:
            status = "defined"
        elif steps.get(label):
            status = "proof steps only"
        else:
            status = "not formalized"
        key = status.split(" (")[0]
        counts[key] = counts.get(key, 0) + 1
        names = ", ".join(f"`{n}`" for n in sorted({n for n, _, _, _ in decls})[:4])
        more = len({n for n, _, _, _ in decls}) - 4
        rows.append(f"| `{label}` | {env} | {status} | {len(decls)} | {' '.join(items) or '-'} | "
                    f"{kernel_cell(compiled_cell(label, made), kernel.get(label))} | "
                    f"{len(steps.get(label, [])) or '-'} | "
                    f"{names}{f' and {more} more' if more > 0 else ''} |")
    tagged_elsewhere = sorted(set(refs) - {lab for lab, _ in res})
    out = [f"# Status of {paper}", "",
           f"Generated by `python3 -m qpp.status {paper}` from `{tex_name(paper)}`, the docstring tags of "
           f"`{paper}/lean` (`[{paper}:lem:x]`, read by `qpp/leanrefs.py`) and its `structure ... : Prop` "
           "hypotheses. Do not edit; rerun.", "",
           "| status | labels |", "|---|---|"]
    out += [f"| {k} | {v} |" for k, v in sorted(counts.items())]
    formal = sum(1 for lab, _ in res if lab in made)
    core_only = sum(1 for lab, _ in res if lab in made and CORE.get(lab) == made[lab])
    out += ["", f"{len(res)} numbered labels; {sum(len(v) for v in refs.values())} tagged declarations for "
            f"{len(refs)} labels. Labels with a compiled statement to match: {formal}"
            f"{f' (of which {core_only} by a core item only)' if core_only else ''}; match examples: "
            f"{sum(made.get(lab, 0) for lab, _ in res)}"
            f"{f', of which {sum(DROPPED.values())} without given clauses with a hole' if DROPPED else ''}."
            f"{kernel_line(kernel)}",
            "",
            "## Labels", "",
            "| label | environment | status | declarations | items | compiled | proof steps | names |",
            "|---|---|---|---|---|---|---|---|"]
    out += rows
    st = statements(paper, tex)
    out += ["", "## Statement items (the full compilation)", "",
            "Per result: its statement items (the `\\sit` rows whose key is not origin, classical, reference or names), "
            "how many compile (formal, and the LaTeX printed back reads the same), and its Lean statement (qpp2lean): "
            "stated, the items stated, or the reason it is not. "
            f"{sum(n for _, n, _, _ in st)} statement items, {sum(c for _, _, c, _ in st)} compiled; "
            f"{sum(1 for _, n, c, _ in st if n == c)} of {len(st)} results fully compiled; "
            f"{sum(1 for *_, lean in st if lean == 'stated')} stated in Lean.", "",
            "| label | statement items | compiled | Lean statement |", "|---|---|---|---|"]
    out += [f"| `{lab}` | {n} | {c} | {lean} |" for lab, n, c, lean in st]
    out += ["", "## External cited leaves (hypothesis structures)", "",
            "Every `structure ... : Prop` of the library: a cited fact (with no parameters, and a fact: tag or the "
            "tag of the table of facts in its docstring) is taken as a hypothesis of the match, never an axiom, and "
            "a person checks once that it says what the cited paper says; a structure with no parameters and no "
            "such tag is no hypothesis of the match; the others are predicates of the library.", "",
            "| structure | file | tags | registered by | docstring (first sentence) |", "|---|---|---|---|---|"]
    bad = []
    for name, f, first, tags, doc in hyps:
        reg, ok = registration(tags, doc, envs, rows_of_facts)
        if not ok:
            bad.append(name)
        out.append(f"| `{name}` | `{f}` | {', '.join(tags) or '-'} | {reg} | {first.replace('|', '/')} |")
    if bad:
        out += ["", "Registered as cited facts but not backed by the LaTeX (a fact environment with a citation, or a "
                "cited row of the table of facts named in the docstring): " + ", ".join(f"`{x}`" for x in bad) + "."]
    if tagged_elsewhere:
        out += ["", "Tags that name no numbered label of the LaTeX (equations, tables, sections): "
                + ", ".join(f"`{x}`" for x in tagged_elsewhere) + "."]
    return "\n".join(out) + "\n"


def main(argv):
    text = page(argv[0])
    if "--check" in argv:
        f = Path(argv[argv.index("--check") + 1])
        if not f.exists() or f.read_text(encoding="utf-8") != text:
            print(f"{f} is stale or missing: rerun python3 -m qpp.status {argv[0]} -o {f}")
            return 1
        print(f"{f} is current")
        return 0
    if "-o" in argv:
        Path(argv[argv.index("-o") + 1]).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
