"""Modules of Q++ sources: split a paper into modules, print the graph of the modules.

    python3 -m qpp.modules split PAPER/source/PAPER.qpp NAME=sec:a NAME=sec:b,sec:c ...
        cut the body of a paper source at the headings listed into modules/NAME/NAME.qpp (a heading listed starts
        its module's lines, up to the next heading listed for another module; a module may take several runs) and
        rewrite the source as a manifest of `include` lines; the uses of each module are the modules of its hard
        references. Fails, writing nothing, unless the manifest flattens to the source byte for byte.
    python3 -m qpp.modules graph [-o graph.md] [--dot graph.dot]
        the modules under modules/: labels, uses, and the references each makes into the others; Markdown, and dot
    python3 -m qpp.modules check
        every module: its header, its hard references within the closure of its uses, no cycle; its vocabulary
        (alias, define, relation and word lines) used only in the modules that use it, directly or not; its signs:
        the rows and vocabulary lines with a form of both signs are exactly those that modules/both_signs.toml lists for
        it, and its mark `application: REASON` is the one listed there; a cited rule that the theorems take as a
        hypothesis (doi:, no mathlib:) has no row keyed core or core NAME (its statement is printed), and a key that
        begins with core is one of the core keys (core, core N, coreN, core NAME); then the typed
        coverage: per module, the statement rows and proof lines that are Q++ (no hole ?{...}), and its rows of both
        signs; everything in Q++: no hole ?{...} in a row, a proof line or a vocabulary line, but in an origin row and
        in the stmt row of a cit, no after row, and the source rows (doi, stmt, mathlib) only in a cit; and the
        list of the primitives in qpp/README.md is the generator's
"""

import re
import sys
from pathlib import Path

from . import source as S
from . import texmath as T

try:
    from . import concordance
except ImportError:  # a tree without the concordance
    concordance = None

FORMAT = "-- Q++ 0.2"


def split(text, plan, path="<qpp>"):
    """(manifest, {name: module text}) for a paper text and a plan [(name, [heading labels])]. Every heading listed
    goes to its module, and so do the lines up to the next listed heading of another module; a heading not listed
    stays with the lines before it (a section must be listed). A module whose headings form one run is included
    whole; a module of several runs is included run by run, `include NAME sec:a`, and is cut at those headings.
    Everything before the first listed heading stays in the manifest."""
    lines = text.split("\n")
    if lines[-1] == "":
        lines.pop()
    heads = [(i, t.split()[0], t.split()[1]) for i, t in enumerate(lines) if t.startswith(("section ", "subsection "))]
    owner = {}
    for name, secs in plan:
        for sec in secs:
            if sec in owner:
                raise ValueError(f"{sec} is listed twice")
            owner[sec] = name
    known = {lab for _i, _k, lab in heads}
    for sec in owner:
        if sec not in known:
            raise ValueError(f"no heading {sec}")
    runs = []  # [name, first line, [heading labels with their levels]]
    for i, kind, lab in heads:
        if lab in owner and (not runs or runs[-1][0] != owner[lab]):
            runs.append([owner[lab], i, []])
        elif lab not in owner and kind == "section" and runs:
            raise ValueError(f"the section {lab} is in no module's list")
        if runs:
            runs[-1][2].append((1 if kind == "section" else 2, lab))
    if not runs:
        raise ValueError("no module")
    bounds = [r[1] for r in runs] + [len(lines)]
    chunks, order, nruns = {}, [], {}
    for k, (name, i, _hs) in enumerate(runs):
        chunks.setdefault(name, []).extend(lines[i:bounds[k + 1]])
        nruns[name] = nruns.get(name, 0) + 1
        if name not in order:
            order.append(name)
    head = lines[:bounds[0]]
    # the uses: the modules of the hard references of each chunk
    defined = {}
    for name, chunk in chunks.items():
        for lab in S.labels_of_lines([(0, t) for t in chunk]):
            defined.setdefault(lab, name)
    modules = {}
    for name, chunk in chunks.items():
        uses = sorted({defined[r] for r in S.hard_refs([(0, t) for t in chunk]) if r in defined} - {name},
                      key=order.index)
        header = [FORMAT, f"module {name}"] + ([f"uses {', '.join(uses)}"] if uses else []) + [""]
        modules[name] = "\n".join(header + chunk) + "\n"
    incl = []
    for name, _i, hs in runs:
        if nruns[name] == 1:
            incl.append(f"include {name}")
            continue
        named, level = [], 3
        for lv, lab in hs:  # name the headings that a cut would otherwise end: the first, and any not below it
            if lv <= level:
                named.append(lab)
                level = lv
        incl.append(f"include {name} {', '.join(named)}")
    manifest = "\n".join(head + incl) + "\n"
    return manifest, modules


def write_split(src, plan, root=S.ROOT):
    src = Path(src)
    text = src.read_text(encoding="ascii")
    manifest, modules = split(text, plan, str(src))
    for name, body in modules.items():
        p = S.module_path(name, root)
        if p.exists() and p.read_text(encoding="ascii") != body:
            raise ValueError(f"{p} exists with another text")
    tmp = {}
    for name, body in modules.items():
        p = S.module_path(name, root)
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp[p] = p.exists()
        p.write_text(body, encoding="ascii")
    def undo():
        for p, existed in tmp.items():
            if not existed:
                p.unlink()
                if not any(p.parent.iterdir()):
                    p.parent.rmdir()

    flat, _origin, mods = S.flatten(manifest, str(src), root)
    if flat != text:
        undo()
        raise ValueError("the manifest does not flatten to the source")
    try:
        S.check_modules(mods, root)
    except S.SourceError:
        undo()
        raise
    src.write_text(manifest, encoding="ascii")
    return manifest, modules


def all_modules(root=S.ROOT):
    base = Path(root) / S.MODULES
    return sorted(p.name for p in base.iterdir() if (p / f"{p.name}.qpp").exists()) if base.exists() else []


def in_order(mods):
    """the names of the modules {name: module}, dependencies first, by name among the ready ones (no cycle)"""
    order, done = [], set()
    while len(order) < len(mods):
        ready = sorted(n for n in mods if n not in done and set(mods[n].uses) <= done)
        order.append(ready[0])
        done.add(ready[0])
    return order


def whole(root=S.ROOT):
    """the text of a manifest that includes every module of modules/, dependencies first, with the bibliography
    modules/references.bib (by its absolute path): the module set read as one paper, as the check of the references
    reads it (.github/scripts/check_refs.py)"""
    names = all_modules(root)
    order = in_order(S.check_modules([S.read_module(n, root) for n in names], root))
    bib = (Path(root) / S.MODULES / "references.bib").resolve()
    return "\n".join([FORMAT, "paper modules", f"bib {bib}", ""] + [f"include {n}" for n in order]) + "\n"


def graph(root=S.ROOT):
    """(markdown, dot) of the modules: per module its labels, its uses and its hard references into each other"""
    names = all_modules(root)
    mods = S.check_modules([S.read_module(n, root) for n in names], root)
    defined = {}
    for n, m in mods.items():
        for lab in S.labels_of_lines(m.body):
            defined.setdefault(lab, n)
    order = in_order(mods)
    used_by = {n: sorted(m for m in names if n in mods[m].uses) for n in names}
    md = ["| module | labels | uses | used by | references into other modules | reads (remarks, examples, prose) |",
          "|---|---|---|---|---|---|"]
    dot = ["digraph modules {", "  rankdir=BT;"]
    for n in order:
        m = mods[n]
        into = {}
        for r in sorted(S.hard_refs(m.body)):
            if defined.get(r) not in (None, n):
                into.setdefault(defined[r], []).append(r)
        refs = "; ".join(f"{t}: {', '.join(rs)}" for t, rs in sorted(into.items()))
        allrefs = set().union(*(S.refs_of(t) for _k, t in m.body)) if m.body else set()
        reads = sorted({defined[r] for r in allrefs if defined.get(r) not in (None, n)} - set(into),
                       key=order.index)
        md.append(f"| `{n}` | {len(S.labels_of_lines(m.body))} | {', '.join(m.uses) or '-'} | "
                  f"{', '.join(used_by[n]) or '-'} | {refs or '-'} | {', '.join(reads) or '-'} |")
        for u in m.uses:
            dot.append(f'  "{n}" -> "{u}";')
    dot.append("}")
    return "\n".join(md) + "\n", "\n".join(dot) + "\n"


def vocab_names(doc):
    """{name: (kind, line)} of the vocabulary lines of a source: aliases, defines, words (with a signature or not),
    types, contexts, and relations by their words (`#asymp #on`), as the generator names them (kernel.vocab_key)"""
    from . import kernel as K
    out = {}
    for line, raw in doc.vocab:
        head, name = K.vocab_key(raw)
        if name:
            out[name] = (head, line)
    return out


def use_pattern(w):
    """the regex of a use of a vocabulary name: a word head, or the words of a relation in order"""
    if w.startswith("#"):
        return r".*?".join(re.escape(x) + r"(?![\w'])" for x in w.split())
    return rf"(?<![\w:.']){re.escape(w)}(?![\w:'])"


def typed_lines(doc):
    """(rows, typed rows, proof lines, typed proof lines) of a source: typed is Q++ with no hole ?{...}"""
    rows = [r for it in doc.items() for r in it.stmt_rows() if r.key not in ("given", "origin", "names")]
    lines = [ln for pr in doc.proofs().values() for ln in pr.lines]
    return (rows, [r for r in rows if "?{" not in r.text], lines, [ln for ln in lines if "?{" not in ln.text])


def check_typed(names, root=S.ROOT):
    """everything in Q++: no hole ?{...} in a row, a proof line or a vocabulary line, but in an origin row and in the stmt row of a cit (text about the
    sources); no after row (prose is a -- line); the source rows doi, stmt and mathlib only in a cit. The rows that
    the generator does not prove fail its run (qpp/modlean.py)"""
    for n in names:
        doc = S.read_file(S.module_path(n, root))
        for line, raw in doc.vocab:
            if "?{" in raw:
                raise S.SourceError(doc.path, line, "a hole ?{...} in a vocabulary line: everything is in Q++")
        for it in doc.items():
            for r in it.rows:
                if r.key == "after":
                    raise S.SourceError(doc.path, r.line, f"{it.label}: an after row: prose is a -- line")
                if r.key in ("doi", "stmt", "mathlib") and it.kind != "cit":
                    raise S.SourceError(doc.path, r.line, f"{it.label}: a row {r.key} outside a cit: a cited "
                                        "statement is a cit, with typed rows")
                if "?{" in r.text and r.key not in ("origin", "stmt"):
                    raise S.SourceError(doc.path, r.line, f"{it.label}: a hole ?{{...}} in the row {r.key}: "
                                        "everything is in Q++ (text only in an origin row and in the stmt row of "
                                        "a cit)")
        for lab, p in doc.proofs().items():
            for ln in p.lines:
                if "?{" in ln.text or "?{" in ln.key:
                    raise S.SourceError(doc.path, ln.line, f"proof {lab}: a hole ?{{...}} in a proof line: "
                                        "everything is in Q++")


def check_primitives(root=S.ROOT):
    """the list of the primitives in qpp/README.md is the generator's (PRIMITIVES in qpp/kernel.py): the list is
    closed, and a change of it is made in both places at once"""
    from . import kernel as K
    readme = (root / "qpp" / "README.md").read_text(encoding="utf-8")
    m = re.search(r"<!-- primitives: [^\n]*-->\n(.*?)<!-- /primitives -->", readme, re.S)
    if m is None or m.group(1) != K.primitives_markdown():
        raise S.SourceError(root / "qpp" / "README.md", 0, "the list of the primitives differs from PRIMITIVES in "
                            "qpp/kernel.py (python3 -m qpp.kernel --primitives prints it)")
    # the Lean constants of each primitive (the audit of the generated statements): exactly the rows of the list,
    # so that no constant is approved without a primitive
    import tomllib
    path = root / "qpp" / "primitives_lean.toml"
    rows = [r["qpp"] for r in tomllib.loads(path.read_text(encoding="utf-8"))["row"]]
    prims = [q for _, rs in K.PRIMITIVES for q, _ in rs]
    if sorted(rows) != sorted(prims):
        extra = [r for r in rows if r not in prims] + [r for r in rows if rows.count(r) > 1]
        missing = [q for q in prims if q not in rows]
        raise S.SourceError(path, 0, "the rows differ from PRIMITIVES in qpp/kernel.py: "
                            + "; ".join(([f"not a primitive: {', '.join(extra)}"] if extra else [])
                                        + ([f"no row: {', '.join(missing)}"] if missing else [])))


def check_signs(names, root=S.ROOT):
    """positivity: per module, in the order of the uses, its rows and vocabulary lines with a form of both
    signs, by the generator's own classifier (kernel.both_rows, through the vocabulary names of both signs of the
    modules it uses), are exactly the ones that modules/both_signs.toml lists for it, a list that may shrink and never
    grow; a module with the mark `application: REASON` is listed with the same reason under [applications]. Returns {module: (number of its rows and lines of both signs, its mark)}"""
    from . import kernel as K
    from . import texmath as T
    listed, apps = K.both_table(root)
    table = Path(root) / S.MODULES / "both_signs.toml"
    mods = {n: S.read_module(n, root) for n in names}
    docs = {n: S.read_file(S.module_path(n, root)) for n in names}
    for n in sorted(set(listed) | set(apps)):
        if n not in mods:
            raise S.SourceError(table, 0, f"{n} is no module")

    def closure(m):
        out, todo = set(), list(mods[m].uses)
        while todo:
            u = todo.pop()
            if u not in out:
                out.add(u)
                todo.extend(mods[u].uses)
        return out

    names_of, out = {}, {}
    try:
        for n in in_order(mods):
            seen = closure(n)
            known = set().union(*(names_of[u] for u in seen))
            # the contexts in scope, so that a row that applies one is read (as the generator reads it)
            T.CLAUSE_APPS.clear()
            T.CLAUSE_APPS.update(nm for u in seen | {n} for _, raw in docs[u].vocab
                                 for h, nm in [K.vocab_key(raw)] if h == "context")
            for it in docs[n].items():
                for r in it.stmt_rows():
                    if r.key not in ("origin", "names") and "?{" not in r.text:
                        try:
                            T.parse_qpp_item(r.text)
                        except ValueError as e:
                            raise S.SourceError(docs[n].path, r.line, f"{it.label} {r.key}: a typed row that is not "
                                                f"Q++, so its signs cannot be read ({e}); write it in Q++ or as a hole")
            own, found = K.both_rows(docs[n], known)
            names_of[n] = set(own)
            ids = sorted(id_ for _, id_, _ in found)
            mark = mods[n].application
            if mark:
                if apps.get(n) != mark:
                    raise S.SourceError(mods[n].path, 3, f"the mark of {n} is not the one under [applications] in "
                                        f"{table.relative_to(root)} ({apps.get(n, 'none')}): each mark needs the "
                                        "user's approval, and is listed there")
                if n in listed:
                    raise S.SourceError(table, 0, f"{n} carries the mark of an application: it is listed under "
                                        "[applications], not under [both_signs]")
            else:
                if n in apps:
                    raise S.SourceError(table, 0, f"{n} is listed under [applications] but carries no mark "
                                        "`application: REASON`")
                want = sorted(listed.get(n, []))
                if ids != want:
                    extra, gone = list(ids), list(want)
                    for i in want:
                        if i in extra:
                            extra.remove(i)
                            gone.remove(i)
                    where = {id_: line for line, id_, _ in found}
                    msg = []
                    if extra:
                        msg.append(f"rows or lines with a form of both signs that {table.relative_to(root)} does not "
                                   f"list for {n}: " + "; ".join(f"{i} (line {where[i]}: "
                                                                 f"{', '.join(dict.fromkeys(next(f for _, j, f in found if j == i)))})"
                                                                 for i in extra) +
                                   " (write them with the positive forms; the list may shrink, never grow)")
                    if gone:
                        msg.append(f"listed for {n} but positive now, or gone: {', '.join(gone)} (remove them from "
                                   "the list)")
                    raise S.SourceError(docs[n].path, where[extra[0]] if extra else 0, "; ".join(msg))
            out[n] = (len(found), mark)
    finally:
        T.CLAUSE_APPS.clear()
    return out


def check_cited(names, root=S.ROOT):
    """every key that begins with core is a core key (texmath.is_core: core, core N, coreN, core NAME), so that no
    misspelt core key (core 1a, core tie 2, core_tie) is silently a printed row read under the given; and a cited rule
    that the theorems take as a hypothesis (a cit with doi: and no mathlib:) prints its statement: no row of it is
    one that only the checks read (texmath.checks_only: core, core NAME). A cit with mathlib: is proved from
    Mathlib, no theorem takes it as a hypothesis, and its sentence states it: a core row is allowed there"""
    for n in names:
        doc = S.read_file(S.module_path(n, root))
        lines = [(r, it.label) for it in doc.items() for r in it.rows]
        lines += [(r, f"proof {lab}") for lab, p in doc.proofs().items() for r in p.lines]
        for r, where in lines:
            if r.key.startswith("core") and not T.is_core(r.key):
                raise S.SourceError(doc.path, r.line, f"{where}: the key {r.key!r} begins with core but is not a core "
                                    "key: core, core N, coreN or core NAME (qpp/README.md, Row keys)")
        for it in doc.items():
            if it.kind != "cit" or it.row("doi") is None or it.row("mathlib") is not None:
                continue
            for r in it.stmt_rows():
                if T.checks_only(r.key):
                    raise S.SourceError(doc.path, r.line, f"{it.label}: the statement of a cited rule that the "
                                        f"theorems take as a hypothesis is printed: key it (1), not {r.key} (a row "
                                        "keyed core or core NAME is read by the checks only)")


def check_vocabulary(names, root=S.ROOT):
    """every use of a vocabulary name is in its owner or in a module that uses the owner, directly or not; returns
    {module: (rows, typed rows, proof lines, typed proof lines)}"""
    docs = {n: S.read_file(S.module_path(n, root)) for n in names}
    uses = {n: S.read_module(n, root).uses for n in names}
    # the generated Lean of every module is in the one namespace Qpp: a vocabulary name has one owner
    owner, where = {}, {}
    for n in names:
        for w, (_, line) in vocab_names(docs[n]).items():
            if w in owner and owner[w] != n:
                raise S.SourceError(docs[n].path, line, f"{w} is defined in module {owner[w]} too ({where[w]}): a "
                                    "vocabulary name is global (one namespace Qpp), so it has one owner")
            owner.setdefault(w, n)
            where.setdefault(w, f"{docs[n].path}:{line}")

    # constructs only from the primitives of Q++: no row names Lean or Mathlib. The
    # generator refuses the lean keyword in every source (as it reads a row: whatever the spaces); the check says so
    # before any generation
    for n in names:
        for line, raw in getattr(docs[n], "vocab", []):
            if re.search(r"(^|[\s=(])lean\b", raw.strip().partition(" ")[2]):
                raise S.SourceError(docs[n].path, line, "Q++ has no lean keyword: types and words are built from the "
                                    "primitives of Q++ (QQ^n, (X -> Y), set(X), pair, join, times; qpp/README.md), a "
                                    "body is written with define NAME(args)(points) := ..., and a Mathlib fact is "
                                    "cited (a cit with a row mathlib:)")

    def closure(m):
        out, todo = set(), list(uses[m])
        while todo:
            u = todo.pop()
            if u not in out:
                out.add(u)
                todo.extend(uses.get(u, []))
        return out

    cover = {}
    for n in names:
        rows, trows, lines, tlines = cover[n] = typed_lines(docs[n])
        seen = closure(n) | {n}
        # the typed rows and proof lines, and the typed given rows (where set words and relations are used most)
        givens = [r for it in docs[n].items() for r in it.rows if r.key == "given" and "?{" not in r.text]
        for x in list(trows) + list(tlines) + givens:
            for w, o in owner.items():
                if o in seen:
                    continue
                if re.search(use_pattern(w), x.text):
                    raise S.SourceError(docs[n].path, x.line, f"{w} is the name of a word of module {o}, which {n} "
                                        "does not use (vocabulary names are global: use the module, or rename)")
    return cover


def main(argv):
    if not argv:
        print(__doc__)
        return 2
    if argv[0] == "split":
        plan = []
        for a in argv[2:]:
            name, _, secs = a.partition("=")
            plan.append((name, [s for s in secs.split(",") if s]))
        manifest, modules = write_split(argv[1], plan)
        print(f"qpp.modules: {argv[1]} -> {len(modules)} modules: {', '.join(modules)}")
        return 0
    if argv[0] == "graph":
        md, dot = graph()
        if "-o" in argv:
            Path(argv[argv.index("-o") + 1]).write_text(md, encoding="utf-8")
        else:
            sys.stdout.write(md)
        if "--dot" in argv:
            Path(argv[argv.index("--dot") + 1]).write_text(dot, encoding="utf-8")
        return 0
    if argv[0] == "check":
        names = all_modules()
        S.check_modules([S.read_module(n) for n in names])
        cover = check_vocabulary(names)
        check_cited(names)
        check_primitives()
        signs = check_signs(names)
        check_typed(names)
        print(f"qpp.modules: {len(names)} modules checked")
        if concordance is not None:
            concordance.report(names)
        tot = [0, 0, 0, 0]
        print("typed coverage (Q++ with no hole): statement rows, proof lines; rows and vocabulary lines of both signs "
              "(modules/both_signs.toml)")
        for n in names:
            c = [len(x) for x in cover[n]]
            tot = [a + b for a, b in zip(tot, c)]
            k, mark = signs[n]
            sign = f"{k} of both signs" + (f" (an application: {mark})" if mark else "")
            print(f"  {n}: {c[1]} of {c[0]} rows, {c[3]} of {c[2]} proof lines; {sign}")
        k = sum(v[0] for v in signs.values())
        none = sum(1 for v in signs.values() if not v[0] and not v[1])
        print(f"  all: {tot[1]} of {tot[0]} rows, {tot[3]} of {tot[2]} proof lines; {k} of both signs, {none} of "
              f"{len(names)} modules with none in their typed parts (the hole text is not read)")
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
