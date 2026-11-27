"""Q++ 0.2 source files: the reader, with the line of every element.

A Q++ 0.2 file is the source of a paper or of a section; qpp2latex prints its LaTeX and qpp.kernel its Lean. It
extends the 0.1 format that latex2qpp writes (item lines `kind label`, statement rows `key: q`, proof lines
`(key) word`, `fix`, `word`, `alias`, `define`, `context`, `relation`, `type`) with:

    -- Q++ 0.2                          the format line (first line; not printed)
    paper NAME
    bib PATH                            the bibliography whose entries the citations reuse (relative to the file)
    frame PATH                          the LaTeX around the body (preamble, bibliography), with a line `% qpp: body`
    advertise lem:x(1), thm:y           the headline results that a Palomar Challenge states (a label: all its rows)
    application: REASON                 the mark of an application with data of both signs: the source may use the
                                        forms of both signs of Q++ (qpp/kernel.py; a module's mark is listed in
                                        modules/both_signs.toml)
    include NAME [sec:a, sec:b]         (a manifest) the body of the module modules/NAME/NAME.qpp, or only those
                                        sections, spliced here; a module included in parts is cut at every heading
                                        that its includes name
    external PAPER                      (a manifest) a companion paper; references into it print as citations
    module NAME                         (a module, after the format line) its name; then `uses A, B`, the modules
                                        whose labels its statements and proofs reference, optionally the mark
                                        `application: REASON`, and one blank line
    -- LaTeX prose                      a prose line; prose directly above an item or a proof is its description,
                                        other prose is printed where it stands
    section sec:label Title             a section (subsection: a subsection)
    lemma lem:x [title]                 an item, with an optional title in brackets
      given: ...                        its rows, as in 0.1 (a row `name := term` in a given names a term: an alias)
      fix (2) squares.2                 a fixture of the row above
      after: LaTeX prose                text after the statement display, inside the environment
    cit fact:y [title]                  a cited fact: a statement that a result whose proof cites it takes as a
                                        hypothesis, and its source
      doi: 10.xxxx/yyyy                 the DOI of the source
      stmt: Theorem 2.1                 the number of the statement in the source (optional)
      mathlib: exists_nat_gt (M)        a fact that Mathlib proves: the generated Lean proves the statement from
                                        this lemma, and the theorems that use it take no hypothesis (the DOI is
                                        then optional); (M) the Mathlib module of the lemma, imported, if the
                                        generated files do not import it already (qpp/kernel.py MATHLIB_IMPORTS)
    proof lem:x [title]                 a proof, with an optional title
      (1) word                          a line: its key in parentheses, or "key" in quotes (any LaTeX), or none

A row or a proof line `?{...}` is LaTeX that is not yet a formula of Q++ (a hole), printed as it stands. A comment
that is indented is a note of the source and is not printed.

The skeleton of a paper, papers/NAME/skeleton.tex, is LaTeX: the whole article with its prose (abstract,
introduction, the text of its sections, conclusion), and a line `% qpp: include sec:x` wherever the section sec:x of
a module is printed, its statements and proofs generated from the Q++ source; a line `% qpp: bib PATH` names the
bibliography (read_skeleton).
"""
import re
from dataclasses import dataclass, field
from pathlib import Path

KINDS = ("theorem", "lemma", "proposition", "corollary", "definition", "construction", "remark", "example", "problem",
         "fact", "cit")
HEADER = re.compile(r"^-- Q\+\+ \d")
READINGS = ("remark", "example")  # items whose references are readings, not uses
TITLE = re.compile(r"^(\S+)(?:\s+\[(.*)\])?\s*$")
SPECIAL = ("doi", "stmt", "mathlib", "after")  # rows that are not rows of the statement


@dataclass
class Row:
    key: str
    text: str
    line: int


@dataclass
class Item:
    kind: str
    label: str
    title: str
    line: int
    prose: list = field(default_factory=list)
    rows: list = field(default_factory=list)
    fixes: list = field(default_factory=list)
    fix_rows: list = field(default_factory=list)  # (index of the row above, fixture id)
    # eqfix KEY ID (a value of the equation of row KEY) and neqfix KEY ID (a counterexample to row KEY without the
    # hypotheses its fixture drops): (annotation, key, fixture id, line), checked by qpp/modfix.py, not printed
    checks: list = field(default_factory=list)

    def row(self, key):
        return next((r for r in self.rows if r.key == key), None)

    def stmt_rows(self):
        """the rows of the statement: every row but the source rows of a cited fact and the text after it"""
        return [r for r in self.rows if r.key not in SPECIAL]

    def after(self):
        """the LaTeX after the statement display, inside the environment"""
        return [r.text for r in self.rows if r.key == "after"]


@dataclass
class Proof:
    label: str
    line: int
    prose: list = field(default_factory=list)
    lines: list = field(default_factory=list)
    title: str = ""


@dataclass
class Section:
    label: str
    title: str
    line: int
    level: int = 1


@dataclass
class Prose:
    lines: list
    line: int


@dataclass
class Doc:
    paper: str = ""
    bib: str = ""
    frame: str = ""
    path: str = ""
    advertise: list = field(default_factory=list)  # tags lem:x(1) or labels lem:x
    application: str = ""  # the reason of the mark `application: REASON` (data of both signs), or empty
    blocks: list = field(default_factory=list)  # Prose, Section, Item, Proof in the order of the file
    vocab: list = field(default_factory=list)  # (line, raw) of the word, alias, define, context, relation lines
    origin: list = None  # for a manifest: (file, line) of every line of the flattened text
    modules: list = field(default_factory=list)  # for a manifest: the included modules, in order
    externals: list = field(default_factory=list)  # companion papers
    parts: list = field(default_factory=list)  # for a skeleton: (section label, line) of each line `% qpp: include`

    def where(self, line):
        """`file:line` of a line of the doc: its module file for a manifest"""
        if self.origin and 0 < line <= len(self.origin):
            f, n = self.origin[line - 1]
            return f"{f}:{n}"
        return f"{self.path}:{line}"

    def items(self):
        return [b for b in self.blocks if isinstance(b, Item)]

    def proofs(self):
        """{label: Proof}; the lines of several proofs of one label are joined, in order"""
        out = {}
        for b in self.blocks:
            if isinstance(b, Proof):
                if b.label in out:
                    first = out[b.label]
                    out[b.label] = Proof(b.label, first.line, first.prose, first.lines + b.lines, first.title)
                else:
                    out[b.label] = b
        return out

    def item(self, label):
        return next((b for b in self.items() if b.label == label), None)


class SourceError(ValueError):
    def __init__(self, path, line, msg):
        super().__init__(f"{path}:{line}: {msg}")
        self.line = line


def read(text, path="<qpp>", orphans=False):
    """the Doc of a Q++ 0.2 file"""
    doc = Doc(path=path)
    prose, prose_line = [], 0
    cur = None

    def flush():
        nonlocal prose, prose_line
        if prose:
            doc.blocks.append(Prose(prose, prose_line))
        prose, prose_line = [], 0

    for n, raw in enumerate(text.splitlines(), 1):
        if not raw.strip():
            flush()
            continue
        if raw.startswith("--"):
            if n == 1 and HEADER.match(raw):
                continue
            if not prose:
                prose_line = n
            prose.append(raw[2:].strip())
            cur = None
            continue
        if raw.startswith(" "):
            body = raw.strip()
            if body.startswith("--"):
                continue
            if cur is None:
                raise SourceError(path, n, "an indented line outside an item or a proof")
            if isinstance(cur, Proof):
                m = re.match(r'^(\([^()\s]*\)|"[^"]*")\s+(.*)$', body)
                if m:
                    key = m.group(1)[1:-1] if m.group(1).startswith('"') else m.group(1)
                    cur.lines.append(Row(key, m.group(2), n))
                else:
                    cur.lines.append(Row("", body, n))
            elif body.startswith(("eqfix ", "neqfix ")):
                ann, _, rest = body.partition(" ")
                parts = rest.strip().rsplit(None, 1)
                if len(parts) != 2:
                    raise SourceError(path, n, f"{ann} KEY ID: {body!r}")
                cur.checks.append((ann, parts[0], parts[1], n))
            elif body.startswith("fix "):
                key, fid = body[4:].strip().rsplit(None, 1)
                cur.fixes.append((None if key == "*" else key, fid, n))
                if key != "*":
                    cur.fix_rows.append((len(cur.rows) - 1, fid))
            else:
                key, sep, q = body.partition(": ")
                if not sep:
                    raise SourceError(path, n, f"a row without 'key: ': {body!r}")
                cur.rows.append(Row(key.strip(), q.strip(), n))
            continue
        head, _, rest = raw.partition(" ")
        rest = rest.strip()
        if head == "paper":
            doc.paper = rest
        elif head == "bib":
            doc.bib = rest
        elif head == "frame":
            doc.frame = rest
        elif head == "external":
            doc.externals += [t.strip() for t in rest.split(",") if t.strip()]
        elif head == "advertise":
            doc.advertise += [t.strip() for t in rest.split(",") if t.strip()]
        elif head == "application:":
            if not rest or doc.application:
                raise SourceError(path, n, "one mark `application: REASON`, with its reason")
            doc.application = rest
        elif head in ("section", "subsection"):
            flush()
            label, _, title = rest.partition(" ")
            doc.blocks.append(Section(label, title.strip(), n, 1 if head == "section" else 2))
            cur = None
        elif head in ("word", "alias", "define", "context", "relation", "type"):
            doc.vocab.append((n, raw))
        elif head in KINDS or head == "proof":
            m = TITLE.match(rest)
            if not m:
                raise SourceError(path, n, f"cannot read the label: {rest!r}")
            label, title = m.group(1), (m.group(2) or "")
            desc = prose
            prose, prose_line = [], 0
            if head == "proof":
                cur = Proof(label, n, desc, title=title)
            else:
                if doc.item(label):
                    raise SourceError(path, n, f"{label} is defined twice")
                cur = Item(head, label, title, n, desc)
            doc.blocks.append(cur)
        else:
            raise SourceError(path, n, f"unknown line: {raw!r}")
    flush()
    for p in doc.proofs().values():
        if not doc.item(p.label) and not orphans:
            raise SourceError(path, p.line, f"a proof of {p.label}, which no item states")
    for it in doc.items():
        if it.kind == "cit":
            d, ml = it.row("doi"), it.row("mathlib")
            if ml is not None and not re.fullmatch(r"[A-Za-z_][\w.']*(, [A-Za-z_][\w.']*)*( \(Mathlib(\.\w+)+\))?",
                                                   ml.text.strip()):
                raise SourceError(path, ml.line, f"the row mathlib of {it.label}: a Mathlib name (or several, separated "
                                  "by commas, whose conjunction proves the statement), then its module in parentheses "
                                  "if the generated files do not import it")
            if (d or ml is None) and (not d or not re.fullmatch(r"10\.\d{4,9}/\S+", d.text)):
                raise SourceError(path, it.line, f"the cited fact {it.label} needs a row 'doi: 10.xxxx/...' "
                                  "(or a row 'mathlib: Name', a fact that Mathlib proves)")
    return doc


ROOT = Path(__file__).resolve().parent.parent
MODULES = "modules"  # modules/NAME/NAME.qpp under the root of the repository
INCLUDE = re.compile(r"^include\s+(\S+)(?:\s+(.*))?$")
REF = re.compile(r"\\(?:[cC]ref|ref|eqref)\{([^}]*)\}")
LABEL = re.compile(r"\\label\{([^}]*)\}")


def module_path(name, root=ROOT):
    return Path(root) / MODULES / name / f"{name}.qpp"


@dataclass
class Module:
    name: str
    path: str
    uses: list
    body: list  # (line number in the module file, text)
    application: str = ""  # the reason of the mark `application: REASON`, or empty


def read_module(name, root=ROOT):
    """a module file: the format line, `module NAME`, optionally `uses A, B`, optionally the mark `application:
    REASON` (an application with data of both signs), one blank line, then the body"""
    path = module_path(name, root)
    lines = path.read_text(encoding="ascii").split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    rel = path.relative_to(root).as_posix() if path.is_relative_to(root) else str(path)
    if len(lines) < 3 or not HEADER.match(lines[0]) or lines[1] != f"module {name}":
        raise SourceError(rel, 2, f"a module starts with the format line and `module {name}`")
    n, uses = 2, []
    if lines[2].startswith("uses "):
        uses = [u.strip() for u in lines[2][5:].split(",") if u.strip()]
        n = 3
    mark = ""
    if n < len(lines) and lines[n].startswith("application:"):
        mark = lines[n][len("application:"):].strip()
        if not mark:
            raise SourceError(rel, n + 1, "the mark `application: REASON` gives its reason")
        n += 1
    if n >= len(lines) or lines[n] != "":
        raise SourceError(rel, n + 1, "one blank line after the module header")
    return Module(name, rel, uses, [(i + 1, lines[i]) for i in range(n + 1, len(lines))], mark)


def sections_of(body, wanted, cuts=()):
    """the lines of the sections `wanted` (labels of section or subsection lines), each to the next heading of the
    same or a higher level or to the next cut (a heading that another `include` of the module names), in the order
    of the body"""
    out, keep, level = [], False, 0
    for n, t in body:
        head, _, rest = t.partition(" ")
        if head in ("section", "subsection"):
            lv = 1 if head == "section" else 2
            label = rest.partition(" ")[0]
            if label in wanted:
                keep, level = True, lv
            elif keep and (lv <= level or label in cuts):
                keep = False
        if keep:
            out.append((n, t))
    return out


def flatten(text, path="<qpp>", root=ROOT):
    """(text, origin, modules) of a manifest: each `include` line replaced by the body of its module, or of the
    sections it names; a module included in parts is cut at every heading its includes name. origin gives
    (file, line) for every line of the text"""
    rows = text.split("\n")[:-1] if text.endswith("\n") else text.split("\n")
    named = {}
    for t in rows:
        m = INCLUDE.match(t)
        if m and m.group(2):
            named.setdefault(m.group(1), set()).update(w.strip() for w in m.group(2).split(",") if w.strip())
    out, origin, mods = [], [], []
    for n, t in enumerate(rows, 1):
        m = INCLUDE.match(t)
        if not m:
            out.append(t)
            origin.append((path, n))
            continue
        mod = read_module(m.group(1), root)
        mods.append(mod)
        body = mod.body
        if m.group(2):
            wanted = [w.strip() for w in m.group(2).split(",") if w.strip()]
            body = sections_of(body, wanted, named.get(mod.name, set()) - set(wanted))
            if not body:
                raise SourceError(path, n, f"module {mod.name} has none of the sections {', '.join(wanted)}")
        for k, line in body:
            out.append(line)
            origin.append((mod.path, k))
    return "\n".join(out) + "\n", origin, mods


SKELETON = "skeleton.tex"  # the skeleton of the paper papers/NAME
DIRECTIVE = re.compile(r"^%\s*qpp:\s*(\S*)\s*(.*?)\s*$")  # a line `% qpp: include sec:x` or `% qpp: bib PATH`
PLACE = re.compile(r"^%\s*qpp:\s*include(?:\s|$)")  # a line of a skeleton: a section of a module goes here
PART = "% qpp: part"  # the prose line before the K-th part of the manifest of a skeleton


def section_owners(root=ROOT):
    """{label: NAME} of the section and subsection headings of the modules modules/NAME/NAME.qpp"""
    out = {}
    for p in sorted((Path(root) / MODULES).glob("*/*.qpp")):
        if p.stem == p.parent.name:
            for _n, t in read_module(p.stem, root).body:
                head, _, rest = t.partition(" ")
                if head in ("section", "subsection") and rest.split():
                    out.setdefault(rest.split()[0], p.stem)
    return out


def read_skeleton(path, root=ROOT):
    """the Doc of the skeleton of a paper: the manifest of the sections that its lines `% qpp: include sec:x` name, in
    their order, each after the prose line `% qpp: part K`, at which qpp2latex cuts the printed body into the parts of
    the skeleton; a section runs to the next heading of the same or a higher level, or to the next heading of its
    module that another line names. The frame of the Doc is the skeleton itself, its paper the name of the folder"""
    path = Path(path)
    lines = path.read_text(encoding="ascii").split("\n")
    owners, bib, parts = section_owners(root), "", []
    text, at = ["-- Q++ 0.2", f"paper {path.parent.name}", "", ""], [1, 1, 1, 1]  # at: the line of the skeleton
    for n, t in enumerate(lines, 1):
        m = DIRECTIVE.match(t)
        if not m:
            continue
        word, arg = m.groups()
        if word == "bib" and arg and len(arg.split()) == 1 and not bib:
            bib = arg
            continue
        if word != "include" or len(arg.split()) != 1:
            raise SourceError(str(path), n, "a line `% qpp: ...` of a skeleton is `% qpp: include sec:x`, one section "
                              "of a module, or `% qpp: bib PATH`, once")
        label = arg
        if label not in owners:
            raise SourceError(str(path), n, f"no module of {MODULES}/ has the section {label}")
        if any(label == q for q, _n in parts):
            raise SourceError(str(path), n, f"the section {label} is placed twice")
        parts.append((label, n))
        text += [f"-- {PART} {len(parts)}", "", f"include {owners[label]} {label}", ""]
        at += [n] * 4
    if not bib:
        raise SourceError(str(path), 1, "a skeleton names its bibliography: a line `% qpp: bib PATH`")
    text[2] = f"bib {bib}"
    flat, origin, mods = flatten("\n".join(text) + "\n", str(path), root)
    check_modules(mods, root)
    doc = read(flat, str(path))
    doc.frame, doc.parts, doc.modules = path.name, parts, [m.name for m in mods]
    doc.origin = [(f, at[k - 1]) if f == str(path) else (f, k) for f, k in origin]
    return doc


def refs_of(text):
    return {x.strip() for m in REF.finditer(text) for x in m.group(1).split(",") if x.strip()}


def labels_of_lines(lines):
    """the labels a body defines: items, proofs excluded, sections, and \\label{..} in its LaTeX"""
    out = set()
    for _n, t in lines:
        head, _, rest = t.partition(" ")
        if head in KINDS or head in ("section", "subsection"):
            out.add(rest.split()[0] if rest.split() else rest)
        out |= set(LABEL.findall(t))
    return out


def hard_refs(lines):
    """the references of the statement rows and the proof lines (indented lines, but `origin:` and `after:`) to
    items, not to sections: the dependencies a module declares with `uses`. The rows and proofs of remarks and
    examples are readings, as prose is, and may point anywhere in the paper (the printed paper's references are
    checked whole, by .github/scripts/check_refs.py)"""
    kinds = {}
    for _n, t in lines:
        head, _, rest = t.partition(" ")
        if head in KINDS and rest.split():
            kinds[rest.split()[0]] = head
    out, soft = set(), False
    for _n, t in lines:
        if not t.startswith(" "):
            head, _, rest = t.partition(" ")
            if head in KINDS:
                soft = head in READINGS
            elif head == "proof":
                soft = kinds.get(rest.split()[0] if rest.split() else "") in READINGS
            elif t.strip():
                soft = False
            continue
        if not soft and not t.strip().startswith(("origin:", "after:", "--")):
            out |= {r for r in refs_of(t) if not r.startswith(("sec:", "app:"))}
    return out


def check_modules(mods, root=ROOT):
    """every hard reference of a module is defined in it or in the closure of its uses; the uses have no cycle; no
    label is defined in two modules (the modules are one set, whichever papers include them)"""
    defined, seen = {}, {}

    def load(name):
        if name not in seen:
            seen[name] = read_module(name, root)
            for u in seen[name].uses:
                load(u)
        return seen[name]

    for m in mods:
        load(m.name)
    for name, m in seen.items():
        for lab in sorted(labels_of_lines(m.body)):
            if defined.setdefault(lab, name) != name:
                line = next((n for n, t in m.body if lab in t), 1)
                raise SourceError(m.path, line, f"{lab} is defined in module {defined[lab]} and in {name}")
    state = {}

    def visit(name, stack):
        if state.get(name) == 1:
            raise SourceError(seen[name].path, 3, "a cycle of uses: " + " -> ".join(stack + [name]))
        if state.get(name) == 2:
            return
        state[name] = 1
        for u in seen[name].uses:
            visit(u, stack + [name])
        state[name] = 2

    for name in seen:
        visit(name, [])

    def closure(name):
        out, todo = {name}, [name]
        while todo:
            for u in seen[todo.pop()].uses:
                if u not in out:
                    out.add(u)
                    todo.append(u)
        return out

    for name, m in seen.items():
        cl = closure(name)
        for r in sorted(hard_refs(m.body)):
            home = defined.get(r)
            if home is None:
                continue  # a label of no module: the paper's own, or of a companion paper
            if home not in cl:
                line = next(n for n, t in m.body if r in refs_of(t))
                raise SourceError(m.path, line, f"{r} is defined in module {home}, which {name} does not use")
    return seen


def read_module_file(path):
    """a module file read as a source of its own: `module NAME` read as `paper NAME`, its `uses` kept on the doc
    (doc.uses), the lines numbered as in the file"""
    rows = Path(path).read_text(encoding="ascii").split("\n")
    name = rows[1].split(None, 1)[1].strip()
    mod = read_module(name, Path(path).resolve().parents[2])
    rows[1] = f"paper {name}"
    for k in (2, 3):
        if k < len(rows) and (rows[k].startswith("uses ") or rows[k].startswith("application:")):
            rows[k] = ""
    # a module may hold the proofs of items of the modules it uses (construction-proofs)
    doc = read("\n".join(rows), str(path), orphans=True)
    doc.uses = mod.uses
    doc.application = mod.application
    return doc


def read_file(path):
    if Path(path).name == SKELETON:
        return read_skeleton(path)
    with open(path, encoding="ascii") as f:
        text = f.read()
    if text.split("\n")[1:2] and text.split("\n")[1].startswith("module "):
        return read_module_file(path)
    if not any(INCLUDE.match(t) for t in text.split("\n")):
        return read(text, str(path))
    flat, origin, mods = flatten(text, str(path))
    check_modules(mods)
    doc = read(flat, str(path))
    doc.origin, doc.modules = origin, [m.name for m in mods]
    return doc
