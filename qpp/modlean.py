"""modlean: the Lean of the Q++ modules, one file per module of modules/ (qpp/kernel.py with its kernel target):
modules/NAME/NAME.qpp -> lean/QppModules/Name.lean, which imports Mathlib, the bridge (lean/QppBridge) and the files
of the modules NAME uses. A file has two parts: the Mathlib reading of the rows, generated and proved over Mathlib in
the namespace QppMathlib (so a reference to a proved row of a used module is its name), and the statements over the
kernel words (qpp/lean/QppKernel/Words.lean) in the namespace Qpp.Modules, each proved from its reading through the
bridge; the axiom audit and the audit of the statements read the second. A file past PART bytes or LINES lines is
written in parts lean/QppModules/Name/PartK.lean, cut at declarations, each importing the one before, and Name.lean
imports the last: one Lean process keeps what it elaborated until its file ends, so its memory grows with the file. The rows
with a hole, or a word the target does not read yet, are listed in the doc comment of the file, not generated, and
fail the run: everything in the modules is in Q++ (qpp.modules check refuses the holes). A
module is positive unless it carries the mark `application: REASON`: a row or a vocabulary line with a form of both
signs is refused, except those that modules/both_signs.toml lists for it (qpp/kernel.py, positivity).

Usage: python3 -m qpp.modlean NAME... [--check]    the file of each module named (nothing else is written)
       python3 -m qpp.modlean --index               lean/QppModules.lean (imports every module) and the axiom audit
                                                    lean/Axioms.lean, from the files written
       python3 -m qpp.modlean --all [--check]       every module, then the index
       python3 -m qpp.modlean --palomar NAME        the Palomar entry of lean/ from the file of module NAME: its
                                                    Challenge and Solution in lean/QppPalomar/, and lean/comparator.json
The memo units gen-{module} and gen-modules-index (tools/memo_units.toml) run the first two. A module sees the proved
rows of the modules it uses, directly or not (the files it imports), and of no other.

A used module is generated for the rows it proves (its statements, cited facts, aliases and vocabulary), and the set
of its proved rows is kept in .memo/modlean/NAME.json (gitignored, not an input of any unit), keyed by the SHA-256 of
the sources of the generator (qpp/*.py), modules/both_signs.toml and the sources of the module and of the modules it
uses, directly or not. With that set the module is generated without its proofs (generate_all, proved); without it,
with its proofs, and the set is kept (QPP_MODLEAN_CACHE=off: always with its proofs, nothing kept). A set is only ever
read under the key of the sources it was found from, so the file written does not depend on the order of the units.
"""
import hashlib
import json
import os
import re
import sys
from pathlib import Path

from . import closers
from . import kernel as K
from . import source as S

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "lean"


def camel(name):
    """the Lean module name of a Q++ module: one-var -> OneVar"""
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[^A-Za-z0-9]+", name) if p)


def names():
    return sorted(p.name for p in (ROOT / "modules").iterdir() if (p / f"{p.name}.qpp").is_file())


def order(mods):
    """the modules after the modules they use"""
    uses = {m: S.read_module(m, ROOT).uses for m in mods}
    out, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for u in uses.get(m, []):
            visit(u)
        out.append(m)
    for m in mods:
        visit(m)
    return out


CACHE = ROOT / ".memo" / "modlean"
CACHE_KEEP = 4  # the keys that the file of a module keeps, the most recent first


def source_key(name, uses):
    """the SHA-256 of what the generation of a module reads: the generator, the list of rows of both signs, and the
    sources of the module and of the modules it uses, directly or not"""
    h = hashlib.sha256()
    files = sorted((ROOT / "qpp").glob("*.py")) + [ROOT / "modules" / "both_signs.toml"]
    files += [ROOT / "modules" / m / f"{m}.qpp" for m in sorted(closure(name, uses) | {name})]
    for f in files:
        h.update(f.relative_to(ROOT).as_posix().encode() + b"\0")
        h.update(f.read_bytes() if f.is_file() else b"")
        h.update(b"\0")
    return h.hexdigest()


def cached_proved(name, key):
    """the names of the rows that the module proves, kept under the key, or None"""
    try:
        data = json.loads((CACHE / f"{name}.json").read_text(encoding="utf-8"))
        hit = next((e["proved"] for e in data if e.get("key") == key), None)
    except (OSError, ValueError, TypeError, KeyError, AttributeError):
        return None
    return set(hit) if isinstance(hit, list) else None


def keep_proved(name, key, proved):
    """keep the names of the rows that the module proves under the key (a write by rename, so that two units that
    write the same file at once leave one of the two whole)"""
    f = CACHE / f"{name}.json"
    try:
        data = json.loads(f.read_text(encoding="utf-8")) if f.is_file() else []
        data = [e for e in data if isinstance(e, dict) and e.get("key") != key]
    except (OSError, ValueError):
        data = []
    data = [{"key": key, "proved": sorted(proved)}] + data[:CACHE_KEEP - 1]
    try:
        CACHE.mkdir(parents=True, exist_ok=True)
        tmp = f.with_name(f"{f.name}.{os.getpid()}.tmp")
        tmp.write_text(json.dumps(data, indent=0) + "\n", encoding="utf-8")
        os.replace(tmp, f)
    except OSError:
        pass


def generate(name, known, known_cits=None, known_aliases=None, known_vocab=None, proved=None):
    """(Gen, Lean path) of one module; known: the proved rows of the modules generated before; known_cits: their
    cited facts; known_aliases: their aliases; known_vocab: their vocabulary (kind -> name -> entry); proved: the
    names of its proved rows, when kept (generate_all: no proof is generated)"""
    path = ROOT / "modules" / name / f"{name}.qpp"
    doc = S.read_file(path)
    doc.lean_imports = [f"QppModules.{camel(u)}" for u in doc.uses]
    # the kernel target: the Mathlib reading in the namespace QppMathlib, the statements over the kernel words
    # in the namespace Qpp.Modules, each theorem from its reading through the bridge (lean/QppBridge)
    K.KERNEL_TARGET[0] = True
    doc.lean_ns = K.MATHLIB_NS
    g = K.generate_all(doc, f"QppModules.{camel(name)}", source=path.relative_to(ROOT).as_posix(), known=known,
                       known_cits=known_cits, known_aliases=known_aliases, known_vocab=known_vocab,
                       allowed=K.both_table(ROOT)[0].get(name, []), proved=proved)
    return g, OUT / "QppModules" / f"{camel(name)}.lean"


# the size of a part of the Lean of a module, in bytes: the Lean process that compiles a file keeps what it elaborated
# until the file ends (the references of its .ilean), so its memory grows with the file; a module whose Lean is larger
# is written in parts of about this size, each compiled by its own process
PART = int(os.environ.get("QPP_LEAN_PART", "1500000"))
# the most lines of a part: a file of a Lean library registered on Palomar has at most 10,000 lines
LINES = int(os.environ.get("QPP_LEAN_LINES", "9000"))


def cuts(text, a, b):
    """the positions in text[a:b] where a part may start: the start of each declaration, with the doc comment and the
    attributes written above it"""
    out = []
    for _, x, _ in closers.declarations(text[a:b]):
        x += a
        before = text[a:x].rstrip()
        if before.endswith("-/"):
            j = text.rfind("\n/-", a, x)
            x = j + 1 if j >= a else x
        out.append(x)
    return out


def lines(text):
    return text.count("\n") + (not text.endswith("\n"))


def split(text, size=None, most=None):
    """the Lean of a module cut into parts of about size bytes and at most `most` lines at declarations, as
    [(header, body)]; one part when it fits. The header (the imports, the doc comment and the options) is repeated in
    every part; the body is the declarations, each inside the namespace it was written in"""
    size = PART if size is None else size
    most = LINES if most is None else most
    first = re.search(r"(?m)^namespace \S+\n", text)
    if not size or not first or (len(text.encode("utf-8")) <= size and lines(text) <= most):
        return [(text, "")]
    header = text[:first.start()]
    pieces = []          # (namespace, text) cut at the declarations
    for m in re.finditer(r"(?m)^namespace (\S+)\n(.*?)^end \1\n?", text[first.start():], re.S):
        ns, a = m.group(1), first.start() + m.start(2)
        b = first.start() + m.end(2)
        at = sorted(set([a] + cuts(text, a, b)))
        pieces += [(ns, text[x:y]) for x, y in zip(at, at[1:] + [b])]
    nbytes, nlines = len(text.encode("utf-8")), lines(text)
    k = max(-(-nbytes // size), -(-nlines // most))
    # the measure that binds: the parts are of equal size in it
    if nlines * size > nbytes * most:
        weight = lambda t: t.count("\n")
    else:
        weight = lambda t: len(t.encode("utf-8"))
    while True:
        out = cut(header, pieces, weight, k)
        if all(lines(h + b) <= most for h, b in out) or k >= len(pieces):
            return out
        k += 1


def cut(header, pieces, weight, k):
    """the pieces in k parts of about equal weight, every part with the header and its namespaces"""
    total = sum(weight(t) for _, t in pieces)
    parts, cur, done = [], [], 0
    for ns, t in pieces:
        cur.append((ns, t))
        done += weight(t)
        if done >= total * (len(parts) + 1) / k and len(parts) < k - 1:
            parts.append(cur)
            cur = []
    if cur:
        parts.append(cur)
    out = []
    for part in parts:
        body, ns = [], None
        for n, t in part:
            if n != ns:
                if ns:
                    body.append(f"end {ns}\n\n")
                body.append(f"namespace {n}\n")
                ns = n
            body.append(t)
        body.append(f"end {ns}\n")
        out.append((header, "".join(body)))
    return out


def write_lean(name, text):
    """write the Lean of module name: lean/QppModules/Name.lean, or, past PART bytes or LINES lines, the parts
    lean/QppModules/Name/PartK.lean (write_parts); returns the paths written"""
    return write_parts(OUT / "QppModules" / f"{camel(name)}.lean", f"QppModules.{camel(name)}", text,
                       f"{name}: the Lean of modules/{name}/{name}.qpp", "qpp/modlean.py")


def write_parts(single, mod, text, what=None, by="qpp/kernel.py"):
    """write the generated Lean file single of the Lean module mod: as it is, or, past PART bytes or LINES lines, the
    parts PartK.lean in the folder of its name, each importing the one before, and single importing the last (so that a
    file that imports mod reads every part); what names it in the doc comment of single (by default the name and the
    source of its header); returns the paths written"""
    single = Path(single)
    base = single.with_suffix("")
    parts = split(text)
    written = []
    if len(parts) == 1:
        single.write_text(text, encoding="utf-8")
        written.append(single)
    else:
        if what is None:
            m = re.search(r"(?m)^# (\S+): generated by \S+ from (\S+); do not edit$", text)
            what = f"{m.group(1)}: the Lean of {m.group(2)}" if m else mod
        texts = []
        for i, (header, body) in enumerate(parts, 1):
            h = header
            if i > 1:
                h = re.sub(r"(?m)^(public import [^\n]*\n)(?![\s\S]*^public import )",
                           lambda m: m.group(1) + f"public import {mod}.Part{i - 1}\n", h, count=1)
            h = h.replace(f"generated by qpp/kernel.py", f"part {i} of {len(parts)}, generated by qpp/kernel.py", 1)
            texts.append(h + body)
        if join(texts) != text:
            raise SystemExit(f"qpp.modlean: the parts of {mod} do not read back as its text (a line outside the "
                             "namespaces?); nothing written")
        base.mkdir(parents=True, exist_ok=True)
        for i, t in enumerate(texts, 1):
            f = base / f"Part{i}.lean"
            f.write_text(t, encoding="utf-8")
            written.append(f)
        single.write_text(f"module\n\npublic import {mod}.Part{len(parts)}\n\n/-! # {what} in {len(parts)} parts, "
                          f"generated by {by}; do not edit -/\n", encoding="utf-8")
        written.append(single)
    for f in sorted(base.glob("Part*.lean")) if base.is_dir() else []:
        if f not in written:
            f.unlink()
    if base.is_dir() and not any(base.iterdir()):
        base.rmdir()
    return written


def read_lean(name):
    """the Lean of module name as one text, from its file or its parts (read_parts)"""
    return read_parts(OUT / "QppModules" / f"{camel(name)}.lean")


def read_parts(single):
    """a generated Lean file as one text, from the file or its parts: the inverse of write_parts (a part after the
    first without its header, and a namespace that write_parts closed at the end of a part and opened again at the
    start of the next one joined)"""
    single = Path(single)
    base = single.with_suffix("")
    parts = sorted(base.glob("Part*.lean"), key=lambda f: int(re.sub(r"\D", "", f.stem))) if base.is_dir() else []
    if not parts:
        return single.read_text(encoding="utf-8")
    return join([f.read_text(encoding="utf-8") for f in parts])


def join(texts):
    """the text of a generated file from the texts of its parts (read_parts)"""
    out = re.sub(r"part 1 of \d+, generated by qpp/kernel\.py", "generated by qpp/kernel.py", texts[0], count=1)
    for t in texts[1:]:
        body = t[re.search(r"(?m)^namespace \S+\n", t).start():]
        opening = body[:body.index("\n") + 1]
        closing = "end " + opening[len("namespace "):]
        if out.endswith(closing):
            out, body = out[:-len(closing)], body[len(opening):]
        else:
            out += "\n"
        out += body
    return out


def closure(m, uses):
    """the modules m uses, directly or not"""
    out, todo = set(), list(uses.get(m, []))
    while todo:
        u = todo.pop()
        if u not in out:
            out.add(u)
            todo.extend(uses.get(u, []))
    return out


THEOREM = re.compile(r"^theorem (\S+)", re.M)
# the text of each module written by main, as its generator wrote it, with the texts of the modules it uses
# (qpp/closers.py refresh reads them)
TEXTS = {}


def index(mods):
    """lean/QppModules.lean and lean/Axioms.lean, from the generated files of the modules"""
    mods = order(mods)
    root = OUT / "QppModules.lean"
    root.write_text("module\n\n" + "".join(f"public import QppModules.{camel(m)}\n" for m in mods), encoding="utf-8")
    names_ = []
    for m in mods:
        f = OUT / "QppModules" / f"{camel(m)}.lean"
        if f.is_file():
            # the theorems over the kernel, which rest on their Mathlib readings; the file whole, or its parts
            part = read_lean(m).partition(f"namespace {K.KERNEL_NS}\n")[2]
            names_ += [f"{K.KERNEL_NS}.{n}" for n in THEOREM.findall(part)]
    # the axiom audit (.github/scripts/check_axioms.py): every generated theorem
    audit = ["module", "", "import QppModules", "", "/-! The axiom audit of the generated Lean of the modules (qpp/modlean.py); "
             "do not edit. -/", ""] + [f"#print axioms {n}" for n in sorted(names_)]
    if not names_:
        audit.append("-- no theorem generated yet")  # .github/scripts/check_axioms.py EMPTY
    (OUT / "Axioms.lean").write_text("\n".join(audit) + "\n", encoding="utf-8")
    print(f"qpp.modlean: {root.relative_to(ROOT)} ({len(mods)} modules), lean/Axioms.lean ({len(names_)} theorems)")


# the Palomar entry of the Lake project lean/ (tools/check_palomar.py): the rows of one module, each stated over Mathlib
# in a Challenge that imports Mathlib alone and proved by the library under the same name
ENTRY_DIR = OUT / "QppPalomar"
STATEMENT = re.compile(r"(?ms)^/-- The statement of (\S+?)\((.*?)\), (\S+?):(\d+): .*?-/\n"
                       r"(def (\S+)\.statement : Prop :=\n.*?)\n\n")


def lean_imports(module):
    """the modules outside this repository that a Lean module of lean/ or qpp/lean imports, directly or through the
    modules of the repository it imports, each once, in the order first met"""
    out, seen, todo = [], set(), [module]
    while todo:
        m = todo.pop(0)
        if m in seen:
            continue
        seen.add(m)
        f = next((d / f"{m.replace('.', '/')}.lean" for d in (OUT, ROOT / "qpp" / "lean")
                  if (d / f"{m.replace('.', '/')}.lean").is_file()), None)
        if f is None:
            out.append(m)
            continue
        todo += re.findall(r"(?m)^(?:public )?(?:meta )?import (?:all )?(\S+)", f.read_text(encoding="utf-8"))
    return out


def entry(name):
    """lean/QppPalomar/Name/Challenge.lean, lean/QppPalomar/Name/Solution.lean and lean/comparator.json, from the
    generated Lean of module name: the Challenge imports the modules outside the repository that the library reads
    (Mathlib and Lean core, so that the statements elaborate as in the library), repeats the statement of each row
    over Mathlib (the definition QppMathlib.L.statement, verbatim) and states its theorem with sorry; the Solution
    imports the module, which proves each one; comparator.json names the theorems"""
    mod = f"QppModules.{camel(name)}"
    text = read_lean(name)
    reading = text[text.index(f"namespace {K.MATHLIB_NS}\n"):text.index(f"end {K.MATHLIB_NS}\n")]
    source = f"modules/{name}/{name}.qpp"
    doc = S.read_file(ROOT / source)
    blocks, names_ = [], []
    for m in STATEMENT.finditer(reading):
        label, key, where, line, decl, n = m.groups()
        item = doc.item(label)
        row = (item.row(f"({key})") or item.row(key)) if item else None
        what = f"{label}({key}), {where}:{line}" + (f": {row.text}" if row is not None else "")
        blocks.append(f"/-- {K.doc_text(what)} -/\n{decl}\n\ntheorem {n} : {n}.statement := sorry\n")
        names_.append(f"{K.MATHLIB_NS}.{n}")
    theorems = THEOREM.findall(reading)
    if sorted(n.rsplit(".", 1)[-1] for n in names_) != sorted(theorems):
        raise SystemExit(f"qpp.modlean: the Palomar entry of {name}: {len(names_)} statements for {len(theorems)} "
                         "theorems; nothing written")
    imports = [m for m in lean_imports(mod) if m.split(".")[0] in ("Mathlib", "Init", "Std", "Lean")]
    note = (f"# {name}: the Palomar Challenge, generated by qpp/modlean.py from {source}; do not edit\n\n"
            f"The {len(names_)} rows of the module over Mathlib: the statement of each, as the library states it "
            f"(`{K.MATHLIB_NS}.L.statement`,\nverbatim), and its theorem with `sorry`, as Palomar asks of a Challenge: "
            "building this module warns\n`declaration uses sorry` once per theorem, by design. It imports the "
            "modules of Mathlib and of Lean core that\nthe library reads, so that the statements elaborate to the "
            "same declarations as in the library.")
    challenge = ("module\n\n" + "".join(f"public import {m}\n" for m in imports) + "\n/-!\n" + K.doc_text(note) +
                 "\n-/\n\n" + K.SECTION + f"\nnamespace {K.MATHLIB_NS}\n\n" + "\n".join(blocks) +
                 f"\nend {K.MATHLIB_NS}\n")
    solution = (f"module\n\npublic import {mod}\n\n/-!\n" +
                K.doc_text(f"# {name}: the Palomar Solution, generated by qpp/modlean.py from {source}; do not edit\n\n"
                           f"The library proves the theorems of the Challenge under the same names, in `{mod}`, each "
                           "from the rows\nof the modules it uses; `lake comparator` (comparator.json) checks that "
                           "they are those of the Challenge.") + "\n-/\n")
    base = ENTRY_DIR / camel(name)
    base.mkdir(parents=True, exist_ok=True)
    (base / "Challenge.lean").write_text(challenge, encoding="utf-8")
    (base / "Solution.lean").write_text(solution, encoding="utf-8")
    config = {"challenge_module": f"QppPalomar.{camel(name)}.Challenge",
              "solution_module": f"QppPalomar.{camel(name)}.Solution", "theorem_names": names_,
              "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
    (OUT / "comparator.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
    print(f"qpp.modlean: the Palomar entry of {name}: {len(names_)} theorems, {base.relative_to(ROOT)}/Challenge.lean "
          f"({challenge.count(chr(10))} lines, {len(challenge.encode())} bytes), Solution.lean, lean/comparator.json")


def main(argv):
    if "--index" in argv:
        index(names())
        return 0
    if len(argv) == 2 and argv[0] == "--palomar":
        entry(argv[1])
        return 0
    every = "--all" in argv
    if "--check" in argv:
        global PART
        PART = 0  # one file, whose lines the source map of the check reads
    mods = names() if every else [a for a in argv if not a.startswith("--")]
    if not mods:
        print(__doc__)
        return 2
    unknown = [m for m in mods if not (ROOT / "modules" / m / f"{m}.qpp").is_file()]
    if unknown:
        print(f"qpp.modlean: no module {', '.join(unknown)} (modules/NAME/NAME.qpp)")
        return 2
    # only the modules named and the modules they use, directly or not, are read: the memo unit gen-{module} then
    # has the files of its uses as inputs, and not every module of modules/
    uses = {}
    todo = list(mods)
    while todo:
        m = todo.pop()
        if m not in uses:
            uses[m] = S.read_module(m, ROOT).uses
            todo.extend(uses[m])
    need = set(uses)
    cache = os.environ.get("QPP_MODLEAN_CACHE", "on") != "off"
    results, cited, aliased, vocab, status = {}, {}, {}, {}, 0
    mains = {}
    for m in order(sorted(need)):
        known, known_cits, known_aliases, known_vocab = {}, {}, {}, {}
        for u in closure(m, uses):
            known.update(results.get(u, {}))
            known_cits.update(cited.get(u, {}))
            known_aliases.update(aliased.get(u, {}))
            for kind, entries in vocab.get(u, {}).items():
                known_vocab.setdefault(kind, {}).update(entries)
        key = source_key(m, uses) if cache else None
        kept = cached_proved(m, key) if cache and m not in mods else None
        g, out = generate(m, known, known_cits, known_aliases, known_vocab, proved=kept)
        if cache and kept is None:
            keep_proved(m, key, g.results)
        results[m] = dict(g.results)
        cited[m] = dict(g.cits)
        aliased[m] = dict(g.aliases)
        vocab[m] = g.vocab
        mains[m] = g.main
        if m not in mods:
            continue  # a used module: its rows are known to the references, its file is not rewritten
        out.parent.mkdir(parents=True, exist_ok=True)
        # each closer chain cut to the alternatives that closed it in the last run of Lean (qpp/closers.py),
        # then the file, in parts past PART bytes or LINES lines
        # (a cut chain is kept while the statements it reads, in the module and in the modules it uses, are unchanged)
        context = [mains[u] for u in sorted(closure(m, uses))]
        # each hedge `try t` as the chain it is, `(first | t | skip)`, cut like the others
        main = closers.try_chains(g.main)
        TEXTS[m] = (main, context)
        write_lean(m, closers.order(main, f"QppModules.{camel(m)}", context=context))
        ok = sum(1 for r in g.report if r[3])
        print(f"qpp.modlean: {m} -> {out.relative_to(ROOT)}: {ok} of {len(g.report)} rows generated")
        for label, key, line, done, why in g.report:
            if not done:
                print(f"  modules/{m}/{m}.qpp:{line}: {label} {key}: not generated: {why}")
                status = 1
        if "--check" in argv:
            status |= K.check(out, g.srcmap, ROOT / "modules" / m / f"{m}.qpp") or 0
    if every:
        index(names())
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
