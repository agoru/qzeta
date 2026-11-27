"""modfix: the fixtures of one Q++ module, checked on its statements (the memo unit fix-{module}).

modules/M/M.qpp, after the modules it uses, is read as Q++ source, each statement a formula tree (source_text); then each
`fix` line of M names a fixture, modules/M/fixtures/ID.json (rows) or ID.py (an algorithm), and its rows are checked on
the statement by the checker of qpp/tests/test_qpp.py (none fails or is undecided, some row holds, a witness fixture
holds on every row). A fixture file of modules/M/fixtures that no fix line names is an error, and so is a cited item
(`cit`) with no fix line and no `mathlib:` row: a cited statement enters the theorems that use it as a hypothesis, so a
fixture checks that it is not stated wrong (a false hypothesis would make them empty). A cited rule about a context
(`context coef(...)`, a relation that is a parameter: every typed statement row applies it) has no concrete instance
in Q++: its fixtures ({"kind": "model"}) are evaluated on the exact model of the contexts of the pair (qpp/ctxmodel.py),
with the vocabulary of M and of the modules it uses. The lines `eqfix KEY ID` (a
value: on every row the hypotheses hold and every side of the equation is the value "=") and `neqfix KEY ID` (a
counterexample: the hypotheses that its fixture drops are needed) are read from the source and checked on the row
with the functions of the same checker.

No fixture is evaluated by enumeration (qpp/enumeration.py): a check that would decide a clause or a term by visiting
the points of a set of candidates (the lattice points of a box, the numbers up to a bound, a grid, the vertices of a
polyhedron, the permutations of a table) stops there, and its fixture is reported as not evaluated. These fixtures are
listed by module in modules/enumerations.toml, each with the place that stops it; the run fails unless the list is
exactly the fixtures whose check enumerates, so a new fixture whose check enumerates fails and the list only shrinks,
as each enumeration is replaced by a closed form or a symmetry of results.

A fixture's verdict is a function of its own inputs: the fixture file, the statement of its item as it is read
(the item's block of the source text, or its rows for a rule read on the model), the vocabulary that the
statement is read with, and the code of the checker (the files of qpp/ that are loaded when the fixtures run). The
verdict of a passing fixture is kept under the SHA-256 of these inputs in .memo/modfix/NAME.json and in the shared
stores named by MEMO_SHARED (folders separated by the path separator), so that a fixture whose
inputs did not change is not evaluated again, whatever else of the module changed. MEMO=record and MEMO=off (the
daily scan, the tests of the memo) evaluate every fixture.

Usage: python3 -m qpp.modfix NAME
"""
import hashlib
import importlib.util
import json
import os
import re
import runpy
import sys
import tomllib
from pathlib import Path

from . import ctxmodel as CM
from . import enumeration as EN
from . import source as S

ROOT = Path(__file__).resolve().parent.parent
# further fixture folders read with modules/M/fixtures
MOVING = []
LEDGER = ROOT / "modules" / "enumerations.toml"
NOT_EVALUATED = "NOT EVALUATED, its check enumerates: "
# the lines of a source that the checker of test_qpp does not read: the module lines, the sections, the types, and the
# functions that `word NAME(...) : TYPE` and `define` give (the model of qpp/ctxmodel.py reads those)
SOURCE_SKIP = ("module ", "uses ", "application:", "section ", "subsection ", "paragraph ", "type ", "define ")


class _NoPytest:
    """a stand-in for pytest, so that the checker loads where pytest is not installed: its decorators
    (pytest.mark.parametrize(...)) leave the function as it is"""

    def __getattr__(self, name):
        return _NoPytest()

    def __call__(self, *args, **kwargs):
        if len(args) == 1 and callable(args[0]) and not kwargs:
            return args[0]
        return _NoPytest()


def closure(name):
    """the modules that the module uses, directly or not, each after the modules it uses"""
    out = []

    def visit(m):
        for u in S.read_module(m, ROOT).uses:
            if u not in out:
                visit(u)
                out.append(u)
    visit(name)
    return out


def contexts_of(name):
    """the names of the context rows of the module and of the modules it uses"""
    out = set()
    for m in closure(name) + [name]:
        for _, raw in S.read_file(S.module_path(m, ROOT)).vocab:
            if raw.startswith("context "):
                out.add(raw.split(None, 1)[1].split("(")[0].strip())
    return out


# eqfix and neqfix: the kind of the fixture file of each annotation, and the
# status of a row that passes
CHECKS = {"eqfix": ("values", "value"), "neqfix": ("counterexample", "counterexample")}


def run_check(ck, paper, label, ann, key, path):
    """(counts {status: n}, bad [(row, status)]) of the fixture of an eqfix or neqfix line of the row key of label, on
    the statement of the extract, with the functions of the checker ck: every row must be a value (eqfix: the
    hypotheses hold and every side of the equation is the value "=") or a counterexample (neqfix: the hypotheses kept
    hold, the conclusion fails, and one of the hypotheses "drop" fails)"""
    d = json.loads(Path(path).read_text(encoding="utf-8"))
    kind, good = CHECKS[ann]
    if d.get("kind") != kind:
        return {}, [(None, f"an {ann} fixture has kind \"{kind}\"")]
    counts, bad = {}, []
    for row in d.get("rows", []):
        try:
            st = (eq_row if ann == "eqfix" else neq_row)(ck, paper, label, key, d, row)
        except ck["Undecided"] as e:
            st = f"undecided: {e}"
        except ValueError as e:
            st = f"error: {e}"
        counts[st] = counts.get(st, 0) + 1
        if st != good:
            bad.append((row, st))
    if not d.get("rows"):
        bad.append((None, "no row"))
    return counts, bad


def check_setup(ck, paper, label, key, d, row):
    """(env, the parts of the given, the part of the row, whether the paper's context holds) for a row of an eqfix or
    neqfix fixture, read as the checker's check() reads a row"""
    Q, T = ck["Q"], ck["T"]
    vocab = paper.get("vocab") or dict(T.PRELUDE)
    data = {k: v for k, v in row.items() if k != "="}
    env = ck["Env"](vocab, data, d.get("bounds", {}))
    items = ck["items_of"](ck["result"](paper, label), vocab, [key])
    parts = next((ps for k, ps in items if k == key), None)
    if parts is None:
        raise ck["Undecided"](f"no row {key} of {label}")
    i = int(d.get("part", 1))
    if not 1 <= i <= len(parts):
        raise ValueError(f"part {i} of a row of {len(parts)} parts")
    p = parts[i - 1]
    if ck["free_indices"](p, env):
        raise ck["Undecided"]("a part with an index free on both sides")
    ok = all(ck["clause"](c, env) for part in vocab.get("#context", []) for c in Q.context_row(part, set(data), env.types))
    return env, [g for k, ps in items if k == "given" for g in ps], p, ok


def conclusion(ck, p, env):
    """(hypotheses, conclusion, env) of a part, the witness rule applied (hypotheses False: a witness is no integer)"""
    inner = env.child()
    if p[0] in ("imp", "ctx"):
        hyp, rest = ck["witnesses"](p[1], p[2], inner)
        return hyp, rest, inner
    return ("and", ()), p, inner


def eq_row(ck, paper, label, key, d, row):
    if "=" not in row:
        raise ValueError("a row of an eqfix fixture gives the value \"=\"")
    env, given, p, ok = check_setup(ck, paper, label, key, d, row)
    if not ok or not all(ck["context"](g, env) for g in given):
        return "not an instance: the given fails"
    hyp, rest, inner = conclusion(ck, p, env)
    if hyp is False or not ck["context"](hyp, inner):
        return "not an instance: a hypothesis fails"
    while rest[0] == "and" and len(rest[1]) == 1:
        rest = rest[1][0]
    if rest[0] != "rel" or any(op != "=" for op in rest[1]):
        raise ValueError(f"the conclusion {ck['T'].to_qpp(rest)} is not an equation")
    want = ck["num"](row["="])
    vals = [ck["value"](t, inner) for t in rest[2]]
    if all(v == want for v in vals):
        return "value"
    return f"fails: the sides are {', '.join(str(v) for v in vals)}, the value {want}"


def neq_row(ck, paper, label, key, d, row):
    Q, T = ck["Q"], ck["T"]
    drop = d.get("drop")
    drop = [drop] if isinstance(drop, str) else list(drop or [])
    if not drop:
        raise ValueError("a counterexample names the hypotheses it drops (\"drop\")")
    texts = {T.to_qpp(T.parse_qpp(x)) for x in drop}
    env, given, p, ok = check_setup(ck, paper, label, key, d, row)

    def flat(y):
        return [z for c in Q.flatten(y) for z in (flat(c[1]) + flat(c[2]) if c[0] == "ctx" else [c])]
    hyps = [c for g in given for c in flat(g)] + (flat(p[1]) if p[0] in ("imp", "ctx") else [])
    missing = texts - {T.to_qpp(c) for c in hyps}
    if missing:
        raise ValueError(f"not a hypothesis of {label}({key}): {', '.join(sorted(missing))}")
    if not ok:
        return "not a witness: the paper's context fails"
    dropped = []

    def kept(x, e):
        """the clauses of a context but the dropped ones, declarations first (as the checker's context())"""
        cs = flat(x)
        first = [c for c in cs if c[0] == "decl" or Q.family_decl(c) is not None or (
            c[0] == "rel" and c[1] in (("subseteq",), ("subset",)) and c[2][0][0] == "var"
            and c[2][0][1] not in e.vals)]
        out = True
        for c in first + [c for c in cs if not any(c is f for f in first)]:
            if T.to_qpp(c) in texts:
                if any(c is f for f in first) or c[0] == "def":
                    raise ValueError(f"a declaration or a definition is not dropped: {T.to_qpp(c)}")
                dropped.append(c)
            elif out and not ck["clause"](c, e):
                out = False
        return out
    if not all([kept(g, env) for g in given]):
        return "not a witness: a hypothesis kept in the given fails"
    hyp, rest, inner = conclusion(ck, p, env)
    if hyp is False:
        return "not a witness: a witness of the part is no integer"
    if not kept(hyp, inner):
        return "not a witness: a hypothesis kept fails"
    held = [ck["clause"](c, inner.child()) for c in dropped]
    if ck["prop"](rest, inner):
        return "the row meets the statement"
    if all(held):
        return "the statement fails at the row: every hypothesis dropped holds"
    return "counterexample"


VOCAB_HEADS = ("type", "relation", "word", "define", "context", "alias")
KEEP_OLD = 2000  # the verdicts of earlier runs that the file of a module keeps, beside those of this run


def cache_roots():
    """the folders of the kept verdicts: .memo/modfix, and modfix/ in each shared store that MEMO_SHARED names
    (separated by os.pathsep)"""
    shared = [Path(p) for p in os.environ.get("MEMO_SHARED", "").split(os.pathsep) if p]
    return [ROOT / ".memo" / "modfix"] + [r / "modfix" for r in shared]


def cache_on():
    return os.environ.get("MEMO", "on").strip().lower() in ("", "on") and os.environ.get("QPP_MODFIX_CACHE") != "off"


def code_digest():
    """the SHA-256 of the code that reads and checks the fixtures: the files of qpp/ loaded now, and the checker"""
    h = hashlib.sha256()
    files = {Path(m.__file__).resolve() for m in list(sys.modules.values())
             if getattr(m, "__file__", None) and Path(m.__file__).resolve().is_relative_to(ROOT / "qpp")}
    files.add((ROOT / "qpp" / "tests" / "test_qpp.py").resolve())
    for f in sorted(files):
        h.update(f.relative_to(ROOT).as_posix().encode() + b"\0" + f.read_bytes() + b"\0")
    return h.hexdigest()


def blocks(text):
    """{label: the lines of its item} of a Q++ text (the item line and its indented rows), and its vocabulary lines"""
    out, vocab, cur = {}, [], None
    for line in text.splitlines():
        head, _, rest = line.partition(" ")
        if line.startswith(" "):
            if cur is not None:
                out[cur].append(line)
            continue
        cur = None
        if head in S.KINDS and rest.split():
            cur = rest.split()[0]
            out[cur] = [line]
        elif head in VOCAB_HEADS:
            vocab.append(line)
    return {k: "\n".join(v) for k, v in out.items()}, "\n".join(vocab)


def item_text(it):
    """the rows of an item of the source, as the model reads them"""
    return "\n".join([f"{it.kind} {it.label}"] + [f"{r.key}: {r.text}" for r in it.rows])


def fixture_key(*parts, path):
    h = hashlib.sha256()
    for p in parts:
        h.update(str(p).encode() + b"\0")
    h.update(Path(path).read_bytes() if Path(path).is_file() else b"missing")
    return h.hexdigest()


class Verdicts:
    """the verdicts of passing fixtures of a module, by the key of their inputs (fixture_key)"""

    def __init__(self, name):
        self.name, self.on, self.kept, self.used = name, cache_on(), {}, {}
        for root in reversed(cache_roots()) if self.on else []:
            try:
                data = json.loads((root / f"{name}.json").read_text(encoding="utf-8"))
                self.kept.update({k: v for k, v in data.items() if isinstance(v, str)})
            except (OSError, ValueError, AttributeError):
                pass
        self.reused = 0

    def get(self, key):
        line = self.kept.get(key) if self.on else None
        if line is not None:
            self.used[key] = line
            self.reused += 1
        return line

    def put(self, key, line):
        self.used[key] = line

    def save(self):
        """keep the verdicts of this run first, then those of earlier runs up to KEEP_OLD; a write by rename"""
        for root in cache_roots():
            f = root / f"{self.name}.json"
            try:
                old = json.loads(f.read_text(encoding="utf-8")) if f.is_file() else {}
                old = {k: v for k, v in old.items() if k not in self.used and isinstance(v, str)}
            except (OSError, ValueError, AttributeError):
                old = {}
            data = {**self.used, **dict(list(old.items())[:KEEP_OLD])}
            try:
                root.mkdir(parents=True, exist_ok=True)
                tmp = f.with_name(f".{f.name}.{os.getpid()}.tmp")
                tmp.write_text(json.dumps(data, indent=0, sort_keys=False) + "\n", encoding="utf-8")
                os.replace(tmp, f)
            except OSError as e:
                if root == cache_roots()[0]:
                    raise
                print(f"qpp.modfix: cannot write to {root}: {e}", file=sys.stderr)


def source_text(name):
    """the module and the modules it uses, in order, as one text that the checker of test_qpp reads: the Q++ sources
    themselves, without the lines that checker does not read (SOURCE_SKIP, the comments, the functions of a typed
    word), with the title of an item left out, a relation written with :<=>, a cited item as a fact, and the binomial
    coefficient by the name choose (binom(n, k) of the primitives is the same Nat.choose, 0 when k > n)"""
    out = ["-- Q++ 0.1", f"paper {name}"]
    for m in closure(name) + [name]:
        skipping = False
        for raw in S.module_path(m, ROOT).read_text(encoding="utf-8").splitlines():
            if not raw.strip() or raw.strip().startswith("--"):
                continue
            if not raw.startswith(" "):
                skipping = raw.startswith(SOURCE_SKIP) or (raw.startswith("word ") and " := " not in raw)
                if not skipping and " [" in raw and raw.endswith("]"):
                    raw = raw[:raw.index(" [")]
                if raw.startswith("relation "):
                    raw = raw.replace(" := ", " :<=> ", 1)
                elif raw.startswith("cit "):
                    raw = "fact " + raw[4:]
            if not skipping:
                out.append(raw)
    return re.sub(r"(?<![\w.'])binom\(", "choose(", "\n".join(out) + "\n")


def ledger():
    """{module: {fixture id: the place where its check enumerates}} of modules/enumerations.toml"""
    if not LEDGER.is_file():
        return {}
    with LEDGER.open("rb") as f:
        return {m: dict(v) for m, v in tomllib.load(f).items() if isinstance(v, dict)}


def ledger_section(name, skipped):
    """the section of modules/enumerations.toml for the module, from the fixtures of this run"""
    rows = [f"[{name}]"] + [f"{json.dumps(fid)} = {json.dumps(skipped[fid][:200])}" for fid in sorted(skipped)]
    return "\n".join(rows)


def evaluate(skipped, fid, label, run):
    """run() -> (line, bad): the verdict of a check, or NOT_EVALUATED with the place where it enumerates"""
    try:
        return run()
    except EN.Enumerates as e:
        skipped[fid] = str(e)
        return f"{fid} ({label}): {NOT_EVALUATED}{str(e)[:200]}", []


def note_skipped(skipped, fid, line):
    """a kept verdict NOT_EVALUATED counts as this run's"""
    if NOT_EVALUATED in line:
        skipped[fid] = line.split(NOT_EVALUATED, 1)[1]


def main(argv):
    if len(argv) != 1:
        print(__doc__)
        return 2
    name = argv[0]
    src = ROOT / "modules" / name / f"{name}.qpp"
    if not src.is_file():
        print(f"qpp.modfix: no module {name} (modules/NAME/NAME.qpp)")
        return 2
    fixdir = ROOT / "modules" / name / "fixtures"
    # the cited items that need a fixture: a cited statement is a hypothesis of the theorems that use it, unless a
    # mathlib: row names the Mathlib lemma that proves it; a cit with no statement row (a statement of the continuum,
    # in the prose above it) is a hypothesis of no theorem
    contexts = contexts_of(name)
    cits = [it for it in S.read_file(src).items() if it.kind == "cit" and it.row("mathlib") is None
            and any(r.key not in ("given", "origin", "names") for r in it.stmt_rows())]
    # the rules read on the model: a cited rule over a context, on programs or on lattice points, a rule with a
    # fixture that reads a relation as the graph of the model's pair (\"graph\"), a rule with a fixture of the
    # kind model (functions on the counts), and a rule with a row, core rows included, that states the pair of a
    # program, which the checker of the paper does not read
    rules = {it.label: it for it in S.read_file(src).items()
             if CM.on_model(it, contexts) or CM.graph_fixtures(it, fixdir) or CM.model_fixtures(it, fixdir)
             or CM.states_prog(it)}
    unfixed = [it.label for it in cits if not it.fixes]
    if unfixed:
        print(f"qpp.modfix: {name}: cited items with no fix line and no mathlib row: {', '.join(unfixed)}")
        return 1
    items = S.read_file(src).items()
    if not any(it.fixes or it.checks for it in items) and not fixdir.is_dir():
        print(f"qpp.modfix: {name}: no fix line, no fixture")
        return 0
    if importlib.util.find_spec("pytest") is None:
        sys.modules["pytest"] = _NoPytest()  # the checker's file imports pytest for its tests only (pytest is skipped)
    EN.ENUMERATE = False
    checker = runpy.run_path(str(ROOT / "qpp" / "tests" / "test_qpp.py"))
    text = source_text(name)
    paper = checker["Q"].read_qpp(text)
    verdicts, code = Verdicts(name), code_digest()
    extracted, extracted_vocab = blocks(text)
    ok, named, moving, skipped = True, set(), [], {}
    own = S.labels_of_lines(S.read_module(name, ROOT).body)
    for label, item, fid in checker["fixtures_of"](paper):
        if label not in own or label in rules:
            continue  # a fixture of a module it uses (checked by the unit of that module), or of a rule over a context
        named.add(fid)
        dirs = [d for d in [fixdir] + MOVING if d.is_dir()]
        found = [d for d in dirs if (d / f"{fid}.json").exists() or (d / f"{fid}.py").exists()]
        if not found:
            print(f"{fid} ({label} {item or 'all'}): FAILED no file in modules/{name}/fixtures")
            ok = False
            continue
        if found[0] != fixdir:
            moving.append(f"{fid} ({found[0].relative_to(ROOT)})")
        path = checker["fixture_path"](found[0], fid)
        key = fixture_key("paper", label, item, code, extracted.get(label, ""), extracted_vocab, path=path)
        line = verdicts.get(key)
        if line is None:
            def run():
                kind, counts, bad, flags = checker["run_fixture"](paper, label, item, path)
                return (f"{fid} ({label} {item or 'all'}, {kind}): {counts}{' ' + str(flags) if flags else ''} "
                        + ("OK" if not bad else f"FAILED {bad[:3]}")), bad
            line, bad = evaluate(skipped, fid, f"{label} {item or 'all'}", run)
            if not bad:
                verdicts.put(key, line)
            ok = ok and not bad
        note_skipped(skipped, fid, line)
        print(line)
    model_vocab = [v for m in closure(name) + [name] for v in S.read_file(S.module_path(m, ROOT)).vocab]
    model_text = "\n".join(raw for _, raw in model_vocab) + "\n" + " ".join(sorted(contexts))
    model = None

    def the_model():
        nonlocal model
        if model is None:
            model = CM.Model(model_vocab)
        return model
    if rules:
        # the cited rules over a context, on the model of the contexts, with the vocabulary of M and of its uses
        for label, it in rules.items():
            for item, fid, _ in it.fixes:
                named.add(fid)
                path = fixdir / f"{fid}.json"
                if not path.is_file():
                    print(f"{fid} ({label} {item or 'all'}): FAILED no file modules/{name}/fixtures/{fid}.json")
                    ok = False
                    continue
                key = fixture_key("model", label, item, code, item_text(it), model_text, path=path)
                line = verdicts.get(key)
                if line is None:
                    def run():
                        try:
                            kind, counts, bad = CM.run_fixture(the_model(), it, item, path)
                        except ValueError as e:
                            kind, counts, bad = "model", {}, [(None, str(e))]
                        return (f"{fid} ({label} {item or 'all'}, {kind}): {counts} "
                                + ("OK" if not bad else f"FAILED {bad[:3]}")), bad
                    line, bad = evaluate(skipped, fid, f"{label} {item or 'all'}", run)
                    if not bad:
                        verdicts.put(key, line)
                    ok = ok and not bad
                note_skipped(skipped, fid, line)
                print(line)
    for it in items:
        # the values and the counterexamples of the module (eqfix, neqfix), on the statement of the extract
        for ann, key, fid, _ in it.checks:
            named.add(fid)
            path = fixdir / f"{fid}.json"
            if not path.is_file():
                print(f"{fid} ({it.label} {key}, {ann}): FAILED no file modules/{name}/fixtures/{fid}.json")
                ok = False
                continue
            if it.label in rules:
                vkey = fixture_key("check-model", it.label, ann, key, code, item_text(it), model_text, path=path)
            else:
                vkey = fixture_key("check-paper", it.label, ann, key, code, extracted.get(it.label, ""),
                                   extracted_vocab, path=path)
            line = verdicts.get(vkey)
            if line is None:
                def run():
                    if it.label in rules:
                        # a rule read on the model (over a context, on programs, on lattice points): its values and
                        # its counterexamples there
                        counts, bad = CM.run_check(the_model(), it, ann, key, path)
                    else:
                        counts, bad = run_check(checker, paper, it.label, ann, key, path)
                    return f"{fid} ({it.label} {key}, {ann}): {counts} " + ("OK" if not bad else f"FAILED {bad[:3]}"), bad
                line, bad = evaluate(skipped, fid, f"{it.label} {key}, {ann}", run)
                if not bad:
                    verdicts.put(vkey, line)
                ok = ok and not bad
            note_skipped(skipped, fid, line)
            print(line)
    if fixdir.is_dir():
        orphans = sorted(p.stem for p in fixdir.iterdir() if p.suffix in (".json", ".py") and p.stem not in named)
        if orphans:
            print(f"qpp.modfix: {name}: fixtures that no fix line names: {', '.join(orphans)}")
            ok = False
    if moving:
        print(f"qpp.modfix: {name}: {len(moving)} fixtures still in the folder of a paper: {', '.join(moving)}")
    listed = ledger().get(name, {})
    new, gone = sorted(set(skipped) - set(listed)), sorted(set(listed) - set(skipped))
    if new:
        print(f"qpp.modfix: {name}: fixtures whose check enumerates, which modules/enumerations.toml does not list (a "
              f"check reads the row at the numbers of its fixture, never the points of a set): {', '.join(new)}")
    if gone:
        print(f"qpp.modfix: {name}: entries of modules/enumerations.toml whose check does not enumerate (the list only "
              f"shrinks: remove them): {', '.join(gone)}")
    if new or gone:
        print("qpp.modfix: the section of this run:\n" + ledger_section(name, skipped))
        ok = False
    if ok:
        verdicts.save()
    print(f"qpp.modfix: {name}: {len(named)} fixtures, {len(skipped)} not evaluated (their check enumerates, "
          f"modules/enumerations.toml), {verdicts.reused} verdicts reused (their inputs unchanged), "
          f"{'OK' if ok else 'FAILED'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
