"""The closer chains `first | a | b | ...` of a generated Lean file, cut to the alternatives that closed them in the last
run of Lean, or reordered with the winner first.

The generator closes a step with a chain of tactics that Lean tries in order until one closes the goal: a search, at
build time, for a closing tactic. Lean pays for every alternative that fails before the one that closes, and the text
of the alternatives that never run can be most of a generated file. A table of the winners, written once from a run of Lean and read by the generator,
replaces the search by its result:

* For a file of the Q++ modules (QppModules.M), each chain that ran is cut to its winners: `first | a | b | c` whose
  winner was c is emitted `first | c`. A chain that ran on several goals (under `all_goals` or `<;>`) keeps the winner
  of each, in their order, and each goal is closed by the same alternative as before, the ones before it having failed
  on it. A chain that did not run is kept whole. The statements, the theorems and the axiom audit do not change; only
  the proof text does, to the steps that Lean took.
* A hedge `try t` of a file of the Q++ modules is the chain `first | t | skip` that Lean defines it as, and is written
  so before the run (try_chains): cut, it is `(t)` where t won on every goal it ran on, `skip` where it failed
  on every one, and `try t` where it did both or did not run (a declaration that is not cut keeps its `try` too).
* For another file (the examples, which exercise every alternative the generator writes), the winner is moved to the
  front: `first | c | a | b`, the other alternatives kept in their order.
* The key of a chain is its declaration, the hash of the declaration's text as the generator writes it (the chains
  in their own order, the comments left out: a docstring carries the line of its source), and its ordinal among the
  chains of the declaration, counted in the order of the text, a chain before the chains inside it. A cut declaration
  also keys on the statements it reads: the statement of each declaration of the file and each definition of the
  modules it uses that it names, and what those name in turn (dependencies). A declaration whose key changed is
  emitted as the generator writes it, with all its alternatives, until the table is refreshed: larger and slower,
  never wrong. What the key does not see (a lemma of a used module whose statement changed under an unchanged call
  and an unchanged definition, a change of the bridge or of the kernel words) can fail a cut chain; the refresh then
  cuts it again.
* The table of a generated file is qpp/closers/MODULE.json (MODULE the Lean module, QppModules.Theory), with the
  toolchain and the Mathlib revision of the run; a table of another toolchain or revision is not read.

`python3 -m qpp.closers refresh FILE MODULE` refreshes the table of a generated file: it writes the file again with
every alternative (a file of the Q++ modules by qpp/modlean.py with QPP_CLOSERS=0), runs Lean on a copy whose chains
log their winner (the tactic qfirst below), writes the table and rewrites the file from it; the generator writes the
same file from the same sources (qpp/modlean.py cuts the files of the modules as it writes them; the units of the files
that qpp/kernel.py writes run `python3 -m qpp.closers apply FILE MODULE` after it). `python3 -m qpp.closers check FILE
MODULE` prints how many declarations of the table are current and how many are stale (their text changed since the
table was written). QPP_CLOSERS=0 writes the chains whole, in the generator's order.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TABLES = ROOT / "qpp" / "closers"
LEAN = ROOT / "lean"
OPEN, CLOSE = "([{\u27e8", ")]}\u27e9"
FIRST = re.compile(r"(?<![\w.'\u2080-\u2089!?])first(?=\s*\|(?![|>]))")
DECL = re.compile(r"^(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|noncomputable|public|partial|unsafe|nonrec)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|example|opaque|axiom|class)\b"
                  r"(?:\s+([^\s:({\[]+))?", re.M)
THEOREM = re.compile(r"(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|public|nonrec)\s+)*(?:theorem|lemma)\b")


class Chain:
    """a chain `first | ...`: its alternatives, each a list of parts (text and nested chains), and the text around
    each alternative (the separator before it, with its `|`, and the blank after it)"""

    def __init__(self):
        self.seps, self.alts, self.trails = [], [], []

    def render(self, order=None):
        alts = [render(a, order) for a in self.alts]
        perm = order(self) if order else None
        mode = try_mode(self, perm)
        if mode == "try":
            return "try " + alts[0]  # t closed some goals and failed on others, as try reads
        if mode == "only":
            return alts[0]  # t, which closed or changed every goal it ran on
        if mode == "skip":
            return "skip"  # t failed on every goal it ran on
        if perm:
            alts = [alts[i] for i in perm]
        return "first" + "".join(s + a + t for s, a, t in zip(self.seps, alts, self.trails))


def try_mode(chain, perm):
    """how a chain `first | t | skip` (a try, try_chains) is written once cut by perm: "try" (both won), "only" (t
    alone), "skip" (skip alone); None for another chain or one not cut"""
    if not perm or not is_try(chain):
        return None
    return {(0, 1): "try", (0,): "only", (1,): "skip"}.get(tuple(perm))


def render(parts, order=None):
    return "".join(p if isinstance(p, str) else p.render(order) for p in parts)


def skip_comment(s, i):
    """the end of a comment or a string that starts at i, or i"""
    if s.startswith("--", i):
        j = s.find("\n", i)
        return len(s) if j < 0 else j
    if s.startswith("/-", i):
        depth, j = 0, i
        while j < len(s):
            if s.startswith("/-", j):
                depth, j = depth + 1, j + 2
            elif s.startswith("-/", j):
                depth, j = depth - 1, j + 2
                if depth == 0:
                    return j
            else:
                j += 1
        return len(s)
    if s[i] == '"':
        j = i + 1
        while j < len(s) and s[j] != '"':
            j += 2 if s[j] == "\\" else 1
        return j + 1
    return i


def parse(s, i=0, in_chain=False, col=0):
    """the parts of s from i: text, and the chains in it, up to the end of s, or (in an alternative of a chain) up to
    the `|` of the next alternative, the end of the line that does not go on with one (a line that starts with `|` at
    the column col of the first `|` of the chain or further right, as Lean reads `first`), or a closing bracket that
    closes nothing opened here; returns (parts, end)"""
    parts, start, depth, j = [], i, 0, i
    while j < len(s):
        k = skip_comment(s, j)
        if k != j:
            j = k
            continue
        c = s[j]
        m = FIRST.match(s, j) if c == "f" else None
        if m:
            parts.append(s[start:j])
            chain, j = parse_chain(s, m.end())
            parts.append(chain)
            start = j
            continue
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            if depth == 0 and in_chain:
                break
            depth = max(depth - 1, 0)
        elif in_chain and depth == 0:
            if c == "|" and s[j + 1:j + 2] not in ("|", ">") and s[j - 1:j] not in ("<", "|"):
                break
            if c == "\n":
                more = re.match(r"([ \t]*)\|(?![|>])", s[j + 1:j + 1 + 4096])
                if not more or len(more.group(1)) < col:
                    break
        j += 1
    parts.append(s[start:j])
    return [p for p in parts if not isinstance(p, str) or p], j


TRY = re.compile(r"(?<![\w.'\u2080-\u2089!?])try(?=[ \t]+\S)")


def try_chains(s):
    """s with each `try t` written as the chain `(first | t | skip)`, which it is (Lean defines try so), so that the
    table cuts it to its winner like any other chain: t where it closed or changed its goal, skip where it failed.
    Its extent is that of an alternative of a chain: up to a `|` of the chain it is in, the end of its line, or
    a closing bracket that closes nothing opened in it, as Lean reads the tactic sequence after `try`"""
    out, start, j = [], 0, 0
    while j < len(s):
        k = skip_comment(s, j)
        if k != j:
            j = k
            continue
        m = TRY.match(s, j) if s[j] == "t" else None
        if m:
            lead = re.compile(r"[ \t]*").match(s, m.end()).end()
            _, end = parse(s, lead, in_chain=True, col=1 << 30)
            body = s[lead:end].rstrip(" \t")
            out += [s[start:j], f"(first | {try_chains(body)} | skip)", s[lead + len(body):end]]
            j = start = end
            continue
        j += 1
    out.append(s[start:])
    return "".join(out)


def parse_chain(s, i):
    """the chain whose word `first` ends at i; returns (chain, end)"""
    chain, j, col = Chain(), i, None
    while True:
        m = re.compile(r"\s*\|(?![|>])").match(s, j)
        if not m:
            break
        sep_end = m.end()
        if col is None:
            col = sep_end - 1 - (s.rfind("\n", 0, sep_end - 1) + 1)
        lead = re.compile(r"[ \t]*").match(s, sep_end).end()
        body, k = parse(s, lead, in_chain=True, col=col)
        text = render(body)
        trail = len(text) - len(text.rstrip(" \t"))
        if trail:
            # the blank before the next `|` belongs to the separator, not to the alternative
            last = body[-1]
            if isinstance(last, str):
                body[-1] = last[:len(last) - trail]
                body = [p for p in body if not isinstance(p, str) or p]
            else:
                trail = 0
        chain.seps.append(s[j:lead])
        chain.alts.append(body)
        chain.trails.append(s[k - trail:k] if trail else "")
        j = k
        if k >= len(s) or s[k] != "|":
            break
    if not chain.alts:
        raise ValueError(f"qpp.closers: no alternative after `first` at {i}")
    return chain, j


def walk(parts):
    """the chains of parts, a chain before the chains inside it, in the order of the text"""
    for p in parts:
        if isinstance(p, Chain):
            yield p
            for a in p.alts:
                yield from walk(a)


def declarations(s):
    """(name, start, end) of each declaration of a Lean text, from its header to the next one"""
    heads = [(m.start(), m.group(1) or f"_{m.start()}") for m in DECL.finditer(s)]
    names = {}
    out = []
    for (a, name), (b, _) in zip(heads, heads[1:] + [(len(s), None)]):
        n = names[name] = names.get(name, 0) + 1
        out.append((name if n == 1 else f"{name}#{n}", a, b))
    return out


def theorem(text):
    """whether a declaration is a theorem: only the proof of a proposition may close its steps in another order (a
    definition could take another value)"""
    return THEOREM.match(text) is not None


SPECIAL = re.compile(r'--|/-|"')


def code(text):
    """a Lean text without its comments (strings kept)"""
    out, i = [], 0
    while True:
        m = SPECIAL.search(text, i)
        if not m:
            out.append(text[i:])
            return "".join(out)
        out.append(text[i:m.start()])
        j = skip_comment(text, m.start())
        if text[m.start()] == '"':
            out.append(text[m.start():j])
        elif text.startswith("/- qpp:V ", m.start()):
            # the mark of a step in a copy of qpp/certx.py, a line of its own: left out with the line break and the
            # indent after it, so that the copy keys as the module's Lean
            j = re.compile(r"\n[ \t]*").match(text, j).end() if text.startswith("\n", j) else j
        i = j


def digest(text):
    """the key of a declaration: the hash of its text without comments, since the docstrings that the generator
    writes carry the line of the source, which moves with any edit above it"""
    return hashlib.sha256(code(text).encode("utf-8")).hexdigest()[:16]


def toolchain():
    """the toolchain and the Mathlib revision of lean/, which a table is valid for"""
    lean = (LEAN / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest = json.loads((LEAN / "lake-manifest.json").read_text(encoding="utf-8"))
    rev = next((p["rev"] for p in manifest.get("packages", []) if p.get("name") == "mathlib"), "none")
    return lean, rev


def table_path(module):
    return TABLES / f"{module}.json"


def read_table(module):
    """the entries of the table of module, {declaration: entry}, or {} (no table, or one of another toolchain or
    Mathlib revision). An entry has the hash of the declaration as the generator writes it ("hash"), and either the
    winner of each chain whose winner is not its first alternative ("first": {ordinal: winner}, the chains reordered)
    or the winners of every chain that ran ("won": {ordinal: [winners]}, the chains cut to them), with the hash of the
    statements it reads ("deps", dependencies) and the hash of its text once cut ("cut")"""
    try:  # opened, not tested with is_file: a traced run (tools/memo.py) records a missing table as an input too
        data = json.loads(table_path(module).read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}
    if [data.get("lean"), data.get("mathlib")] != list(toolchain()):
        return {}
    out = {}
    for d, e in data.get("decls", {}).items():
        out[d] = {"hash": e["hash"], "first": {int(k): v for k, v in e.get("first", {}).items()},
                  "won": {int(k): list(v) for k, v in e["won"].items()} if "won" in e else None,
                  "deps": e.get("deps"), "cut": e.get("cut")}
    return out


IDENT = re.compile(r"[A-Za-z_][\w.'\u2080-\u2089!?]*")
NAMESPACES = ("QppMathlib.", "Qpp.Modules.", "Qpp.Examples.", "QppMathlib.Examples.")


def statement(text):
    """the part of a declaration that other declarations read: a theorem up to its proof, a definition whole"""
    if theorem(text):
        m = re.search(r":=\s*by\b|:=", text)
        return text[:m.start()] if m else text
    return text


def dependencies(text, context=""):
    """the hash of what each theorem of a generated file reads from the other declarations: the statement of each
    declaration it names (a theorem up to its proof, a definition whole), in the file or in context (the files of the
    modules it uses, as their generator writes them: one text, or a list of them), and what those name in turn; so that a
    chain cut to its winners is not kept when a lemma it applies changed its statement and its own text did not"""
    body = {name: bare(code(text[a:b])) for name, a, b in declarations(text)}
    seen_names = {}
    for part in ([context] if isinstance(context, str) else context):
        # each used module on its own (context: its text, or the list of the texts of the modules it uses), so that
        # the last declaration of one module does not run into the header of the next
        for name, a, b in declarations(part):
            # numbered across the modules, as in one text: a name that two modules declare is name#2 in the second
            base_name = name.split("#")[0]
            n = seen_names[base_name] = seen_names.get(base_name, 0) + 1
            key = base_name if n == 1 else f"{base_name}#{n}"
            # the definitions of the modules it uses, and none of their theorems: a used module is generated with its
            # theorems or without them (qpp/modlean.py keeps the rows it proved), and its statements are definitions
            # (X.statement, read through the theorem X it names, and the definition X of a theorem X_iff)
            if not theorem(part[a:b]):
                body[f"ctx:{key}"] = bare(code(part[a:b]))
    base = {}
    for name in body:
        base.setdefault(name.removeprefix("ctx:").split("#")[0], []).append(name)

    def named(t, own):
        out = set()
        for tok in set(IDENT.findall(t)):
            for cand in [tok] + [tok[len(ns):] for ns in NAMESPACES if tok.startswith(ns)]:
                for key in base.get(cand, ()):
                    if key != own:
                        out.add(key)
        return out
    stmts = {name: statement(t) for name, t in body.items()}
    heads = {}
    out = {}
    for name, t in body.items():
        if name.startswith("ctx:") or not theorem(t):
            continue
        todo = list(named(t, name))
        for tok in set(IDENT.findall(t)):
            # a theorem of a used module (not in body): its statement, and the definition it unfolds
            for cand in [tok] + [tok[len(ns):] for ns in NAMESPACES if tok.startswith(ns)]:
                if cand not in base:
                    todo += base.get(cand + ".statement", []) + base.get(cand.removesuffix("_iff"), [])
        seen = set()
        while todo:
            x = todo.pop()
            if x in seen or x == name:
                continue
            seen.add(x)
            if x not in heads:
                heads[x] = named(stmts[x], x)
            todo += list(heads[x]) + base.get(x.removeprefix("ctx:").split("#")[0] + ".statement", [])
        h = hashlib.sha256("".join(f"{x.removeprefix('ctx:')}\0{stmts[x]}\0" for x in sorted(seen)).encode("utf-8"))
        out[name] = h.hexdigest()[:16]
    return out


def bare(text):
    """a declaration without the namespace lines that follow it (the last one before `end N`, as declarations cuts)"""
    return re.sub(r"(?:\s*^(?:end|namespace) [^\n]*$)+\s*\Z", "", text, flags=re.M).rstrip() + "\n"


def cut(parts, won, ordinal):
    """the order of each chain of parts that ran: its winners, in their order (a chain that ran on several goals keeps
    the winner of each, and each goal is closed by the same alternative as before, the ones before it having failed on
    it); a chain that did not run is kept whole"""
    def perm(chain):
        w = won.get(ordinal[id(chain)])
        if w and all(0 <= i < len(chain.alts) for i in w):
            return list(w)
        return [0, 1] if is_try(chain) else None  # a try that did not run: written as the generator wrote it
    return perm


def is_try(chain):
    """whether a chain is a try written as a chain, `first | t | skip` (try_chains)"""
    return len(chain.alts) == 2 and render(chain.alts[1]).strip() == "skip"


def untry(text):
    """a declaration with each try that try_chains wrote as a chain written as a try again (a declaration that the
    table does not cut keeps the count of its hedges as the generator wrote them)"""
    parts, _ = parse(text)
    return render(parts, lambda c: [0, 1] if is_try(c) else None)


def shape(parts, perm=None):
    """the number of alternatives of each chain of parts, in the order of walk, once each chain is cut by perm"""
    out = []
    for p in parts:
        if isinstance(p, Chain):
            cut_ = perm(p) if perm else None
            mode = try_mode(p, cut_)
            if mode is not None:
                # a try written as try t, t or skip (Chain.render): no chain of its own, the chains of t kept
                out += shape(p.alts[0], perm) if mode != "skip" else []
                continue
            idx = cut_ or range(len(p.alts))
            out.append(len(idx))
            for i in idx:
                out += shape(p.alts[i], perm)
    return out


def front(n, w):
    """the order of n alternatives with the alternative w first"""
    return [w] + [i for i in range(n) if i != w]


def movable(chain, w):
    """whether the alternative w of a chain can go first: not the first already, and not a chain written without
    parentheses (`first | a | first | b | c`, whose inner chain takes the alternatives after it: put first, it would
    take them all)"""
    return w is not None and 0 < w < len(chain.alts) and not isinstance(chain.alts[w][0], Chain)


def restore(text, moves):
    """the text of a declaration as the generator wrote it, from its text with the winners of moves first; with the
    number of chains counted"""
    parts, _ = parse(text)
    back, n = {}, 0

    def number(parts):
        # the ordinals of the generator's text: put back from the outside in, so that the chains inside a moved
        # alternative are counted where the generator wrote them
        nonlocal n
        for p in parts:
            if isinstance(p, Chain):
                w = moves.get(n)
                n += 1
                alts = p.alts
                if w is not None and 0 < w < len(alts):
                    inv = front(len(alts), w)
                    alts = [None] * len(alts)
                    for at, src in enumerate(inv):
                        alts[src] = p.alts[at]
                    if isinstance(alts[w][0], Chain):
                        alts = p.alts       # not moved by order (movable)
                    else:
                        back[id(p)] = [inv.index(i) for i in range(len(inv))]
                for alt in alts:
                    number(alt)
    number(parts)
    return render(parts, lambda c: back.get(id(c))), n


def order(text, module, table=None, context=""):
    """the text of a generated file with each chain of the table cut to its winners (an entry "won") or with its
    winner first (an entry "first"). A declaration is left as it is when its hash is not the table's, when the
    statements it reads changed (an entry "won"), or when its text so written does not read back as the same chains
    (a guard: a chain is read as Lean reads it, or not touched)"""
    if os.environ.get("QPP_CLOSERS", "1") == "0":
        return text
    table = read_table(module) if table is None else table
    if not table:
        return text
    deps = dependencies(text, context) if any(e["won"] is not None for e in table.values()) else {}
    out, pos = [], 0
    for name, a, b in declarations(text):
        entry = table.get(name)
        if not entry or entry["hash"] != digest(text[a:b]) or not theorem(text[a:b]):
            out += [text[pos:a], untry(text[a:b])]
            pos = b
            continue
        parts, _ = parse(text[a:b])
        ordinal = {id(c): n for n, c in enumerate(walk(parts))}
        if entry["won"] is not None:
            if entry["deps"] != deps.get(name):
                out += [text[pos:a], untry(text[a:b])]
                pos = b
                continue
            perm = cut(parts, entry["won"], ordinal)
            put = render(parts, perm)
            if shape(parse(put)[0]) != shape(parts, perm):
                out += [text[pos:a], untry(text[a:b])]
                pos = b
                continue
        else:
            moves = entry["first"]

            def perm(chain, moves=moves, ordinal=ordinal):
                w = moves.get(ordinal[id(chain)])
                return front(len(chain.alts), w) if movable(chain, w) else None
            put = render(parts, perm)
            if restore(put, moves) != (text[a:b], len(ordinal)):
                continue
        out.append(text[pos:a])
        out.append(put)
        pos = b
    out.append(text[pos:])
    return "".join(out)


def canonical(text, module):
    """the text that the generator wrote before order: each declaration of the table whose winners were moved to the
    front is put back, if the hash of the text put back is the hash of the table. A chain cut to its winners cannot be
    put back: the file of a table with cut chains is written again by its generator with QPP_CLOSERS=0 (refresh)"""
    table = read_table(module)
    out, pos = [], 0
    for name, a, b in declarations(text):
        entry = table.get(name)
        if not entry or entry["won"] is not None:
            continue
        put, _ = restore(text[a:b], entry["first"])
        if digest(put) == entry["hash"]:
            out.append(text[pos:a])
            out.append(put)
            pos = b
    out.append(text[pos:])
    return "".join(out)


QFIRST = r'''
open Lean Elab Tactic in
/-- `first`, which also logs the alternative that closed the goal (qpp/closers.py) -/
syntax (name := qfirst) "qfirst " num withPosition((ppDedent(ppLine) colGe "| " tacticSeq)+) : tactic

open Lean Elab Tactic in
@[tactic qfirst] partial def evalQfirst : Tactic := fun stx => do
  let id := stx[1].isNatLit?.getD 0
  let alts := stx[2].getArgs.map (fun a => a[1])
  let rec loop (i : Nat) : TacticM Unit := do
    if h : i < alts.size then
      let s <- saveState
      try
        if i + 1 < alts.size then Term.withoutErrToSorry (withoutRecover (evalTactic alts[i]))
        else evalTactic alts[i]
        logInfo m!"QPP-CLOSER {id} {i}"
      catch e =>
        s.restore
        if i + 1 < alts.size then loop (i + 1) else throw e
    else throwError "qfirst: no alternative"
  loop 0

'''


def instrument(text, start=0, qfirst=True):
    """a copy of a generated file for a run of Lean outside the module system, whose chains log their winner (numbered
    from start + 1; the tactic qfirst defined in it when qfirst, else read from an import); returns
    (text, {id: (declaration, ordinal)})"""
    ids, out, pos, n = {}, [], 0, start
    for name, a, b in declarations(text):
        parts, _ = parse(text[a:b])
        chains = list(walk(parts))
        local = {id(c): k for k, c in enumerate(chains)}
        tags = {}
        for c in chains:
            n += 1
            tags[id(c)] = n
            ids[n] = (name, local[id(c)])

        def tag(parts):
            return "".join(p if isinstance(p, str) else
                           f"qfirst {tags[id(p)]}" + "".join(s + tag(alt) + t for s, alt, t in zip(p.seps, p.alts,
                                                                                                     p.trails))
                           for p in parts)
        out.append(text[pos:a])
        out.append(tag(parts))
        pos = b
    out.append(text[pos:])
    body = "".join(out)
    body = re.sub(r"\Amodule\n", "", body)
    body = re.sub(r"(?m)^public import ", "import ", body)
    body = body.replace("@[expose] public section\n", "")
    first_decl = body.find("\n/-!")
    first_decl = first_decl if first_decl >= 0 else body.find("\nnamespace ")
    return body[:first_decl] + "\n" + (QFIRST if qfirst else "") + body[first_decl:], ids


def base(name):
    """a name of declarations without its count (name#2: name) and an unnamed declaration without its position"""
    return re.sub(r"#\d+\Z", "", re.sub(r"\A_\d+\Z", "_", name))


def run_instrumented(text, module):
    """(log, ids): Lean run on the instrumented copy of a generated text; a file of the Q++ modules in the parts that
    qpp/modlean.py writes it in, each compiled by its own Lean process importing the part before (QppClosers.PartK, in a
    temporary folder), so that the run takes the memory of a part, not of the file"""
    name = module_name(module)
    if name is None:
        parts = [(text, "")]
    else:
        from . import modlean
        parts = modlean.split(text)
    # the ids are those of the whole text: a name that comes back (the same row over Mathlib and over the kernel) is
    # name#2 there, and may be the first of its part
    _, ids = instrument(text)
    logs, start = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "QppClosers").mkdir()
        for i, (header, body) in enumerate(parts, 1):
            copy, got = instrument(header + body, start=start, qfirst=i == 1)
            start += len(got)
            if any(n not in ids or ids[n][1] != k or base(ids[n][0]) != base(d) for n, (d, k) in got.items()):
                raise SystemExit(f"qpp.closers: the chains of part {i} of {module} are not those of the whole text")
            if i > 1:
                copy = re.sub(r"(?m)^(import [^\n]*\n)(?![\s\S]*^import )",
                              lambda m: m.group(1) + f"import QppClosers.Part{i - 1}\n", copy, count=1)
            f = root / "QppClosers" / f"Part{i}.lean"
            f.write_text(copy, encoding="utf-8")
            if len(parts) == 1:
                cmd = ["lake", "env", "lean", str(f)]
            else:
                cmd = ["lake", "env", "sh", "-c", 'LEAN_PATH="$LEAN_PATH:$0" exec lean -R "$0" -o "$1" "$2"',
                       str(root), str(f.with_suffix(".olean")), str(f)]
            run = subprocess.run(cmd, cwd=LEAN, capture_output=True, text=True)
            log = run.stdout + run.stderr
            logs.append(log)
            # an error, or a declaration that error recovery closed with sorry (an error inside the last alternative of
            # a chain may leave only the warning): the run is no record of the winners
            errors = [line for line in log.splitlines() if ": error:" in line or "declaration uses `sorry`" in line]
            if run.returncode != 0 or errors:
                print("\n".join(errors[:20]) or log[-4000:], file=sys.stderr)
                raise SystemExit(f"qpp.closers: part {i} of {len(parts)} of the instrumented copy of {module} failed; "
                                 "the table is not written")
            print(f"qpp.closers: {module}: part {i} of {len(parts)} ran", flush=True)
    if start != len(ids):
        raise SystemExit(f"qpp.closers: the parts of {module} have {start} chains, the whole text {len(ids)}")
    return "\n".join(logs), ids


def source(m):
    """the file of the repository of the Lean module m (lean/ or qpp/lean/), or None"""
    for base in (LEAN, ROOT / "qpp" / "lean"):
        f = base / (m.replace(".", "/") + ".lean")
        if f.is_file():
            return f
    return None


def imports(text):
    """the modules of the repository that a generated file imports (built before the run); the files of all the
    modules it imports, directly or not, are read, so that a traced run (tools/memo.py) records them as its inputs"""
    names = re.findall(r"(?m)^(?:public )?import (\S+)", text)
    direct = [m for m in names if source(m)]
    seen, todo = set(), list(direct)
    while todo:
        m = todo.pop()
        if m not in seen:
            seen.add(m)
            todo += [n for n in re.findall(r"(?m)^(?:public )?import (\S+)", source(m).read_text(encoding="utf-8"))
                     if source(n)]
    return direct


def generator_text(path, module):
    """(text, context): the text of a generated file as its generator writes it, before order, and the texts of the
    modules it uses. A file of the Q++ modules (QppModules.M) is generated again by qpp/modlean.py with QPP_CLOSERS=0 (a
    file whose chains are cut cannot be put back); another file is read with its moved winners put back (canonical)"""
    name = module_name(module)
    if name is None:
        return canonical(read(path, module), module), ""
    from . import modlean
    saved = {k: os.environ.get(k) for k in ("QPP_CLOSERS", "QPP_LEAN_PART")}
    os.environ.update(QPP_CLOSERS="0", QPP_LEAN_PART="0")
    try:
        modlean.PART = 0
        if modlean.main([name]) != 0:
            raise SystemExit(f"qpp.closers: qpp/modlean.py {name} failed")
    finally:
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        modlean.PART = int(os.environ.get("QPP_LEAN_PART", "1500000"))
    return modlean.TEXTS[name]


def module_name(module):
    """the Q++ module of a Lean module of the Q++ modules (QppModules.Table: table), or None"""
    if not module.startswith("QppModules."):
        return None
    from . import modlean
    return next((m for m in modlean.names() if f"QppModules.{modlean.camel(m)}" == module), None)


def write(path, module, text):
    """write a generated file as qpp/modlean.py writes it, in parts past its size"""
    name = module_name(module)
    from . import modlean
    if name is None:
        modlean.write_parts(Path(path), module, text)
    else:
        modlean.write_lean(name, text)


def read(path, module):
    """a generated file as one text (the parts of a file of the Q++ modules joined)"""
    name = module_name(module)
    from . import modlean
    return modlean.read_parts(Path(path)) if name is None else modlean.read_lean(name)


def refresh(path, module):
    """run Lean on the instrumented copy of the file and write the table of its winners; then the file in the new
    order. A file of the Q++ modules (QppModules.M) gets the winners of every chain that ran, and its chains are cut
    to them; another file (the examples, which exercise every alternative the generator writes) gets the winners that
    are not the first alternative, moved to the front"""
    path = Path(path)
    prune = module.startswith("QppModules.")
    text, context = generator_text(path, module)
    deps = imports(text)
    if deps:
        subprocess.run(["lake", "build", *deps], cwd=LEAN, check=True)
    log, ids = run_instrumented(text, module)
    won = {}
    for m in re.finditer(r"QPP-CLOSER (\d+) (\d+)", log):
        won.setdefault(int(m.group(1)), set()).add(int(m.group(2)))
    decls = {}
    hashes = {name: digest(text[a:b]) for name, a, b in declarations(text)}
    theorems = {name: text[a:b] for name, a, b in declarations(text)}
    chains = {}
    for name, a, b in declarations(text):
        for k, c in enumerate(walk(parse(text[a:b])[0])):
            chains[(name, k)] = c
    for n, (name, k) in sorted(ids.items()):
        w = won.get(n)
        if not w or not theorem(theorems[name]):
            continue
        if prune:
            decls.setdefault(name, {"hash": hashes[name], "won": {}})["won"][str(k)] = sorted(w)
        elif len(w) == 1 and movable(chains[(name, k)], min(w)):
            decls.setdefault(name, {"hash": hashes[name], "first": {}})["first"][str(k)] = min(w)
    if prune:
        dep = dependencies(text, context)
        for name, e in decls.items():
            e["deps"] = dep.get(name)
            parts, _ = parse(theorems[name])
            ordinal = {id(c): j for j, c in enumerate(walk(parts))}
            e["cut"] = digest(render(parts, cut(parts, {int(j): v for j, v in e["won"].items()}, ordinal)))
    lean, rev = toolchain()
    TABLES.mkdir(parents=True, exist_ok=True)
    # one line per declaration, so that a change of the proofs of a row changes the lines of its declarations only
    rows = ",\n".join(f"  {json.dumps(d)}: {json.dumps(e, separators=(',', ':'))}" for d, e in sorted(decls.items()))
    table_path(module).write_text(f'{{\n "lean": {json.dumps(lean)},\n "mathlib": {json.dumps(rev)},\n "decls": {{\n'
                                  f'{rows}\n }}\n}}\n', encoding="utf-8")
    put = order(text, module, context=context)
    write(path, module, put)
    moved = sum(len(e.get("first", {})) for e in decls.values())
    kept = sum(len(e.get("won", {})) for e in decls.values())
    print(f"qpp.closers: {path.relative_to(ROOT) if path.is_absolute() else path}: {len(ids)} chains, "
          f"{len(won)} ran, " + (f"{kept} cut to their winners; {len(text.encode())} bytes before, "
                                 f"{len(put.encode())} after" if prune else
                                 f"{moved} with a winner after the first alternative") +
          f"; table {table_path(module).relative_to(ROOT)}")


def check(path, module):
    """how many declarations of the table are current: their text now is the text the table was written from, or
    that text cut to its winners"""
    text = canonical(read(path, module), module)
    table = read_table(module)
    hashes = {name: digest(text[a:b]) for name, a, b in declarations(text)}
    current = sum(1 for d, e in table.items() if hashes.get(d) in (e["hash"], e["cut"]))
    print(f"qpp.closers: {path}: {len(table)} declarations in the table, {current} current, "
          f"{len(table) - current} stale")
    return 0


def apply(path, module):
    """rewrite a generated file with the winners of its table first (for the files that qpp/kernel.py writes, whose
    units run this after it; qpp/modlean.py orders the files of the modules itself)"""
    text = read(path, module)
    put = order(canonical(text, module), module)
    if put != text:
        write(path, module, put)


def main(argv):
    commands = {"refresh": refresh, "check": check, "apply": apply}
    if len(argv) == 3 and argv[0] in commands:
        return commands[argv[0]](argv[1], argv[2]) or 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
