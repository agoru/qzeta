# Q++: the source language of the modules

Q++ is the language of the modules of `modules/`. A module `modules/NAME/NAME.qpp` states results over the counts
(the positive integers) and the masses (the positive rationals) as the rows of its items, proves each row by a word
of proof steps, and names the fixtures that test its rows. A module holds no Lean and no LaTeX: both are generated
from it.

    modules/NAME/NAME.qpp  --qpp.modlean-->  lean/QppModules/Name.lean   each row over Mathlib, then over the kernel
                           --qpp.modfix--->  modules/NAME/fixtures/      each fixture checked on its row, exactly
                           --qpp2latex---->  LaTeX                       read back by latex2qpp as the same rows

This file is the reference of the language and of its tools: the kernel and the bridge, the source, the generator,
the printers, the fixtures and the checks of the generated Lean.

## The kernel and the bridge

The statements of the modules are written over the words of the kernel, `qpp/lean/QppKernel`, on Lean core alone
(no Mathlib). A count is an inductive type, `one | succ`: its recursor is induction (`ind`) and its no-confusion is
`1 + 1 != 1` (`neq`), so neither is assumed, and the sum and the product of counts are defined by recursion, with
their laws proved once. A mass is a pair of counts up to the tie `p * s = r * q`, as in Landau's construction of the
positive rationals. The three symbols are `1`, `+` and `/`; the product and the inverse are derived
(`x^(-1) := 1 / x`, `x * y := x / (1 / y)`), and the order is `a < b :<=> exists c, b = a + c`, which is no word in
`1`, `+`, `/`. The four laws of the symbols (Tarski's axiom `x / (y / (z / (x / y))) = z`, the unit `1 / 1 = 1`, `+`
associative, and `(x + y) / z = x / z + y / z`), `neq` and `ind` are theorems of the kernel about the masses
(`QppKernel/Laws.lean`); with `ind` the four laws are those of a semifield with no zero. There is no zero: a
`Count0` or a `Mass0` is a count or a mass, or absent, and a sum of no terms is absent. The kernel is described in
full in the section "The kernel" below.

Each word of the kernel has a reading over Mathlib in the bridge `lean/QppBridge` (`Count0.toNat`, `Mass0.toRat`,
`Idx.map`, ...), with one transport lemma per word in the simp set `qpp_bridge`. Each row of a module is proved over
Mathlib, in the namespace `QppMathlib`, and its statement over the kernel, in the namespace `Qpp.Modules`, is proved
from that reading through the bridge. A cited fact is never an axiom: it is proved from named lemmas of Mathlib (a
row `mathlib:`), or the theorems that use it take its statement as a hypothesis. Every declaration depends on
`propext`, `Classical.choice` and `Quot.sound` at most: the audits are `lean/Axioms.lean` (every row over the kernel),
`lean/QppBridge/Axioms.lean` (the bridge) and `qpp/lean/QppTests/Axioms.lean` (the kernel).

## The files

| file | what it does |
|---|---|
| `source.py` | the reader of Q++ 0.2 sources (below): prose, sections, items, rows, cited facts, proofs and fixture lines, each with its line |
| `texmath.py` | the term layer: Q++ terms, their LaTeX (in a canonical spelling) and their Lean |
| `kernel.py` | the generator: a Q++ 0.2 source to its Lean over Mathlib and, with a kernel target, its statements over the kernel words, each proved from its reading through the bridge; `--check` compiles the file and prints Lean's errors at their Q++ lines; `--primitives` prints the list of the primitives below |
| `modlean.py` | the Lean of the modules: `modules/NAME/NAME.qpp` to `lean/QppModules/Name.lean`, the rows over Mathlib in the namespace `QppMathlib`, then over the kernel in `Qpp.Modules`, with imports by `uses` (a module sees the proved rows of the modules it uses, directly or not); a file past 9,000 lines or 1.5 MB is written in parts `Name/PartK.lean`, each importing the one before; `--index` writes `lean/QppModules.lean` and the audit `lean/Axioms.lean`; `--palomar corner` writes the Palomar entry |
| `modules.py` | the check of the module sources: their uses, the scopes of the vocabulary, the row keys, no hole, and the list of the primitives in this file against the generator's |
| `modfix.py` | the fixtures of one module, checked on its rows by the checker of `tests/test_qpp.py` |
| `ctxmodel.py` | the exact model of the contexts of the pair, on which the fixtures of the cited rules over a context are evaluated |
| `enumeration.py` | the switch that keeps the fixture checkers from enumerating: a check that would visit the points of a set of candidates stops, and its fixture is reported as not evaluated (listed in `modules/enumerations.toml`) |
| `closers.py` | the closer tables `closers/*.json`: for each chain `first \| a \| b \| ...` of a generated file, the alternative that closed it in a run of Lean, so that the generator writes that alternative alone |
| `cert.py`, `fieldcert.py`, `progcert.py`, `lp.py` | the certificates that the generator writes, in exact arithmetic: Farkas certificates of the word `V` over pairs, identities of rational functions for the field steps, the prices and points of `prog`, the LP certificates of `LP` and `at` |
| `simplex.py`, `qpoly.py` | exact linear algebra and linear programming over Q (two-phase simplex, Farkas certificates), and exact polynomials over Q (resultants with their cofactors) |
| `pin.py` | pins: the test of Krawczyk and Moore on a box, in exact rational arithmetic, the Python side of `QppKernel/Pin.lean` |
| `qpp2latex.py`, `prooftex.py` | a Q++ 0.2 source to its LaTeX and its bibliography; the proofs as sentences, from their proof words |
| `latex2qpp.py`, `syntax.py` | the reader of that LaTeX back into Q++ (the round trip), and its lexer and parser of proof words |
| `qpp2lean.py` | the reading of a statement that the fixture checker shares with the Lean side: free indices, family ranges, defined relations, and the clauses a statement leaves out |
| `leanrefs.py`, `status.py` | the label map of a Lean library read from the tags of its docstrings, and the status page of a LaTeX source against it, per label |
| `examples/` | small sources that exercise the language: `vocabulary.qpp` (every vocabulary row and proof word, over Mathlib and over the kernel), `means.qpp`, `programs.qpp` and `pairs.qpp`, with their LaTeX; `refused/` holds the forms that the generator refuses, each with its reason |
| `closers/` | the closer tables, one per generated file, with the toolchain and the Mathlib revision of the run |
| `primitives_lean.toml` | the Lean constants of each primitive, which the audit of the statements reads |
| `lean/QppKernel/` | the kernel, on Lean core alone (section "The kernel") |
| `lean/QppTests/` | the checks of the kernel: identities replayed by `qeq` (`Smoke.lean`, `Resultant.lean`), certificates replayed by `farkas` (`FarkasSmoke.lean`, `Farkas.lean`; the large ones written by `resultant.py` and `farkas.py`), the sparse check (`Sparse.lean`), pairs (`PairSmoke.lean`), the pin of `y^2 = 2` (`Pin.lean`), the axiom audit (`Axioms.lean`) and the replay in three kernels (`kernels.sh`) |
| `tests/` | the Python tests (pytest, no Lean): the reader and the printers, the generator, the kernel's checks mirrored in Python, the LaTeX reader, and `test_qpp.py`, the checker of fixtures; `tests/fixtures/` holds the small LaTeX and Q++ files they read |

## Commands

From the root of the repository (Python 3, standard library; pytest for the tests):

    python3 -m qpp.modules check               # the module sources: uses, vocabulary, row keys, no hole, primitives
    python3 -m qpp.modlean NAME                # lean/QppModules/Name.lean from modules/NAME/NAME.qpp
    python3 -m qpp.modlean --all               # every module, then the index
    python3 -m qpp.modlean --index             # lean/QppModules.lean and the audit lean/Axioms.lean
    python3 -m qpp.modlean --palomar corner    # lean/QppPalomar/Corner/{Challenge,Solution}.lean, lean/comparator.json
    python3 -m qpp.modfix NAME                 # the fixtures of modules/NAME, on its rows
    python3 -m qpp.kernel SRC.qpp -o OUT.lean  # any source (the examples) over Mathlib; --check runs Lean on it
    python3 -m qpp.closers refresh FILE MOD    # the closer table of a generated file, from a run of Lean
    python3 -m pytest qpp/tests -q             # the Python tests

The Lean, in the Lake project `lean/` (Mathlib from its cache) and in the kernel's project `qpp/lean/`:

    cd lean && lake exe cache get && lake build      # the bridge, the modules and the examples
    cd lean && lake env lean Axioms.lean             # the axioms of every row over the kernel
    cd lean && lake build QppPalomar                 # the Palomar entry (its Challenge warns `sorry`, by design)
    cd qpp/lean && lake build QppKernel QppTests     # the kernel and its checks, on Lean core alone
    cd qpp/lean && lake env lean QppTests/Axioms.lean

## Q++ 0.2: the source and its printers

A module is a Q++ 0.2 file. Its lines, here from `modules/mean/mean.qpp`, with a cited fact of
`qpp/examples/means.qpp`:

    -- Q++ 0.2                                 the format line (not printed)
    module mean                                the name of the module
    uses root                                  the modules whose labels it references, then a blank line
    subsection sec:mean Cells that meet by a table
    -- LaTeX prose                             directly above an item or a proof: its description; elsewhere a paragraph
    lemma lem:mean [cells that meet by a symmetric table: the mean tie]     an item with its title
      core double: A, B in QQ>=0 : A * B + A * B <= A^2 + B^2               a row: its key, then the row
      (tie): n in NN>=1, P in Forms(n, n), ... : ...
      fix (tie) mean.tie                       a fixture of the row (tie): modules/mean/fixtures/mean.tie.json
      neqfix (tie) mean.tie.nosym              a counterexample: the row is false without a hypothesis
    proof lem:mean
      "core double" cases[A <= B; V[hc1 * hc1]; V[hn1 * hn1]]               a proof line: the key of its row, then a word
    cit fact:powermean [power means]           a cited fact: a statement and its source
      doi: 10.1017/CBO9781139020411            (stmt: N, optional, the number of the statement in the source)
      given: J, E in NN>=1, u_(1..J) in QQ>0
      (1): (sum j in 1..J, u_(j))^(E + 1) <= J^E * (sum j in 1..J, u_(j)^(E + 1))

A row `given:` holds the hypotheses of an item, and `c := t` in it names a term: Lean binds `c` with `h_c : c = t`,
never expanded. Further lines are `section`, `proof LABEL [title]`, a row `after:` (text after the statement
display, inside the environment), the vocabulary lines (`word`, `type`, `define`, `relation`, `context`, `alias`,
below), and `eqfix KEY ID` and `neqfix KEY ID` beside `fix` (section "Fixtures"). An indented `--` line is a note of
the source, not printed. The prose is the only prose of the module: the LaTeX needed to say what each item is. A row
or a proof line `?{...}` is LaTeX that is not Q++, printed as it stands and never generated; `python3 -m qpp.modules
check` refuses one in a row, a proof line or a vocabulary line of a module, but in an `origin:` row and in the
`stmt:` row of a cited fact, which are text about the source. An article is printed from a skeleton, a LaTeX file
with the prose that no item holds and a line `% qpp: include sec:x` wherever the section `sec:x` of a module goes
(`source.py`, `read_skeleton`).

### Row keys

The key of a row (and of a proof line) decides two things: whether the article prints it, and whether it is
read under the given of its item. Every reader (the kernel, `qpp2latex`, `latex2qpp`, the fixtures) asks the two
predicates `texmath.checks_only` and `texmath.is_core`, which read the key as follows:

| key | printed | read |
|---|---|---|
| `given`; a conclusion `(1)`, `(2a)`, a word (`sums`) | yes | under the given of the item |
| `core N`, `coreN` (digits: `core 1`, `core0`) | yes | alone (a core item) |
| `core`, `core NAME` (a letter first: `core tie`) | only where a printed proof cites it | alone (a core item) |

**A digit or a letter after `core` changes whether the row prints**: `core 1` is printed, `core tie` is not, unless a
printed proof of the article cites it (`lem:x(core tie)`, through an alias, or `fact:x` whose one row it is;
`qpp2latex.cited_cores`): then the row is printed in its item, so that a printed proof cites only printed rows. A core
item declares every name it uses before its colon and is read without the given (only the paper's context rows and the
result's operator definitions apply), so an item may carry several rows that only the checks read (`core`, `core tie`,
...), each with its fixture line (`fix core tie FILE`). A proof line keyed `"core"` or `"core NAME"` is not printed,
even where its row is: that proof is in the Lean. There is no row that is read under the given and not printed. In a
module, a key that begins with `core` and is none of these (`core 1a`, `core tie 2`, `core_tie`) is refused by
`qpp.modules check`.

### The printers

`qpp2latex` prints the LaTeX in the conventions that `latex2qpp` reads (`stmt`/`\sit`, `expr`/`\eit`), so the round
trip qpp -> LaTeX -> qpp is a test (`tests/test_printers.py`). That is the full print (`--full`); the print of an
article gives each proof line without the instantiation of its references, `[x := t, ...]`, which the Lean holds
(every claim and every reference stays, and so do the hypotheses a reference proves after `;`). A cited fact is a `fact` with `\cite[stmt]{key}` in
its title, keyed by the entry of the store (the file of the `bib` line) with that DOI, else by a `@misc` with the DOI.
The `.bib` is printed from the citations: it holds the entry of every key that the printed LaTeX cites and nothing
else; a cited key with no entry, and a `bib` line that names no file, fail the printing.
The vocabulary lines print at their place in the file, consecutive lines as one `stmt` display, one row each keyed by
its kind: `\sit{word}{\text{mass}:=\Q_{>0}}`, a typed word `\sit{word}{\mathrm{sep}(K\in \mathrm{Loss}(n),\ K'\in
\mathrm{Loss}(n'))\in \mathrm{Loss}(n+n')}` and its body `\sit{define}{\mathrm{sep}(K,K')(x,y):=K(x)+K'(y)}`, a define,
a type row `\sit{type}{\mathrm{Loss}(n):=\mathrm{Point}(n)\to \Q_{\ge0}}` (`set(X)` as `\mathcal{P}(X)`, `X^n` as
`(X)^{n}`, `pair` as its carrier `(\Q_{\ge0}\times\N_{\ge1})\cup\{\top\}`), a relation `\sit{relation}{K\ \text{bdd}\
B:\iff ...}`, a context `\sit{given relation}{\mathrm{coef}(K\in \mathrm{Loss}(n),\ ...)}`, an alias
`\sit{alias}{\mathrm{Arch}:=\cref{fact:arch}}`. `qpp2latex` reads each row back (`latex2qpp.vocab_row`) and fails
unless it gives the line's terms (`qpp2latex.vocab_tree`): the LaTeX says what the line says. So every module's LaTeX
(the extract of `modfix`) names the words it uses, and `qpp/examples/vocabulary.tex` prints every kind.

### The generator

The generator (`python3 -m qpp.kernel SRC.qpp -o OUT.lean [--check]`) writes the Mathlib reading of a source: one
`NAME.statement : Prop` per conclusion row (`lem_mean_1`), over Mathlib's rationals and natural numbers, and the
theorem `NAME` when the proof line generates; a cited fact is a statement, and a result whose proof cites it takes
`fact_y_1.statement` as a hypothesis, unless a row `mathlib:` proves it (below).

### The modules over the kernel

The modules over the kernel (`qpp/modlean.py`): the statement of a row of a module is over the words of the
kernel (`qpp/lean/QppKernel/Words.lean`, Lean core alone): a variable in `NN` is a `Count0` (a count, or absent for
zero), in `NN>=1` a `Count`, in `QQ>=0` a `Mass0`, in `QQ>0` a `Mass`; a tuple of `X^n` is `Idx n -> X` with the
indices `Idx n` counts; sums are `Idx.sum`, `boxSum` and `rangeSum`; the deficit is `Count0.deficit` or
`Mass0.deficit`, `binom` is `Count0.binom` (Pascal's rule), a numeral is a literal of Lean read by `OfNat`. A row
whose names are all in `QQ>0` or `NN>=1` (or tuples of them), and whose terms are built from them and from numerals
at least 1 by `+`, `*`, `/` and powers by a numeral or a count, is printed over `Mass` and `Count` themselves, with
no `Mass0.of` and no `Count0` in its terms (a count where a mass is wanted is `Mass.ofCount`; the size of a tuple
stays a `Count0`, since `Idx` is on `Count0`); any other row is printed over the zero layer as above
(`lem:zpositive`). Its proof
is the proof of its Mathlib reading (the same row over Mathlib, in the namespace `QppMathlib`), carried to the
kernel by the bridge `lean/QppBridge`: each binder is read in Mathlib (`Count0.toNat`, `Mass0.toRat`, `Idx.map`), and
the simp set `qpp_bridge` turns the reading back into the kernel statement. A quantifier of the reading over `ℕ`,
the positive integers, `ℚ≥0` or the positive rationals reads as one over `Count0`, `Count`, `Mass0` or `Mass`; a
quantifier of the kernel over `Count0` guarded by `1 <= x` (`x in NN, 1 <= x`) reads as one over `Count`, so that it
meets the reading (`Count0.forall_one_le`, `Count0.exists_one_le`); and a
quantifier over a tuple or a tuple of tuples of the kernel as one over the tuples of `ℕ` or `ℚ≥0`. A relation row is
a structure over the kernel with its reading `NAME.toMath` (the relation of the reading at the readings of its
arguments, proved field by field: the field `h.hK` of the hypothesis and the field `K` of the goal rewritten together
by `qpp_bridge`, then the field by its name) and a classical `Decidable` instance; a bundle is a structure over the kernel with its reading
`NAME.toMath` and its inverse `NAME.ofMath`, part by part. A pair is a `PairLM`, read by `PairLM.toMath`: a literal
pair `(l, m)` is `PairLM.mk l m` (`l` a `Mass0`, `m` a `Count`), `top` is `PairLM.top`. A program atom
`prog(DECLS, ROWS : COST) = P` is `IsProg S c P`, with `S` and `c` functions of a point `x : Idx k -> Mass0` whose
coordinate `j` is `Idx.extend 0 x j`; over families of scales the scale `j` of the block at the offset `o`
is `NAME.blk x o j`, that is `Idx.extend 0 x (o + j)`, and absent at `j` absent (`Option.elim`: `Count0` is
`Option Count`), emitted with the type row and read in Mathlib by `NAME.blk_toRat`; the lemma `NAME.prog_i` reads it as the atom of the Mathlib reading at the
readings of its names (`isProg_iff_pred` of the bridge), before the transfer reads the rest. A cited fact with no
context is a statement over the kernel with its reading `NAME.toMath`; a row that cites it takes it over the kernel,
read in Mathlib by `NAME.toMath`, and a row `mathlib:` proves it from the Mathlib reading (`NAME.holds`). A family
`a_(1..k)` is a function `a : Count0 -> X` on the counts, its member `a_(j)` is `a j`, and it is read as
`fun i => R (a (Count0.ofNat i))`, where `R` is the reading of `X`; a quantifier over families is read by the bridge.
A function on the counts (a type row `NN -> QQ>=0`) is `Count0 -> Mass0`, read in the same way; it is read at a
natural number (`f(u + 1)`, or a term that is a natural number once its indicators are counts, `S(sum i, A_(i) *
iverson(i = j))`), and a member of a family of them at a point (`YP_(j)(u)`, `YP j u`); the bridge reads
`Count0.ofNat (u + 1)` as `Count0.ofNat u + 1` (`Count0.ofNat_add`).
A define of masses or counts (`define half(x) := x / 2`) is a definition over `Mass0` or `Count0` with its reading
`NAME.toMath` in `qpp_bridge`. `join(x, y)` is `Idx.join x y`, with its two defining equations in the kernel and its
laws in the bridge (`lean/QppBridge/Join.lean`: its halves `Idx.fst`, `Idx.snd`, its reading `Fin.append`); a word
is a definition over the kernel with its equation `NAME_def` (at its point, or at `Idx.join x y` for two points), in
`qpp_bridge` with the equation of its Mathlib reading. A tuple of a size `n + n'` of two counts is read on
`Fin (n.toNat + n'.toNat)`, as the reading at the sizes `n` and `n'` asks (`Idx.mapAdd`, `Idx.unmapAdd`, through
`Count0.toNat_add` and `Fin.cast`), and so are its indices, quantifiers, sums and boxes. Mathlib never enters a
statement of a module: the audit of the statements reads the
column `kernel` of `qpp/primitives_lean.toml`, and `lean/QppBridge/Axioms.lean` audits the axioms of the bridge. A row
that the kernel printer does not write yet (a word of both signs, a context, a set and its operations, `oplus`, a form
of both signs) is not generated, with its reason, and `qpp.modlean` fails on it. A typed word of masses on points is
written over the kernel too, with its equation in `qpp_bridge`; a typed word with an argument in NN, values in
tuples, or defined at a coordinate is written over Mathlib only, where the proofs read it: a module may define one and
use it in its proofs, and a statement that names one is not generated over the kernel. The example
`qpp/examples/vocabulary.qpp` is generated over the kernel too (`--kernel-target Examples`,
`lean/QppExamples/Kernel.lean`), its vocabulary that is not over the kernel yet left out
with its reason.

### Over Mathlib

Over Mathlib (the examples and the Mathlib reading of the modules):

* A cited fact is `def fact_x_core.statement : Prop`, never an axiom. A theorem whose proof cites it, directly or
  through the results it uses, takes `fact_x_core.statement` as a hypothesis, and its docstring lists them
  (`; cited: fact_x_core`).
* A row `mathlib: NAME (MODULE)` instead of `doi:` (or with it) names the Mathlib lemma that proves the cited
  statement: the file then imports MODULE and proves `fact_x_core.holds` from NAME, and the theorems that use the
  fact apply `fact_x_core.holds` and take no hypothesis for it. Example (base): `cit fact:arch` with
  `mathlib: exists_nat_gt (Mathlib.Algebra.Order.Archimedean.Basic)`. A row `mathlib: NAME, NAME' (MODULE)` names
  Mathlib lemmas that together prove the statement, the parts of an existential or a conjunction: the binders
  introduced, then the anonymous constructor of the lemmas, each applied to nothing, to a hypothesis or to a term
  found by unification. Example (vocabulary): the floor, `cit fact:zfloor` with `mathlib: Nat.floor_le,
  Nat.lt_floor_add_one (Mathlib.Data.Rat.Floor)`.
* Every other cited item needs a `fix` line (`fix-{module}` fails otherwise): its statement enters as a hypothesis,
  so a fixture checks that it is not stated wrong. A cited rule about a context (every typed statement row applies one,
  as `coef(K, B, p)`) has no concrete instance in Q++: its fixture `{"kind": "model", "rows": [...]}` is evaluated on
  the exact model of the contexts of the pair (`qpp/ctxmodel.py`). A loss is a sum of
  monomials `c * w^a` (`c` a positive rational, even natural exponents; in a fixture blocks in separate variables, a
  block a monomial or `{"sum": [...]}`), a region a finite union of boxes in the orthant with rational corners, a
  weight a tuple of positive naturals; the model computes their pair exactly, by the program of `fact:readout`(1) at
  the corner of each box (Lin 2017, Theorems 4.8 and 4.10, Propositions 2.5, 3.2, 3.3). Each row of the fixture gives the names of the rule that are not
  pairs, as `{"n": 1, "K": [[2]], "B": [[[1, 2]]], "C": [[[0, 2]]]}` (the loss `w^2`, the boxes `[1, 2]` and
  `[0, 2]`: `top` and `(1/2, 1)`, which tell the two directions of Mono apart); a hypothesis `coef(K, B, p)` binds
  `p`. An existential over a set that the model does not enumerate (`exists z in Point(n) : ...`) is read at the
  witness the row gives under its bound names: the clause holds when its body holds there, and stays undecided when the
  witness fails it (`fact:strict` of `root`). A witness the row gives is read first over any set, the points of
  `NN^n` included, before the bounded reading of the type (the value of a word at a point, `lem:wdepth(core dyad)`);
  a witness outside its type (a coordinate of a point of `NN^n` that is no natural number, one of a point of
  `(QQ>0)^n` that is zero) proves nothing (`lem:witnesswrong` of `qpp/examples/refused/contexts.qpp`). A row holds, fails, is vacuous (a hypothesis is false) or is undecided; the fixture fails if a row fails or is
  undecided, or if none holds. A fixture of kind `"witness"` (the kind of the checker of the statements) fails unless every row holds. The examples: the rules of `qpp/examples/vocabulary.qpp` and, stated wrong,
  `qpp/examples/refused/contexts.qpp` (`python3 -m qpp.ctxmodel SRC.qpp FIXDIR`). A `neqfix KEY ID` line on such a rule is read on the
  model: its fixture `{"kind": "counterexample", "drop": [...]}` gives rows where the hypotheses kept hold, a dropped
  one fails and the conclusion fails. A cit takes one `doi:`; further sources go in an
  `origin: ?{...}` row, which is printed and generates no Lean.
* A row over the relation of the coefficient of `def:coef`, `(K #coefficient lambda #multiplicity m #weight q #over
  B)`, is not decided on its definition (lists of boxes at every level). Its fixture may name the relation, `"graph":
  "coefficient"` next to its kind (`model`, or `counterexample` for a `neqfix`): the rule is then read on the
  model, with the relation read as the graph of the model's pair (`K` has the pair `(lambda, m)`, not `top`, over `B`
  for the weight `q`), as a rule over a context reads `coef`. The name is refused unless the relation's parameters
  are, in their order, a loss, a rational, a natural number, a tuple of natural numbers and a region, so that no other
  relation is read so by accident. `(K #bdd B)` keeps its definition (the least value of `K` on `B`), so that a row
  on `top` compares two computations. The reading tests the wording of a row (the direction of an inequality, the
  larger multiplicity at a tie, a hypothesis that is needed), not the definition: the definition is tied to the
  model's pair by `lem:readoutlists`(1), (2) with the rows `unique` and `unique tie` of `lem:pair`, for a sum of
  monomials on a region between two cubes at the origin; on a box with a positive corner and on a union of boxes the
  model's values are the classical ones that `qpp/ctxmodel.py` cites. A row that ends in `0 < 0` is vacuous on every
  instance, so its fixtures are `neqfix` lines, one for each hypothesis dropped.
* A cited rule that the theorems take as a hypothesis (a `doi:` and no `mathlib:`) prints its statement: in a module
  no row of it is keyed `core` or `core NAME` (key it `(1)`; `qpp.modules check`). A cit with `mathlib:` is proved,
  no theorem takes it as a hypothesis and its sentence states it, so it may keep `core`. The examples are not
  modules and are not checked so.
* A reference without a key (`fact:arch`) is row 1 of the item, or else its one row (`core`).
* `alias NAME := LABEL(KEY)` (a top-level line) makes the proof word `NAME[data]` the reference `LABEL(KEY)[data]`:
  the lemma of that row, proved once in the module that owns it, applied at each use. Nothing is expanded or proved
  again at a use. An alias names one row; a composite word is a lemma item of its own, which an alias then names. A
  module sees the aliases of the modules it uses, directly or not.
* Vocabulary lines (top-level, not printed; a module sees those of the modules it uses, directly or not, and
  `qpp.modules check` fails on a use outside them, in a given row too). The generated Lean of every module is in the
  one namespace `Qpp`, so a vocabulary name is global: the check fails on a name that two modules define (naming both
  lines), and on a variable named like a word of a module that is not used (rename it, or use the module).
  `qpp/examples/vocabulary.qpp` uses each row and proof word once; CI generates it and builds and audits its Lean
  (lean/QppExamples):
  * Constructs only from the primitives of Q++: no row names Lean or Mathlib, and the
    generator and `qpp.modules check` refuse the word `lean` in a row. The primitives are every construct the
    generator writes in a statement; they and their Mathlib counterparts are one list, `PRIMITIVES` in
    `qpp/kernel.py`, printed below by `python3 -m qpp.kernel --primitives` (`qpp.modules check` fails when the two
    differ). **The list is closed**: a new primitive is a change of the language. A proof over Mathlib may use any of Mathlib (tactics
    and lemmas create no construct, and Lean checks them); a row of a module is proved over the kernel from that
    proof through the bridge, and nothing of Mathlib is proved again on the kernel. The only escape is a cited fact (`cit`), whose statement is Q++: a
    `doi:` row, or a `mathlib:` row naming a Mathlib lemma and its Mathlib module; a context is a parameter of the
    statements that use it.
  * Positivity: over Mathlib a source is positive unless it carries the mark
    `application: REASON`, a header line (after `paper NAME`; in a module after `uses`) for an application with data
    of both signs. The list ends with the forms of both signs (`x in QQ`, the
    type `QQ`, `a - b`, `-a`, `|a|`); with them `ZZ` and every vocabulary name whose line has one, directly or through
    another such name, of the source or of a module it uses (`type Loss(n) := Point(n) -> QQ>=0` is of both signs if
    `Point` is). In a positive source a row or a given with such a form is not generated, with its reason listed,
    and a vocabulary line with one is an error. The deficit `max(a - b, 0)` (Lean `max (a - b) 0`) is the one
    subtraction, its arguments read like any term; `max(0, a - b)` is no deficit. The deficit of two natural
    numbers is a natural number: over `NN` it is `max (a - b) 0` in `Nat` (the truncated difference), read in `QQ`
    the same number over `Rat` (`lem:zdeficit`). Proof lines are not read: a
    certificate may carry coefficients of both signs, and the tactics subtract. `modules/both_signs.toml` lists by module
    the rows and lines of both signs it still carries (`LABEL(KEY)`, `LABEL(given)`, `HEAD NAME` for a vocabulary
    line), and the marks under `[applications]`; `qpp.modules check` fails unless each module carries exactly its
    list, which may shrink and never grow, and the generator refuses any other. The kernel takes such a list with
    `--allow ID,...` (as for `qpp/examples/vocabulary.qpp`). The refused cases are in
    `qpp/examples/refused/both_signs.qpp`. In a source of refused cases (`--refused`) a refused vocabulary line is reported
    with its reason, like a row, and every vocabulary line that `--allow` does not list must be refused (the lines it
    lists set up the cases); `qpp/examples/refused/lines.qpp` holds vocabulary lines with a refused term.
  * A bracket of an existential over a number set, `iverson(exists q in NN : A = q * p)`, is refused: Lean finds no
    decidable instance for it. The clause is a relation row (which has a classical instance), or the bracket the count
    of its witnesses, `(sum q in 0..A, iverson(A = q * p))` (`lem:ivexists` of `qpp/examples/refused/terms.qpp`).
  * The audit of the generated statements: `qpp/primitives_lean.toml` gives the Lean constants of each row
    of the list below (instances left out), and `qpp.modules check` fails unless its rows are exactly the rows of the
    list. The audit prints the constants of every `NAME.statement` of the namespace Qpp (a cited fact's too) and of
    the vocabulary definitions they reach (types, words, defines, the structures of relations, the contexts), and
    fails on any constant that no row lists, naming the module, the declaration and the constant. Proofs are not audited. The audit reads
    constants, not their arrangement: `HSub.hSub` is approved by the deficit and by the order `m - 1` of a literal
    pair, so the rule above (the kernel's refusals) keeps a bare `a - b` out of a positive source; the report counts,
    per module, the statements that name `Neg.neg` or `abs`.

### The primitives

<!-- primitives: generated by python3 -m qpp.kernel --primitives -->
| Q++ | Lean over Mathlib |
| --- | --- |
| *binders (a sign bound is a hypothesis of the binder)* | |
| `x in NN` | x : Nat |
| `x in NN>=k` | x : Nat, k <= x |
| `x in QQ>=0` | x : Rat, 0 <= x |
| `x in QQ>0` | x : Rat, 0 < x |
| `x in {0, 1}` | x : Rat, x = 0 or x = 1 |
| `a_(1..k) in S` | a : Nat -> T, the bound of S at every i |
| `c := t` (in a context) | c : T, c = t |
| *types (type rows)* | |
| `QQ>=0` | NNRat |
| `QQ>0` (the positive rationals) | {x : Rat // 0 < x} |
| `NN>=1` (the positive counts, as coordinates: (NN>=1)^n, ((NN>=1)^n)^k, and a part of a bundle) | {x : Nat // 0 < x} |
| `NN` | Nat |
| `X^n` | Fin n -> X |
| `(X^n)^k` (a tuple of tuples: k rows of n coordinates, X one of NN, NN>=1, QQ>=0, QQ>0) | Fin k -> Fin n -> X |
| `(X -> Y)` | X -> Y |
| `(X -> QQ>0), (X -> NN>=1)` (a function with positive values) | X -> {x : Rat // 0 < x}, X -> {x : Nat // 0 < x} |
| `set(X)` | Set X |
| `pair` | WithTop (Lex (Prod NNRat (OrderDual Nat))) |
| *terms* | |
| `0, 1, 2, ...` | numerals |
| `a + b, a * b, a / b` | the same |
| `a^e` (e a numeral or a natural number) | a ^ e |
| `iverson(P)` | if P then 1 else 0 |
| `min(a, b, ...), max(a, b, ...)` | min a b, max a b |
| `max(a - b, 0)` (the deficit: the one subtraction of a positive source) | max (a - b) 0 |
| `binom(n, k)` | Nat.choose n k |
| `sum k in a..b, t; prod k in a..b, t` | Finset.sum, Finset.prod over Finset.Icc a b |
| `bidetP(T, U), bidetM(T, U); bidetP(A), bidetM(A)` (the two halves of the bideterminant: of a couple of square tables T, U of ((QQ>=0)^n)^n standing for T - U, or of one table A; only in a tie, a comparison or a deficit that reads each couple through det(T - U) alone, invariant under one mass added to both halves) | QppMathlib.bidetP T U, QppMathlib.bidetM T U (U the table 0 for one table): Laplace's recursion along the first row over NNRat, with bidetP T U = bidetM T U + Matrix.det (T - U) in Rat (QppMathlib.bidetP_eq) |
| `a_(i)` | a i |
| `f(x, y)` (a define row) | f x y |
| `x_(i), a_(j)_(i), f_(iota)_(i)` (x a tuple of X^n, X one of NN, NN>=1, QQ>=0, QQ>0; a_(j) a member of a family a_(1..k) of such tuples; f a tuple of tuples (X^n)^k; i, iota bound over their coordinates) | x i, a j i, f iota i; i : Fin n, iota : Fin k |
| `sum i, t; prod i, t` (i over the coordinates of the tuples it indexes) | Finset.sum, Finset.prod over Finset.univ (Fin n) |
| `sum u <= b, t` (b a tuple of NN^n: the lattice points u of the box [0, b], cut by rows through iverson) | Finset.sum over Finset.Icc 0 b |
| `sum k in a..b : C_1, ..., C_J, t; sum i : C_1, ..., C_J, t; sum u : C_1, ..., C_J, t; sum u in T : C_1, ..., C_J, t` (the points of the range at which every clause holds; on the lattice the points of (NN>=1)^n, or of NN^n when T is a tuple type of NN^n, the first clause bounding the content by a level) | Finset.sum over Finset.filter of Finset.Icc a b, Finset.univ, Finset.Icc 1 (fun _ => L) (Finset.Icc 0 (fun _ => L) for a point typed in NN^n) |
| *propositions* | |
| `=, !=, <, <=, >, >=` (chains) | =, !=, <, <=, >, >= (chains joined by and) |
| `P, Q; P or Q; P => Q; P <=> Q; not(P)` | and, or, implies, iff, not |
| `forall x in S : P; exists x in S : P` | forall, exists, with the bound of S |
| `forall i : P; exists i : P` (i over the coordinates of the tuples it indexes) | forall i : Fin n, P; exists i : Fin n, P |
| `i = j, i < j, i <= j` (an index over the coordinates of tuples and an index or a count: indices are counts, with their order and equality) | i = j, i < j, i <= j with i, j : Fin n; (i : N) + 1 = (j : N) + 1 for two ranges; (i : N) + 1 = t for a count t |
| `forall K in Loss(n) : P; exists p in Pair : P` (over a type row) | forall K : Loss n, P; exists p : Pair, P |
| `(x #word y)` (a relation row) | a structure, one field per clause |
| `coef(K, B, p)` (a context row) | an argument of the statement |
| `prog(v, w_(1..L) in QQ>=0, ROWS : COST) = P` (an atom, P a pair; with families of scales and universal rows) | NAME.IsProg {x : Fin k -> Rat \| 0 <= x i, ROWS} (fun x => COST) P: P = top and no point is feasible, or P = NAME.mk L d with L : NNRat the least value of the cost (IsLeast, Set.image) and d the dimension (Module.finrank of the vectorSpan, a Submodule) of the feasible points of cost L (Set.ofPred); over families of scales, k is the number of the scales plus the lengths of the families, and the scale j of the block at the offset o is NAME.blk x o j (over the kernel Idx.extend 0 x (o + j), by Option.elim) |
| *objects* | |
| `K(w)` | K w |
| `forall w in B : P; exists w in B : P` | forall w in B, P; exists w in B, P |
| `join(x, y)` (two tuples of one type row) | Fin.append x y |
| `B times C` (two sets of tuples) | Set.image2 Fin.append B C |
| `B cup C, B cap C, B subseteq C, emptyset` | Union, Inter, Subset, the empty set |
| `union j in a..b, P_(j); inter j in a..b, P_(j)` | iUnion, iInter over Finset.Icc a b |
| `oplus j in a..b, p_(j)` (or min j in a..b, ...) | (Finset.Icc a b).inf p |
| `top; p + q; min(p, q); p <= q` (pairs) | top; +; min; the order of the pair |
| `Pr.P` (the part P of a bundle Pr) | Pr.P, the projection |
| `(l, m)` (a literal pair, where type NAME := pair is in scope) | NAME.mk l (m - 1); l in NNRat: numerals, a natural number cast (k : NNRat), a name in QQ>0 or QQ>=0 as Rat.toNNRat x (x under the sign hypothesis of its binder), with + * / ^ min max; m: a numeral at least 1, a name in NN>=k with k >= 1, + * ^ of those, or a product over a range of those |
| *definitions (vocabulary rows)* | |
| `type NAME := pair` | NAME.mk l o := toLex (l, OrderDual.toDual o), with the laws NAME.mk_le and NAME.mk_add |
| `word w(K in X, ...) : Y; define w(K, ...)(x) := t` | def w ... : Y := fun x => t, and w_def (rfl) |
| `word w(N in NN, ...) : Y` (an argument in NN, which Y may name) and define w(N, ...)(u)_(j) := t (a result whose values are tuples, at a coordinate; read by proofs only) | def w (N : Nat) ... : Y := fun u => fun j => t, and w_def at u and j (rfl) |
| `define w(K, K')(x, y) := t` (two points) | fun z => t at the halves of z (Fin.castAdd, Fin.natAdd), and w_def at Fin.append x y |
| `define f(x, y) := t` | def f (x y : Rat) := t, and f_def |
| `type NAME(k, n) := {P, N in X, op in Y}` (a bundle: named parts of different types, each a tuple, an object of a type row or in NN) | structure NAME (k n : Nat), one field per part |
| `relation (x #word y) := clauses` | a structure, one field per clause; over Mathlib also a classical Decidable instance (the relation inside a bracket) and R_iff, the relation as the conjunction of its fields |
| `context NAME(x in X, ...)` | a parameter Ctx_NAME of the statements that use it |
| *both signs (applications only: refused in a positive source)* | |
| `x in QQ` | x : Rat |
| `QQ` | Rat |
| `a - b, -a` | the same |
| `\|a\|` | \|a\| |
<!-- /primitives -->

  * `word NAME := SET` (`word mass := QQ>0`): `x in NAME` declares x in SET;
  * `define f(x, y) := t`: `def f (x y : Rat) := t` with its equation `f_def`, emitted once in the module that owns the
    line; `cases V` rewrites by the equation, the other closers get its instances as ties (base: `pos(x)`);
  * `relation (q #site t) := q in QQ>0, q <= t, t <= 2 * q`: a `structure site (q t : Rat) : Prop` with one field
    per row (h1, h2, ...: the bounds of the declarations, then the clauses); the clause `(a #site b)` in a given is
    one hypothesis `h_k : site a b`. After the intro its rows are named in the context, `have h_k_1 := h_k.h1; ...`
    (the cast of a compound count pushed), so that a certificate names a row (`V[q * h_1_2]`) and every closer and
    side goal (`div`, `pow`) sees them, and `h_k` stays for a lemma that takes the relation itself. Its arguments
    may be objects of type rows (`relation (K #asymp K' #on B) := n in NN, K, K' in Loss(n), B in Region(n), (exists
    c, C in QQ>0 : forall w in B : c * K'(w) <= K(w) <= C * K'(w))`), the parameters of their types (`n`) implicit.
    At a use, the rows read the parameters from the declarations of the arguments, position by position, and take
    them with the arguments at once: with `relation (f #zwide t) := k, n in NN, f in Rows(k, n), t in NN, n <= t`
    and `g in Rows(n, k)`, the row of `(g #zwide t)` reads `k <= t` (`k, n := n, k`); a bundle that `take` gives
    part by part reads them from the set of its existential (`lem:ztake`: `exists B in ZBox(r, h)` gives
    `k, n := r, h`). An argument may be a family, of objects or of numbers, indexed from 0 or 1 (`relation (P #chain
    M #floors a #top m ...) := ..., P_(0..m), M_(0..m) in Line, a_(0..m) in QQ>=0, ...`, `lem:chain`): its Lean
    argument is the function of its index (`P : Nat -> Line`, over the kernel `Count0 -> Line`), the bound of its
    members is the item's, not a field, and at a use the argument is the name of a family of the scope;
  * `type Point(n) := (QQ>=0)^n`, `type Loss(n) := Point(n) -> QQ>=0`, `type Region(n) := set(Point(n))`: a type
    in Q++ from the primitives (a point has nonnegative coordinates; the number
    sets are the words of a binder, so the check of signs reads them; `QQ>0` in a type row is the type of the
    positive rationals `{x : Rat // 0 < x}`, as `QQ>=0` is `NNRat`: `type Weight(n) := (QQ>0)^n`, positive by
    construction, so that `join` and the contexts need no side proof; it types
    tuples, sets, the arguments of functions and their values (`type PosLine := NN -> QQ>0`); `NN>=1` in a type row
    is the type of the positive counts `{x : Nat // 0 < x}`, as a coordinate (`type PosGrid(n) := (NN>=1)^n`, and
    `((NN>=1)^n)^k`), as the value of a function (`NN -> NN>=1`) or as a part of a bundle, while in a binder
    `x in NN>=1` stays the hypothesis `1 <= x` (`lem:zposcount`); over the kernel such a coordinate, value or part is a `Count`, a value in `QQ>0` a `Mass`, and
    their bounds are read by the bridge, not written as hypotheses; a quantifier over a tuple of `NN>=1` or `QQ>0`
    inside a statement is refused over the kernel with its reason (the bridge reads quantifiers over tuples of `NN`
    and `QQ>=0` only), and stays over Mathlib; a tuple may be written in its binder, `x in X^n` or `s in (X^n)^k`
    with `X` one of `NN`, `NN>=1`, `QQ>=0`, `QQ>0` (`x in (QQ>0)^n`), and reads as the type it unfolds to, as
    `x in Weight(n)` does: `lem:ztuplebind`),
    `abbrev Point (n : Nat) : Type := Fin n -> NNRat` and `abbrev Loss (n :
    Nat) : Type := Point n -> NNRat`, once in their owner; `K in Loss(n)` is the binder `(K : Loss n)`, `P_(1..J) in Region(n)` the family
    `P : Nat -> Region n`. `type Pair := pair` is the pair, the second coordinate ord = m - 1, with `Pair.mk l o`,
    `Pair.mk_le`, `Pair.mk_add` and the order read in Rat (`mk_le_rat`, `mk_lt_rat`, `mk_eq_rat`): `+` is the
    product of pairs, `min` the tropical sum, `top` the pair of no point;
  * `type Prog(k, n) := {P, N in Rows(k, n), op, om, eps in Grid(k)}`: a bundle,
    named parts of different types, each a tuple, an object of a type row or a number of `NN`; a
    `structure Prog (k n : Nat)` with one field per part, in order. `Pr in Prog(k, n)` binds one name, and
    `Pr.P` is its part `P`, read as a name of the part's type with the bundle's arguments (`Pr.P_(iota)_(i)` a
    coordinate; LaTeX `\mathrm{Pr}.P_{\iota,i}`). A relation may take a bundle as an argument (`relation (s
    #zfeasible Pr #zlevel L) := ..., Pr in Prog(k, n), ...`), so that a program and its certificate are each one
    object and each one clause. A fixture gives a bundle as a JSON object, one value per part (`{"P": [[1]], "N":
    [[0]], ...}`); the model reads the arguments of a relation that its row leaves implicit (`k`, `n` of
    `Pr in Prog(k, n)`) from the lengths of the values passed, part by part. A part's name may end in digits
    (`u0`, `K0`), and its indices read as those of a name (`Pr.N_(iota)_(i)`, LaTeX `\mathrm{Pr}.N_{\iota,i}`).
    A part may be a function on the points of a tuple type (`F in Moduli(n, n)` in `type Chart(n)`); over the
    kernel it is read through its points, its values read back (`pivots`, `thm:pivots`);
  * `context coef(K in Loss(n), B in Region(n), p in Pair)`: a relation that is a parameter, never a definition. A
    statement that uses it, or uses a result or a cited fact that does, takes `(coef : Ctx_coef)` and passes it on;
    the clause `coef(K, B, p)` is a hypothesis or a goal (LaTeX `\mathrm{coef}(K,B,p)`, read back by the line
    `% qpp: relations coef` of the LaTeX);
  * `join(omega, omega')` and `B times B'` are words of the primitives: from `Weight(n)` and `Weight(n')` (a type row
    `X^n`), or `Region(n)` and `Region(n')` (a type row `set(Point(n))`, `Point(n) := X^n`), to `Weight(n + n')` and
    `Region(n + n')`. `join` is not the literal pair `(l, m)`.
  * A word with a body is written in Q++, pointwise: the signature, then a `define` line with the points,
    `word sep(K in Loss(n), K' in Loss(n')) : Loss(n + n')` and `define sep(K, K')(x, y) := K(x) + K'(y)`. One point
    is a point of the domain of the result; two points split a domain `Point(a + b)` (with `Point(n) := X^n`) into
    `Point(a)` and `Point(b)`. The generator writes the `def` from its template (`Fin.castAdd`, `Fin.natAdd`) and the
    equation `sep_def : sep K K' (Fin.append x y) = K x + K' y` (by `simp only [sep, Fin.append_left,
    Fin.append_right]`, which holds when the two halves have one size too; one point: `rfl`), and one `def sep {n n'
    : Nat} (K : Loss n) (K' : Loss n') : Loss (n + n')`, its parameters read off the types of the arguments at a
    use. The body takes objects applied to the points, numerals, the parameters, `+ * /` and `min max`, in the value
    type of the result (NNRat or Rat; subtraction only in Rat); it is read at the `define` line, where an error names
    the line, and a point may not be named like an argument or a parameter. In a row, a word is applied at a point,
    `shift(K)(w)` or `sep(K, K')(join(x, y))` (Lean `sep K K' (Fin.append x y)`, read in Q). V reads it through its
    equation: the tie `NAME_def` at the point (a word of two points at `join(x, y)` only, where its equation holds),
    with the signs of the values in NNRat (`0 <= K(w)`) that the tie brings in.
  * A word may take an argument in NN, `word halve(n, N in NN) : Halves(n)` (Lean `(n N : Nat)`, explicit), which
    the result type may name; a result whose values are tuples (`Halves(n) := Grid(n) -> Point(n)`) is defined at a
    coordinate, `define halve(n, N)(u)_(j) := u_(j) / 2^N` (Lean `fun u => fun j => ...`, and `halve_def` at `u` and
    `j`, rfl). The body takes, besides the above, the coordinates of its point at that index, powers with an exponent
    in NN, sums over a range `sum k in 1..B_(j), t`, brackets of natural numbers `iverson(a <= b)`, and an object
    applied at a word at the point, `K(halve(n, N)(u))`; a coordinate in NN gives a body in NN. In a proof,
    `halve(n, N)(u)_(j)` is the coordinate of the word at a point (and `Ch.F(u)_(j)` that of a part of a bundle), and
    V reads it through the equation of the word; a tuple that a hypothesis names as the word at a point (`y =
    halve(n, N)(u)`, the witness of `take[y := halve(n, N)(u)]`) has its coordinates read through that hypothesis, and
    a word whose body applies an object at that point is read at the name (`value(K, N)(u)` is `K(y)`); where the
    ties are quotients, V rewrites by them first and clears the quotients (`2^N * y_(j) = u_(j)`). A word is an
    argument of a relation or of a reference (`(value(K, N) #zfloor Q #zbox b)`), and `take` gives a part of a bundle
    that is a function by a word, `take[D.F := halve(n, N), D.N := N]` (`lem:wdepth`).
* Objects over Mathlib: `top` and `emptyset` take the type of the other side; `B cup C`, `B cap C`, `B subseteq C`;
  `union j in 1..J, P_(j)` is `⋃ j ∈ Finset.Icc 1 J, P j` and `oplus j in 1..J, p_(j)` (or `min j in 1..J, ...`) is
  `(Finset.Icc 1 J).inf fun j => p j`, top for J = 0. `forall w in B : ...` quantifies over the points of a region (a
  type row `set(X)`), `K(w)` applies an object of a function type row (an NNRat value is read in Rat); the point
  may be of any type whose type rows unfold to the domain, as a member `F_(k)` of `Forms(r, n)` for `Point(n)`
  (`lem:zalias`). A tuple
  `(l, m)` is a literal pair where `type NAME := pair` is in scope (`coef(K, B, (1/2, 1))`, printed `(1/2,1)` and read
  back by latex2qpp as a tuple): `NAME.mk l (m - 1)`, the first coordinate built in NNRat from numerals, counts
  (cast), masses and names in `QQ>=0` (`x.toNNRat`, their sign hypothesis the hint of the cast back), with `+ * / ^
  min max` and no subtraction, so that it is positive by construction; the second a multiplicity, at least 1 whatever
  the values of its names: a numeral at least 1, a name in `NN>=k` with k >= 1 or a member of such a family, `+ *`
  of those, one to a natural power, or a product over a range of one (the empty product is 1). Never a name in `NN`,
  a subtraction, a sum (it can be empty), `binom`, `min`, `max` or a name given by `c := t`: at m = 0 the order m - 1
  in N would be that of m = 1. The literal pair is a primitive.
  The forms refused are cases in `qpp/examples/refused/literal_pairs.qpp`: `kernel.py --refused` fails if
  one of them is generated, and its generated file lists each reason. A goal between sums of literals (`=`, `<=`, `<`,
  `>=`, `>`) is folded by `show` (`mk_add` is `rfl`) and read in Rat with no choice of a branch: `NAME.mk_le_rat` is
  `mk l o <= mk l' o' <-> l <= l' /\ (l = l' -> o' <= o)` (`mk_lt_rat` alike, `mk_eq_rat` both
  equal). Where the orders compare outright (the multiplicities evaluated exactly at three fixed values of their
  names, then `omega`), the word of the proof line (`V`, `V[...]`, `eq`, `I`) proves `l <= l'`; where they do not, it
  proves `l < l'` (`mk_le_of_lt`, `mk_lt_of_lt`). So `a <= b : (a, m) <= (b, m)` and `(min(a, b), 1) <= (a, 1)` are
  closed from the weak comparison. `(l, m) < top` is a simp lemma. A `min` of literals (the tropical sum) is reduced with
  no search: under `=` the argument equal to the other side whatever the names (equal at three fixed values of the
  names, an identity that needs no hypothesis; Lean proves the equation) (`min_eq_left` or `min_eq_right`, the
  comparison of the two arguments as above), so `b <= a : min((a, 1), (b, 1)) = (b, 1)`; on the right of `<=` or `<`
  by `le_min` or `lt_min`; on the left by the argument equal to the other side whatever the names, or below it with
  no name or by a hypothesis on the first coordinates (`min_le_of_left_le`, `min_lt_of_left_lt`, ...); else it is
  refused with its reason. A context applied (`coef(K, B, (b + a, 1 + 1))`, word `V`) is the hypothesis of the same
  context that prints the same (`exact`), or that differs from it only by a pair equal to its pair whatever the names
  (`coef(K, B, (a + b, 2))`): `convert h using 1` leaves the equation of the two pairs, proved as above. A goal between objects is closed by a tactic chosen by its shape: a
  tropical sum over `1..J` against a member is `Finset.inf_le`, a lower bound of every member below it `Finset.le_inf`
  (the hypothesis over the members found by `solve_by_elim`), an equation of the two both (the least member is the
  sum); regions by `tauto_set` (the algebra of sets, with the subset hypotheses); two tuples (`S(u) = s`) coordinate
  by coordinate (`funext`), each coordinate by the equations in scope; else `order` or `simp`. A
  hypothesis quantified over the points of a region, `forall v in B : K(v) <= K'(v)`, is used by `V` at the points
  of B that the goal introduces (`forall w in B : ...`, `intro w hm_w`): its instance `h w hm_w` is a fact, with the
  ties and signs it brings in. Not yet: a point of B given by a subset hypothesis. The LaTeX gets `% qpp: maps Loss ...` (objects applied) and `% qpp: textrel _ asymp
  _ on _` (the patterns of the relation rows), which latex2qpp reads back.
* Programs over Mathlib: the atom
  `prog(v_1, ..., v_k in QQ>=0, ROW_1, ..., ROW_J : COST) = P` stands only on the left of `=`, with a pair `P` on the
  right (a literal pair, `top`, or a name of the pair type), in a row or in a given. The scales are fresh names
  declared in `QQ>=0` (a scale with the name of a name in scope is refused); each row is one relation `>=`, `<=` or
  `=` of two terms affine in the scales (their coefficients any terms free of the scales); the cost is a linear form
  in the scales, each monomial of degree 1 read through products (`(v + 1) * alpha` is refused). These refusals are
  made where the statement is built, so they hold in a given too, where no word runs. The atom is `NAME.IsProg S c P` with
  `S = {x : Fin k -> Rat | 0 <= x 0 /\ ... /\ ROWS}` and `c = fun x => COST`, the scale i read as `x i`.
  `NAME.IsProg` is emitted once with the type row `type NAME := pair` (after `NAME.mk`), with its lemmas
  `isProg_mk`, `isProg_top`, `isProg_unique` (at most one pair satisfies the atom), `IsProg.le` (the least value is
  at most the cost at every feasible point, read by a reference `at` a point), `le_faceDim` and `faceDim_le` (the
  dimension of a face from below and from above):
  `IsProg S c p := (p = top /\ S = emptyset) \/ exists L : NNRat, IsLeast (c '' S) L /\
  p = NAME.mk L (Module.finrank Rat (vectorSpan Rat {x | x in S /\ c x = L}))`.
  The least value is an NNRat because the first coordinate of a pair is one: a program whose least value is below
  zero has no pair (a cost with coefficients at least zero is at least zero on the orthant). When some point is
  feasible and the cost has no least value at least zero (unbounded below, or least below zero), the atom is false
  for every P. The pair stores the dimension d of the optimal face, so the literal pair `(l, m)` reads `d = m - 1`.
  The constants that the row adds to the audited statements are `IsLeast`, `Set.image`, `Set.ofPred`, `vectorSpan`,
  `Submodule` and `Module.finrank`. No item states that some pair satisfies the atom (that a program bounded below
  attains its least value is not used): the word proves the atom for the pair it is given. The fixtures read the atom on the exact model (`qpp/ctxmodel.py`): the pair by the exact simplex
  of `qpp/simplex.py` (the least value, then the dimension of the face it cuts, from the inequalities that no point
  of the face makes strict), at the values of the parameters, without the word; `neqfix` refutes a
  wrong pair (`lem:progtie` in `qpp/examples/vocabulary.qpp`). The forms refused are in
  `qpp/examples/refused/programs.qpp`.
* Programs over families of scales. A declaration
  of the atom may be a family `v_(1..L) in QQ>=0`, with `L` a term of the given that names no scale; a row may be
  universal over an index of a range, `forall j in NN>=1 : j <= B => ROW(j)`, with `B` free of the scales and
  `ROW(j)` one relation `>=`, `<=` or `=` affine in the scales and the members `v_(j)`; the cost may hold sums
  `sum j in a..b, t(j)` linear in the members. A member is read at an index free of the scales; a family used whole,
  a scale in a denominator or a product of two scales is refused. An atom with no family reads as above. The point
  is `x : Fin k -> Rat`, with `k` the sizes of the blocks in the order declared (a scale 1, a family its length:
  `1 + L + R` for `x, v_(1..L), u_(1..R)`), and the block at the offset `o` (the sum of the sizes before it) is read
  by `NAME.blk x o : Nat -> Rat`, its scale `j` the coordinate `o + j - 1` for `1 <= j` within the point and 0
  otherwise; a scale is `NAME.blk x o 1`. The lemmas emitted with the type row: `blk_succ`, `blk_one`,
  `blk_nonneg`, `blk_add`, `blk_sub`, `blk_smul`, `blk_zero`, `blk_le_one`; the points built block by block,
  `NAME.emb k o s f` (the members `f 1, ..., f s` of a block at the offset `o`), with `blk_emb_self`,
  `blk_emb_before`, `blk_emb_after`, `emb_nonneg`; `van_first`, `van_step`, `van_end` (a point whose blocks are
  all 0 is 0); `isProg_cast` (the atom does not depend on how its size is written); and the two bounds of the
  dimension of the face used by the word `face[...]`: `faceDim_le_ties` (the face lies in the solutions of
  ties that fix every block but the free scales: its dimension is at most their number) and `one_le_faceDim` (two
  points of the face that differ at a scale: its dimension is at least 1). The reading lemma `NAME.prog_i` reads
  the atom over the kernel as the atom of the Mathlib reading by `isProg_iff_pred` and `isProg_cast`, with no
  literal `k` and no `fin_cases`. The exact model (`Ev.prog_expand` in `qpp/ctxmodel.py`) expands the families at
  the values of a fixture: the members become scales, a universal row its instances, a sum its terms.
* The coordinates of a tuple and the lattice points of a box (two primitives). For a tuple `x` of a type row `X^n` (`X` one of `NN`, `QQ>=0`, `QQ>0`), `x_(i)` is its
  coordinate `i`, read only under a binder over the coordinates: `sum i, t`, `prod i, t`, `forall i : P`,
  `exists i : P`. A binder without a range runs over the coordinates of the tuples it indexes, all of one length; in
  Lean `x i` with `i : Fin n`, the sums and products over `Finset.univ`, a coordinate in `QQ>=0` or `QQ>0` read in
  `Rat`. Two indices of one range compare, `i = j`, `i < j`, `i <= j` (indices are counts, with their order and
  equality), in an indicator, `iverson(iota = i)`, or as a
  guard (`lem:zindex`, `lem:zbundle`(diag)). An index compares with an index of another range, or with a count, as
  the count it is (`lem:zcross`): `iota = i` with `iota` over the coordinates of `IntForms(k, n)` and `i` over those
  of `Exponent(n)` is `(iota : N) + 1 = (i : N) + 1` (over the kernel `iota.1 = i.1`), and `i <= t` with `t` in
  `NN` is `(i : N) + 1 <= t` (over the kernel `Count0.of i.1 <= t`), since `i : Fin n` is the count `i + 1`. A side
  may be a sum or a product of counts and indices: the row `iota` of a second block of rows reads the coordinate `i`
  as `iverson(iota = K + i)`, so that a count read from an index never indexes a tuple and no index leaves its
  range. The range of each index is read from its uses `x_(i)` in the body of its binder; an index with no such use
  runs over the range that the same name had last in the declaration (the rows of a program given by formulas in
  `take`, a sum over the rows whose terms are formulas), else over the range of the index it is compared with;
  `sum[W]` reads a sum whose term has the factor `iverson(iota = j)`, with `iota` and `j` of one range, as its term
  at `j` (`Finset.sum_eq_single`); with `j` an index of a shorter range (`Fin n` within `Fin (n + 1)`), or a count
  `t + 1` where `iota` runs over `Fin (t + 1)`, as its term at the element of the same count, when no other factor
  indexes a tuple by `iota` (the rows of `Prog(n + 1, n)` read at a coordinate `p` or at the count `n + 1`, as in
  `lem:binomial`; over Mathlib the element `<p, _>` of `Fin (n + 1)`, the other terms absent by `Fin.ext`; at a count
  `j` the element `<j - 1, _>`, its bound and `1 <= j` by terms where they have one, with no `omega`: `Nat.sub_lt`
  of `1 <= j` from a count `t + 1` or `t + (u + 1)` (`Nat.le_add_left`) or from a tie `j = t + 1` by name, then
  `j <= n` by name unless `j` is the size `n` of the range, and every other term absent by `b + 1 != j` from
  `b != j - 1` (`Nat.eq_sub_of_add_eq`)); and a product
  whose term is a power whose exponent has that factor as its factor at `j`, the base at `j` to the rest of the
  exponent (`Finset.prod_eq_single`; `lem:compare`(core point)), except where the two sides are two sums or two
  products over one range, which compare term by term; `cases` closes a case whose comparisons of indices contradict
  each other (`omega`). An indicator in a coordinate of `NN` is a count (`if P then 1 else 0` in `Nat`, over the
  kernel `iversonN`), and so is a relation of two terms that are counts once their incidences `iverson(iota = i)`
  are (a row of a program at a coordinate, `(sum i, 2 * iverson(iota = i) * s_(i)) = 2 * s_(iota)`), an exponent
  `E_(X) * iverson(X = X0)`, and the side goal of a natural hypothesis (`iverson(X = X0) <= 1`). In a term an index
  is the count it is, with its arithmetic (indices are counts "with their order, equality and
  arithmetic"), as the coefficient `2 * iota` of a row read at its index (`lem:zidxcount`; Lean `(iota : N) + 1`,
  over the kernel `Count0.of iota.1`). What stays refused is a count read from an index used as an index: a
  subscript is a name bound over the coordinates, and a member of a family over a range is indexed by a name of its
  range, never by `i + 1` with `i` over coordinates (`lem:cindex` in `qpp/examples/refused/lattice.qpp`). A numeral
  as a coordinate (`x_(1)`), a binder that indexes no tuple and tuples of two lengths are refused.
  `a_(i)` stays the member of a family over a
  range, indexed by a name of its range (not by an index over the coordinates). The tuple may be a member `a_(j)` of a family `a_(1..k)` of
  tuples of `X^n`, `a_(j)_(i)` (Lean `a j i`), or a row `f_(iota)` of a tuple of tuples `f` of a type row
  `(X^n)^k`, `f_(iota)_(i)` (Lean `f iota i`, `f : Fin k ->
  Fin n -> X`), both indices bound over coordinates; one level only (a member of a family of families, a row of a
  tuple of tuples of tuples, are refused), and `a_(j)_(i)` with `i` over a range is refused. Both print with one
  subscript, `a_{ji}`, `f_{\iota,i}`, which latex2qpp reads as one application of two indices, `a_(j, i)`: the
  read-back of a vocabulary row is compared up to that merge (in a typed row the kernel reads only the nested form),
  and the exact model reads both forms alike. For `b` a tuple of
  `NN^n`, `sum u <= b, t` is the sum over the points `u` of `NN^n` with `u <= b` coordinatewise
  (`Finset.Icc 0 b`); rows cut the box through `iverson(...)` in `t`, so the number of points of a cut box is
  `sum u <= b, iverson(ROWS)`; `Finset.filter` enters a statement only through a cell sum, and `Finset.card` never.
  Only a sum runs over a box,
  whose corner is a tuple of `NN^n`; neither construct admits `ZZ`, a difference or an infinite sum (a sum over
  infinitely many points is stated as a bound uniform in `b`). The constants added to the audited statements are
  `Finset.univ` and the casts of a coordinate. A file whose statements use either imports `Mathlib.Data.Pi.Interval`,
  `Mathlib.Algebra.BigOperators.Fin` and `Mathlib.Combinatorics.Enumerative.DoubleCounting`. The fixtures evaluate
  the rows on the exact model (`qpp/ctxmodel.py`), the sums by enumeration, `binom` of two natural numbers exactly
  (`lem:zsimplex`), a quantifier over the points of `NN^n` on the boxes that its clauses `forall i : u_(i) <= t` bound (a point outside fails that clause), a quantifier over `NN` (or `NN>=d`, from `d`) on the numbers up to the bound `x <= t` (or `x < t`) of its premise or body. A quantifier over the points of `NN^n` that no clause bounds is read in two cases: when its premise is `F(u) = s`, at the one point `s`; and when its body is an identity of polynomials in the coordinates, on the grid `{0, ..., D}^n`, `D` the largest degree, which decides it (a polynomial of degree at most `D` in each variable that vanishes on that grid is zero). A quantifier over the points of a tuple type of `QQ>=0` (`Point(r)`) is read at the one point `s` of its premise `F(u) = s` when `s` lies in the type; when it does not, no point meets the premise, and the quantifier holds (`forall`) or fails (`exists`). Points are equal coordinate by coordinate. A function on points (a type row `Exponent(n) -> QQ>=0`, `Exponent(n) -> Exponent(r)` or `Exponent(n) -> Point(r)`) is given by a table, `{"table": [[point, value], ...]}`; a point the table does not list leaves the row undecided. A function on the counts (a type row `NN -> QQ>=0`, read at a natural number such as `u + 1`, and a member of a family of them read at a point, `YP_(j)(u)`) is a list of its values at `0, 1, ...` or a table `{"table": [[u, value], ...]}`, and a family of them a list of such values; a fixture of the kind `model` is read on the model whatever the rule, so a rule on functions on the counts is. With `fix` and
  `eqfix` (`sec:lattice` of `qpp/examples/vocabulary.qpp`); the forms refused are in
  `qpp/examples/refused/lattice.qpp`, and the rules stated wrong that the model refutes in
  `qpp/examples/refused/contexts.qpp`.
* The bideterminant. For square tables `T`, `U` of
  one type row `((QQ>=0)^n)^n`, `bidetP(T, U)` and `bidetM(T, U)` are the two halves of the determinant of the couple
  `(T, U)` standing for `T - U`, over the semiring of couples (Akian, Gaubert and Guterman, arXiv:0812.3496,
  Def. 4.14); `bidetP(A)` and `bidetM(A)` are those of the couple `(A, 0)`, the bideterminant `(|A|^+, |A|^-)` of
  Gondran and Minoux (the sums over the even and over the odd permutations, AGG Remark 4.17), so that
  `det A = |A|^+ - |A|^-` over a ring. Both readings define them by Laplace's recursion along the first row: `(1, 0)`
  on no rows, the halves of the minor of `(1, j)` exchanged at the even columns `j`. Over Mathlib they are
  `QppMathlib.bidetP T U` and `QppMathlib.bidetM T U` over `NNRat` (`lean/QppBridge/BidetMath.lean`, which imports
  Mathlib only), read in `Rat`; over the kernel `bidetP T U` and `bidetM T U` (`qpp/lean/QppKernel/Words.lean`), read
  as the former by `Mass0.toRat_bidetP` and `Mass0.toRat_bidetM` (`lean/QppBridge/Bidet.lean`, simp set
  `qpp_bridge`); one table is the couple with the table `fun _ _ => 0`. Their one law, `QppMathlib.bidetP_eq`, is
  `bidetP T U = bidetM T U + Matrix.det (T - U)` in `Rat`, by `Matrix.det_succ_row_zero` and induction on `n`; every
  other law of the halves enters from a law of `Matrix.det` through it. The recursion is unfolded only there and in
  the transport: in a proof a half is an atom of a certificate, as a name is (`lem:zbidet` in
  `qpp/examples/vocabulary.qpp`), and the sum over the permutations is never written. Each half alone is #P-hard
  (`|A|^+ = (per A + det A) / 2`), so a tie, a comparison or a deficit `max(a - b, 0)` reads each couple only
  through `det(T - U)`: with `bidetP(T, U)` read as `M + D` and `bidetM(T, U)` as `M` (`D` for the determinant),
  the difference of its two sides, a polynomial in the halves, holds no `M`, that is, it is invariant under one mass
  added to both halves of a couple. The halves enter by sums, products, powers by a numeral and quotients by a term
  with no half; a deficit whose sides pass is read as an atom. So `bidetP(T, U) = bidetM(T, U) + k` passes, and so
  does the tie of crossed products of two couples, whose difference is `(P - M)(P' - M') - k l` (`lem:zbidet`(core
  cross), the form of the law of Binet and Cauchy), while the generator refuses a half fixed at the determinant
  (`bidetP(T, U) = 2 * bidetM(T, U)`), a half counted twice, the products of the halves of one side, halves of two
  couples compared, two halves on one side, a half under `min`, in a witness of `take` or in the body of a
  definition (`qpp/examples/refused/bidet.qpp`). A deficit of the halves of one couple is decided by the order of its
  two sides, a fact of the step (`max_eq_left`). The printer
  writes `\bidetP{T}{U}`, `\bidetPa{A}` and their `M` forms, the macros `|(T,U)|^{+}` and `|A|^{+}` of
  `modules/macros.tex`, which `latex2qpp` reads back. The fixtures evaluate the halves on the exact model
  (`qpp/ctxmodel.py`) by the same recursion over the rationals, each couple checked against the sums over the
  permutations, `|(T,U)|^+ - |(T,U)|^- = det(T - U)` and `|(T,U)|^+ + |(T,U)|^- = per(T + U)`; a table is a list of
  its rows.
* Words over Mathlib only: `cases V[d, ...]` gives the facts of the data (products of hypotheses and squares, as for
  `V`) to every case after the split; `mono` compares sums, products, powers and quotients term by term, written as
  one term: the two sides walked together, each operation by its monotone lemma (`add_le_add`,
  `mul_le_mul_of_nonneg_left`, `mul_le_mul`, `div_le_div_of_nonneg_right`, `pow_le_pow_left0`, `pow_le_pow_right0`,
  `pow_le_pow_of_le_one`, `Finset.sum_le_sum`, `Finset.prod_le_prod0`, `1 <= prod i, F` from `1 <= F` at each
  index over the product of 1 (`Finset.prod_const_one`), and `a <= b + c` from `a <= b` and `0 <= c`),
  each place where the sides differ a fact of the step whose statement it is (a fact over one index at an index in
  scope, the bound of a binder in `NN>=k`), each side condition a sign by name (the hypothesis of a mass, a coordinate
  in `QQ>=0` or `QQ>0`, a count cast, a square, and their sums, products, quotients and powers). Where a place has no
  such fact, or a sign no name, `mono` is `gcongr` with its side goals closed as by `V`, and on `t^e <= t^f` (one base
  on both sides) also the base at most 1 (`pow_le_pow_of_le_one`: `0 <= t`, `t <= 1`, `f <= e`); `div[c]` also
  proves `t > 0` and `a > b` from `c * t > 0`, `c * a > c * b`.
* An equation `a = b` (one `=`, not between regions) proved by two words `W1, W2` is `le_antisymm`: `W1` proves
  `a <= b` and `W2` proves `b <= a`, as a value from an inner and an outer bound (`"core" lem:unique, lem:uniq2`, or a
  cited rule twice with its names swapped).
* `min` and `max` of more than two terms are nested; `-(-t)` prints with its parentheses; an identity with variable
  exponents distributes the powers of products and quotients first.
* `NN>=k` is `Nat` with the hypothesis `hp_x : k <= x`. A relation between natural numbers in a given stays over `Nat`,
  and its cast to `Rat` is given to `linarith` and `nlinarith` (a sum with its casts at the atoms; not a relation with
  a truncated difference); so is the bound `hp_x` of a binder in `NN>=k` with `k >= 2` (`k in NN>=3` does what
  `k in NN, 3 <= k` does). A reference given a compound natural term (`m := (sum i, a_(i))`) carries its cast whole,
  where the goal has the casts at the atoms: its instance closes the goal up to casts too (`exact_mod_cast`, or
  `push_cast` then `linarith`), and its hypotheses are discharged up to casts (`assumption_mod_cast`;
  `lem:zcastref`). The cast of a sum or a product whose term is its index (`sum j in 0..J, j`, `prod i in
  1..d, i`) is not folded back by `norm_cast`: its relation is cast whole (`Nat.cast_le`) and pushed, for
  `linarith` and for the side goals of `mono` (`lem:zround(index, prod)`, `lem:zchoose(mono)`).
* The files import only the Mathlib modules the generated proofs need (`MATHLIB_IMPORTS` in `kernel.py`), plus the
  module of each `mathlib:` row. Over Mathlib a file sets `maxHeartbeats` to 2000000: a closing word is a search, the
  alternatives that fail spend the budget of the declaration, and a proof of several steps, each by a closing word,
  can pass the default 200000 (an option of the elaborator; the kernel checks the proofs as they are). The budget is
  per declaration: tower's `lem:link(top)`, about 40 steps in one row, passes at 2000000 and not at 1000000.

### Types and proof words

Types, in the Mathlib reading: `QQ>0` is `ℚ` with the hypothesis `0 < x`, `QQ>=0` is `ℚ` with `0 <= x`, `NN>=k`
is `ℕ` with `k <= x`, `NN` is `ℕ`, `QQ` is `ℚ` (a source of both signs only). A family is a function on every
index, and the sign of its set (`QQ>=0`, `QQ>0`, `NN>=k`) is a hypothesis at every index, not only on its range: a
consumer extends a family past its range by a value of that sign. The range is not checked against the reads of a
statement, so a statement that reads `u_(j)` outside the range (a hypothesis over every `j in NN`) reads that
extension.

Proof words:

* `eq` on an equation of terms with sums: the two sides are walked together, and each place where they differ
  is given by one law, either way round: two sums exchanged (`Finset.sum_comm`), a product of powers with one
  exponent free of the index and the power of the product (`Finset.prod_pow`), a product of 1 and 1
  (`Finset.prod_const_one`), a factor moved into or out of a sum
  (`Finset.mul_sum`, `Finset.sum_mul`), a sum of a sum split (`Finset.sum_add_distrib`), a sum against the indicator
  of its index at `t` collapsed to its term at `t`, the law of a box: a sum over the lattice points of boxes of a
  product over the coordinates and the product over the coordinates of the sums over their ranges, `(sum s <= b, sum
  e <= b2, prod z, F(z, s_(z), e_(z))) = prod z, (sum t in 0..b_(z), sum t2 in 0..b2_(z), F(z, t, t2))`, with a factor
  free of the points on both sides (`Finset.prod_univ_sum`, the box `Finset.Icc 0 b` being by definition the product
  of the intervals of its coordinates; `Finset.mul_sum`, `Finset.sum_mul`; `F` reads each point at the coordinate
  only, and holds no product, nor a sum where a factor moves; `lem:zboxprod`), a fact of the step, or its instance at
  the names of the place,
  its leading universals over indices and points read off the two sides by matching (`h_2 i a`, `h_1 i x`), one
  range written two ways whose upper bounds a fact of the step ties, `hi = hi'` in counts (`Finset.sum_congr` over
  the two ranges equal by that fact, `lem:layer`(unit)), or an identity of rings, where the two sides are one polynomial in the same atoms (a sum, an indicator, an entry), up to
  their bound names (`ring1`); the places are reached by congruence through a sum over one range
  (`Finset.sum_congr`) and through `+` and `*`, each argument a goal. Where each sum of the goal is named by a fact,
  the laws are used only when one of them applies, else linear arithmetic over the sums as below (`lem:zsumlaws`,
  `lem:zfactplace`);
* `eq`, `I`, `eq[h_c, 2 * h_1]` (each equation either way round): the equations of the given that define a local
  (`x = t` or `t = x`, `x` not in `t`) are substituted first, each by its name in order (`subst h_c`; none where no
  equation defines one), then the data are the coefficients of a `linear_combination`, and without data the normal
  form of the two sides (`ring1`) closes the goal, else the closers of arithmetic, naming no local that the
  substitution removed (`t = 0` turns `x^t` into `x^0`;
  `lem:zeqsub`);
* `V[...]`: the data, with products of hypotheses and squares among them, are the certificate of a
  `linear_combination`, the rest closed by `ring1` or by the positivity of the difference. A datum names a
  hypothesis of the row (`h_1`, `h_c`) or the fact of a step of the proof line, `hwK` for the `K`-th step (a `with`
  or a link of a `chain`, in the order of the text; `lem:zwithcert`). Where the certificate is exact, it is
  one `linear_combination` with no remainder left to a search: an inequality times its multiplier is
  `mul_le_mul_of_nonneg_left` (or `mul_lt_mul_of_pos_left`) with the sign of the multiplier written (a numeral by
  `norm_num`, a multiplier of several terms term by term by `add_nonneg` and `mul_nonneg`, or `add_pos` and
  `mul_pos` for a strict one, a count by its cast, a sum of terms at least 0 by `Finset.sum_nonneg`, a deficit
  `max(a - b, 0)` by `le_max_right`;
  `lem:zmultsign`), so that `linear_combination` runs no `positivity` on a coefficient, and the rest, a sum of
  positive monomials in the masses, one term `0 < c * m` per monomial, each sign by the name of its hypothesis
  (`hp_x`, a member `hp_w k` of a family, the cast of a count from `hp_k`; `lem:zmasscert`). A relation between
  counts is read in Q by its cast (`exact_mod_cast`), and the cast of a sum, a product or a power of counts by the
  sum, the product or the power of their casts, as the Lean of a relation over Q writes it (`lem:zcountcast`); an
  equation is a tie, whose datum gives the size of its
  multiplier and whose side the proof writes (Q++ writes no negative numeral): in `V[written | turned]` a datum
  `c * h` with `h` the equation `a = b` is read as `a <= b` would be before the bar and as `b <= a` after it, so
  that the certificate is a tie of two positive sums as written and the generator only checks it; for a goal that
  is an equation, data with no bar have their sides read off the target by one linear solve, monomial by monomial
  (`eq_sides`), a computation with one answer; no side is ever tried; a goal that is an equation takes equations
  only, exactly; a datum times 0 gives no term, so a goal true by ring is
  `linear_combination` alone (`lem:zeqcert`). A datum also names the clause of the `K`-th `cases` of the proof line
  and its negation, `hcK` and `hnK`, each in its own branch, and a universal fact over an index at an index in scope,
  `h_1(i)` or `hwK(i)`, read as the fact applied to the index, the bound `i <= n` of an index `i` in scope over the
  coordinates of the tuples of length `n`, `hb(i)` (Lean: `i.isLt`, since `(i : N) + 1 <= n` is `i < n`), and the guard
  of a name `x` of the given, `k <= x` for `x in NN>=k` or `0 < x` for `x in QQ>0`, `hp(x)` (`lem:zidxbound`); the
  words that read a fact by name (`cases`, `logic`, the sides of a bracket) read the bound of an index too; a sum of
  the goal that a coefficient of the data writes is one atom, as one that a fact writes; `V[0]` names no fact, for a
  goal that the rest alone closes; a goal between counts is combined over Q and cast back (`exact_mod_cast`;
  `lem:zcasecert`), and so is a relation stated
  over N because its incidences `iverson(iota = i)` are read as counts, whose facts the data read by their casts.
  Where the strict reading leaves the data no certificate, the strict orders of counts `a < b` that they name are
  read as `a + 1 <= b` (the strict order of counts is the order of the successor), over Q by their casts
  (`lem:zsucc`). A
  monomial of
  the rest may also read atoms at least 0 by name (a count by `Nat.cast_nonneg`, a coordinate, a sum of such terms),
  signed term by term, when another term or a strict fact gives a strict goal its strictness. A deficit
  `max(a - b, 0)` of counts whose bound `b <= a` a fact of the step states by name is read as `a - b`: the tie
  `max(a - b, 0) + b = a` over Q, from `max_eq_left` and `Nat.sub_add_cancel` over N by its casts, enters as a
  definition, and the goal over N is read in Q with the deficit cast whole (`lem:zdeficitwit`); in a relation over
  Q the deficit of two counts is the deficit of their casts, `max ((a : Q) - b) 0`, as the Lean of the relation
  writes it. A conditional of
  the certificate that a fact of the step decides by name is read at its branch: the bracket `iverson(P)` by
  `if_pos` from `P` (`rfl` for `a = a`) and by `if_neg` from a fact that excludes `P` (`a != b`, `a < b`, `b <= a`,
  ...; `a = b` for `iverson(a != b)`, by `not_not`), `max` and `min` of two terms by `a <= b` or `b <= a` (`max_eq_left`, `max_eq_right`, `min_eq_left`,
  `min_eq_right`), a deficit `max(a - b, 0)` by `a <= b` or `b <= a` (`sub_nonpos`, `sub_nonneg`); the tie of the
  conditional with its branch enters as a definition (`lem:zcondname`); the terms of a deficit may be sums, whose
  bound names are not names of the step (`lem:zdeficitsum`). A sum over a range that its bounds make nonempty is
  strict by `Finset.sum_pos` (the bounds by their index terms), so that a sign `0 < t` with sums in `t` is `V[0]`;
  a strict goal whose rest has no monomial of masses takes the first monomial that has a strict sign by name
  (`lem:zsumsign`). A quotient in the data or in a fact (a multiplier `(1 / A) * h_1`, a fact `b / a <= 1`) is
  exact once the ties `d * d^-1 = 1` of its denominators are added, which the exact arithmetic cancels and `ring1`
  does not: each denominator above 0 by the signs of its names, the tie by `mul_inv_cancel₀`, its multiplier
  computed by `qpp/fieldcert.py` (`lem:zdentie`). A power of a count as a coefficient is read with its cast
  pushed in, as the goal reads it (`lem:zpowcoef`). A sign with no name, or a quotient whose sides or denominators
  are not read, leaves the remainder to the closer, a search that `modules/searches.toml` counts.
  The data of the bare `V` of the modules are read once from Lean by `qpp/certx.py`: the combination that `linarith`
  finds, whose coefficients are constants over the parameters read as atoms, is written in the source where the
  generator checks it exactly and Lean accepts its `linear_combination`; with `--cases --bare --searched`, every
  bare `V` whose step is still a search gets the certificate of the exact LP over the facts of its step, their
  products two by two and their roundings, named in the data (`h_1 * hw2` for a product);
* `LP[p_1, ..., p_J; extra]`, the LP certificate of a program (an item whose given declares scales in `QQ>=0`): one price per row of the given on the scales, in order, read as `V[p_1 * h_r1, ...]`, then further data; a row `at: x := t, ...; ...` states that the points satisfy the rows and attain the value of the row `cost >= value` (its proof generated); `qpp/lp.py` checks the same certificates in exact arithmetic (`qpp/examples/programs.qpp`);
* `prog[w_1, ..., w_J; v := t, ...; ...]` on an atom `prog(...) = (l, m)`: one price per row, in order, then each
  point as assignments (a scale left out is 0). The arithmetic is exact over the parameters (`qpp/progcert.py`): the
  equalities `x = t` of the given are substituted (`subst`), each denominator of a term substituted for a name that the
  rows or the cost read stated not 0 beside those of the prices, so that the identities read its tie (`lem:zdentie`), and a sign is read from the given: a ratio of
  polynomials whose coefficients have one sign, in names of `QQ>0`, `QQ>=0` or `NN`, or such a ratio times the gap
  `b - a` of a hypothesis `a < b` or `a <= b`; each sign is a goal of the proof (`positivity`, `mul_pos` with the
  gap). The value: the first point is feasible and attains l; the prices are at least zero on the rows `>=` and
  `<=`, the reduced costs `s_i` are at least zero, and `sum_j w_j b_j = l` (weak duality: one `linear_combination`
  of the identity `c(x) - l = sum_j w_j (row_j) + sum_i s_i x_i` and of the facts `0 <= w_j (row_j)`,
  `w_j (row_j) = 0` on a row `=`, `0 <= s_i x_i`, each with the coefficient 1 that the identity gives it). The order: from above, the rows of positive price, the
  rows `=` and the scales of positive reduced cost are tight on the face, with coordinates injective on their common
  kernel (`faceDim_le`); from below, the points, with the inverse of their differences at pivot coordinates
  (`le_faceDim`). A sign is read from the signs of the names, or as a function of one sign times the gap `b - a` of
  a hypothesis `a < b` or `a <= b`; a sign at least zero by the names is strict when it is a function of strict sign
  times a strict gap (`kq / (5 + eta)` with `0 < kq`, `lem:progstrict`). The word is refused, naming the sign, when
  a price or a reduced cost has a sign that the given does not decide, and when the two bounds differ (naming the prices and reduced costs only shown at least zero):
  each case of the parameters is one item (`lem:progabove`). `prog[y_1, ..., y_J]` proves `prog(...) = top` (a
  Farkas line: `sum_j y_j a_j <= 0` in each scale and `sum_j y_j b_j > 0`). Without data, or on a name of the pair
  type, the word is refused (an exact solve of the program is not built). `LP` stays for the one-sided rows
  `cost >= value`;
* `face[VALUE; POINT_1 by W_1; ...; TIES by W; GAP]` on an atom over families of scales `prog(...) = (l, 1)` or
  `(l, 2)` (`prog[...]` is refused there), or on such an atom whose scales are all scalars, read then as
  blocks of size one, with `l` a formula of the given at least 0 by the signs of its names. It proves the
  pair from rows of the item already proved, with no search. Its data are the read-out of the tristars of the
  program: the prices that balance the cost against the tight rows, the points where the tight rows meet, and the
  ties that name them:
  - VALUE is the word of `COST >= l` at every feasible point (in its own context: the scales and the members as
    names, then the hypotheses `h_(n+1), ...`, the signs of the blocks and the rows, in order);
  - each POINT is a list of assignments `x := t, v_(j) := t(j)` (a block left out is 0), proved by its word: the
    signs of the blocks given, the rows at the point and `COST = l`, in that order and with the terms at 0 left
    out; there are `m` points, and the first gives the least value (`IsLeast`);
  - TIES are equations, or universal rows `forall j in NN>=1 : j <= B => A = A'`, that hold at every point of the
    face, proved by their word on the rows and `COST = l` (the last hypothesis). Each tie solves the block declared
    last among those it names, with coefficient 1 or one above zero by the signs of the given; the blocks left unsolved
    are scales, `m - 1` of them (a family left unsolved is refused). The dimension is at most `m - 1`
    (`faceDim_le_ties`);
  - GAP, only at `m = 2`, is the word of `T1 < T2`, the free scale at the two points: the dimension is at least 1
    (`one_le_faceDim`).
  The rows that state the value, the points and the ties are the item's own (value), (point), (only) and (edge)
  rows (`lem:capped`); the word assembles them, and each refusal names the goal it could not write;
* `V` with no data: first the goal by name where it has one: a fact of the step that states it, up to the
  names they bind (`exact_mod_cast h`), a part of such a fact (a conjunct or a link of a chain, `(h).2.1`), or the
  instance of a fact over one index at an index in scope, or a part of it (`exact_mod_cast h i`); the range of the
  index of a sum (`lo <= j <= hi`) and the facts at that index are facts by name, and so are the guards of the
  binders, `0 < x` of a mass, `k <= n` of a count at least `k`, and their instances at a member of a family
  (`hp_c r`; `lem:zguardname`); a sign `0 <= t` or `0 < t` by its term, the signs of the parts of `t` written as
  for `mono`; a bound `x <= y` of counts by its index term (`x + 1 <= y` or `x <= y` from a fact `x < y`, `0 <= y`
  by `Nat.zero_le`; `lem:znatbound`); a quotient times its denominator, `t / c * c = t`, by `div_mul_cancel₀` with
  the sign of `c` by name (`lem:zsumsign`(core quot)); then the certificate of `V[0]`, where it is exact (the definitions and the deficits by their ties, the
  rest signed by name); then the closers of arithmetic (`positivity`, `linarith` and `nlinarith` over the hypotheses). The sign hints of
  the closers are terms too: a coordinate or a value in `QQ>=0` (`NNRat.coe_nonneg`), a count (`Nat.cast_nonneg`, or
  `1 <= n` from the bound of `NN>=k`), a power of a numeral (`pow_pos`), and a hint elaborated after the facts are
  rewritten (`split_ifs at *`) reads only the signs of the names, not the facts. An order `a <= b` of indices,
  counts and coordinates of tuples of `NN` is first its index term (as for `term[J]` below; `a <= t` from a fact
  `a < t + 1`, or `a < c` with `c` the numeral after the numeral `t`, by `Nat.le_of_lt_succ`), and `a < b` is
  `a < t + 1` from `a <= t` (`Nat.lt_succ_of_le`) or `a + 1 <= b` (`Nat.lt_of_succ_le`), with or without data; an
  equation of two such terms from two words, one for each order (`V, V`, `le_antisymm`);
* `h_K(i)[x_(l) := t, y := s]` (also `hwK(i)[...]`, `hiK(i)[...]`, `ih_x[...]` for the hypothesis of an induction
  on `x`, and `h_K[...]` with no index): the instance of a fact of the step at given terms. The indices in
  parentheses go to its leading universals over indices, in order; each datum goes to the universal over a point (a
  tuple of `NN` given by a formula in its coordinate), over a number, or over an object of a type row (a bundle, a
  point) given by its name in scope (`ih_k[A := E, u := u2]`), of that name, the names that the fact binds
  renamed first, so that a free name of the formula is captured by nothing. Where the goal is no implication, each
  premise of the instance is a fact of the step by name (as `V` names a fact up to the names it binds), given to the
  instance in order; none is searched. A sum whose term carries the indicator of its index at a given point is
  collapsed to the term at that point by a fixed list of rewrites (`Finset.sum_ite_eq`), unless the goal writes that
  indicator, and the instance so written is the goal (`exact_mod_cast`): the proof states it and Lean checks it
  (`lem:zfactat`, `lem:sumupperside`);
* `cases V`: first the certificate of `V[0]`, where it is exact with the conditionals that the facts of the step
  decide by name read at their branches (as for `V[...]`), so that no case is split (`lem:zcondname`); else `max`,
  `min` and `|x|` written as conditionals, every conditional of the goal and of the hypotheses
  split (`split_ifs`), each case closed as by `V`; the bracket of a conjunction is first the bracket of its first part
  around the bracket of the rest (`ite_and`), so that `iverson(P, Q) = iverson(P) * iverson(Q)`;
* `sum[W]`: a relation of two sums over the same range, or of a sum and `0` (`=`, `<=`, `>=`), term by term,
  with `W` (default `V`) for one term, at whose index the words read by relation in the term are instantiated, and,
  over Mathlib, the hypotheses `forall r in NN>=1 : r <= K => P(r)` of a sum over `1..K`; over Mathlib,
  `sum` also reads a law of ranges, for a sum or a product over `lo..hi`, either side: the last term split off,
  `(sum j in lo..K + 1, F) = (sum j in lo..K, F) + F(K + 1)` (`Finset.sum_Icc_succ_top`, the step of an induction
  `ind[n; W; W']` on a sum over `lo..n`), the first term (`Finset.add_sum_Ioc_eq_sum_Icc`), two consecutive ranges
  (`Finset.sum_Ico_consecutive`), one term (`Finset.Icc_self`), an empty range (`Finset.Icc_eq_empty_of_lt`) and one
  range written two ways, each bound the same polynomial in the counts, `a * (b + 1 + 1)` and `a * (b + 1) + a`
  (`Finset.sum_congr` over the two ranges equal by `ring1`, `lem:qsum`(scale)),
  each bound by its index term (as for `term[J]`), the two sides then the same up to beta and the numerals of the
  indices (`rfl`; `lem:zrangelaw`). A goal with a range of numerals `lo..hi`, `hi < lo`, is read first with that
  range empty, the sum 0 and the product 1 (`lem:zrangelaw`(core empty)). Three more laws of ranges: the
  index shifted by an offset `o` free of it, `(sum j in lo..hi, F(o + j)) = (sum c in o + lo..o + hi, F(c))` or with
  `j + o` and `lo + o..hi + o`, either side, each bound written so or a numeral of that value
  (`Finset.map_add_left_Icc`, `Finset.map_add_right_Icc`, `Finset.sum_map`; not where the Lean term reads its index
  cast to Q); a term free of the index, `(sum j in lo..hi, t) = r * t` (or `t * r`), `r` a count with `r + lo = hi +
  1` (`Finset.sum_const`, `Nat.card_Icc`, `Nat.sub_eq_of_eq_add` by `ring1`); and a sum over a range at most the sum
  of the same term over a larger range, `(sum j in lo'..hi', F) <= (sum j in lo..hi, F)` (or `>=`), `lo <= lo'` and
  `hi' <= hi` by their index terms, `W` proving `0 <= F` at an index of `lo..hi`
  (`Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.Icc_subset_Icc`; `lem:zrangeshift`);
* `ind`: a relation of terms with sums over one range `1..K` (or `0..K`), `K` a name with no hypothesis on it, by
  induction on `K`: the least `K`, then the step from `n` to its successor with the relation at `n` (`ih`) as a
  hypothesis, the sums at `n` being atoms; each case by `V` (linearity, constant factors and terms); over Mathlib
  the step also has the sign of each sum at `n` and of its term at `n + 1`, built from the signs of the atoms (a
  power of a base at least 0, which `positivity` does not read from a hypothesis: `pow_nonneg`,
  `Finset.sum_nonneg`), and a hypothesis over every natural number (`forall j in NN : P(j)`, the tie of each term)
  is read at the least index and the base in the first case and at the new index in the step, each case closed
  with it as an exact combination (`linear_combination ih + h`);
* over Mathlib, `ind[n; W; W']`: induction on the natural binder `n` of the row, for any goal (an existential, a
  relation, a universal over points); `W` proves the case 0 and `W'` the step from `n` to `n + 1`, which reads the
  goal at `n` as a fact `ih_n` (an existential or a conjunction destructed first, its witnesses under the names it
  binds, for `logic`, `with` and `take`). A binder of `NN>=k` starts at `k` (`Nat.le_induction`). No hypothesis of
  the row and no other binder may depend on `n` (they would have to be generalized: refused). A coordinate in an
  exponent, `2^(l * A_(i))`, indexes its tuple as anywhere else, so `ind` on a product over the coordinates splits
  off the last factor;
* over Mathlib, on the coordinates and the boxes: `sum[W]` also compares two sums over the coordinates (or over one
  box) term by term, with the hypotheses `forall i : P` at the index, and over a box the hypotheses `forall w in X :
  P` over the type `X` of its points at the point (`lem:zsumfac(boxfact, boxwith)`), the point's place in the box
  as the fact `forall i : u_(i) <= b_(i)`, and the term by any word of a goal (`with`, `cases`, `take`); `ind` on sums over the coordinates of tuples of
  length `n` (`n` a name) is the induction on `n`, the tuples and the hypotheses over every coordinate generalized:
  the case 0 by `simp`, the step with the last coordinate split off (`Fin.sum_univ_castSucc`) and the relation at the
  first `n` coordinates (`Fin.init`); `box` compares a count over a box, `sum u <= b, iverson(R)` or
  `sum u <= b, 1`, with the points of a box `prod i, (c_(i) + 1)` (`Pi.card_Icc`, `Finset.card_le_card`): from above
  when every point of the cut lies under `c`, from below when every point under `c` lies under `b` and meets `R`
  (`box[W]`: `W` for `R`), and the equation `sum u <= b, 1 = prod i, (b_(i) + 1)`; the goals at a point are closed
  by arithmetic with the hypotheses at the coordinate, a term of a sum over the coordinates at most the sum
  (from above) and each such sum monotone in the point (from below); `count` evaluates a goal at fixed values: each
  tuple of `NN^n` fixed by a hypothesis `forall i : b_(i) = c` (`c` a numeral) is substituted and the closed goal is
  decided in the kernel (`decide +kernel`); `inj` compares two counts over boxes,
  `sum u <= b, iverson(R) <= sum v <= c, iverson(S)`, by an injective relation
  (`Finset.card_le_card_of_forall_subsingleton`), from two hypotheses: the totality
  `forall u in T : P => exists v in T' : Q` (the relation is `Q`, which bounds `v` by `c` and gives `S`; a count in
  `S`, `sum w <= b, iverson(R')`, is read in `Q` as the goal reads it) and the
  injectivity `forall u, w, v in ... : P' => forall i : u_(i) = w_(i)`, their premises read from the points
  (`tauto`), each a hypothesis or a fact of `with`; the relation needs no map of tuples; `fibres` splits a count
  over a box by the value of a map into the points of another box (`Finset.card_eq_sum_card_fiberwise`),
  `sum u <= b, iverson(R) = sum s <= B, sum u <= b, iverson(R, S(u) = s)` (or `<=`), `S` a function of the points
  (`type Sizes(n, r) := Exponent(n) -> Exponent(r)`), from a hypothesis that the map sends each point of the cut into
  the box, `forall u in T : P => forall s in T' : S(u) = s => forall X : s_(X) <= B_(X)`, its premise read from the
  point (`tauto`; `pivots`, `thm:pivots(core weight)`);
* sums over a cell (`sec:lattice` of `qpp/examples/vocabulary.qpp`; the forms refused in
  `qpp/examples/refused/lattice.qpp`). `sum k in a..b : C_1, ..., C_J, t`, `sum i : C_1, ..., C_J, t` and
  `sum u : C_1, ..., C_J, t` sum `t` over the points of the range (an index range, the coordinates of the tuples `i`
  indexes, the positive lattice points `u` of `(NN>=1)^n`) at which every clause holds. A clause is a comparison by `<`, `<=`, `=`,
  `>=`, `>` (a chain is one clause per link) or a family of them, `forall j : A(j) rel B(j)` over the coordinates or
  `forall j in NN>=1 : j <= B => A(j) rel B(j)` over a bounded index; no `!=`, `or`, `not`, `=>` and no deficit in a
  clause (a complement or a union of cells is a sum of cell sums), and no `iverson` of the point in `t` (the
  comparison is a clause). On the lattice the first clause bounds the content by a level, `sum i, c_(i) * u_(i) + O
  rel L` (`rel` one of `=`, `<=`, `<`; `c` a tuple of `(NN>=1)^n`, or every weight 1 and the length of `u` read from
  a tuple that it meets; `O`, `L` in `NN` free of `u`), so that `u_(i) <= L` and the cell lies in the box
  `[1, L]^n`. The range of the point is a parameter: `sum u in T : ...` names the type of the point, needed when the
  point meets no other tuple, a tuple type of `(NN>=1)^n`, or of `NN^n` (the box `[0, L]^n`: a zero, listed in
  `modules/zeros.toml`, only to restate a row that already holds it); `PosGrid(r)` and `Grid(r)` of `qpp/examples`
  are examples of the two. Over Mathlib the sum is `Finset.sum`
  over `Finset.filter` of the clauses on the holder (`Finset.Icc a b`, `Finset.univ`, `Finset.Icc 1 (fun _ => L)` or
  `Finset.Icc 0 (fun _ => L)`); over the kernel it is the sum over the holder of the indicator of the clauses times
  `t` (for the positive points the box from 0 with every coordinate at least 1, which the transfer reads as the box
  from 1), generated, its false branch the kernel's absent. The words on cells: a point `u` of a cell meets each clause,
  the fact `h_ck_u` (the clause `k` at `u`), which `sum` and `sum[W]` read when they compare two cell sums term by
  term; `inj` compares two lattice cells, `(sum t : C_1, ..., C_J, 1) <= sum u : D_1, ..., D_K, 1`, from the
  totality `forall t in T : C_1, ..., C_J => exists u in T' : Q_1, ..., Q_p, D_1, ..., D_K` and the injectivity
  `forall t, t2 in T : forall u in T' : C(t), C(t2), Q(t, u), Q(t2, u) => forall k : t_(k) = t2_(k)`
  (`Finset.card_le_card_of_forall_subsingleton`), each image placed in the box of its level from its content clause
  (`Finset.single_le_sum`, each weight at least 1; the second cell over `NN^n` for now); `simplex` counts the wall
  `sum k, t_(k) = m` of the lattice of `NN^r`, `(sum t in T : sum k, t_(k) = m, 1) = binom(m + d, d)` with
  `r = d + 1` a fact by name (the weak compositions, Mathlib's `Finset.card_finsuppAntidiag_nat_eq_choose`, and
  `Nat.choose_symm_add`), and the positive wall at the level `m + r`, `(sum t in T : sum k, t_(k) = m + r, 1)
  = binom(m + d, d)` (its points are `s + 1` for the weak compositions `s` of `m`: `Finset.card_bij`, each `t_(k) =
  s_(k) + 1` by `Nat.exists_eq_add_of_le'`, no subtraction); `trichotomy`
  splits a cell sum by one comparison `A`, `B`: into the three cells with one more clause `A < B`, `A = B`, `B < A`,
  or a clause `A <= B` into its chamber `A < B` and its wall `A = B` (`lt_trichotomy`, the cells read term by term
  through `Finset.sum_filter`). A part left out is empty: refuted at each point by the bound of the range (`b < m`
  against `m <= b`), or, as `trichotomy[W_1; ...; W_K]`, by a certificate `W_k` of `1 <= 0` from the clauses at the
  point (`h_ck_m`), its range (`m_rng`), the families over the range at the point, and the comparison of the part
  (`h_tri_m`); an empty cell is never written alone. `same[h_1, ..., h_K]` (or `same`, with no tie) reads two cells
  over one holder with one term as one cell, their clauses agreeing at each point, in order or up to their order,
  once the named ties are read there (a tie, a family over the coordinates, or a family over the range whose premises
  are its bounds; `Finset.filter_congr`, the conjunction up to order by `and_comm`, `and_left_comm`, `and_assoc`); the
  generator checks the agreement on the clauses before it writes any Lean. A point of a cell over a range is a point
  of the range: `sum[W]` and `trichotomy[W]` give `W` its range `m_rng` and the families over the range at it. A cell
  over a range with a clause `m = p` among its clauses is its term at `p` by `sum`, the other clauses at `p` facts by
  name (`Finset.sum_eq_single_of_mem`, the bounds of `p` facts by name); over the coordinates the one clause `i = k`.
  An index `i` over the coordinates has `1 <= i` and `i <= n` as facts by name. The exchange `sum j, (sum m in a..b : C, D(j),
  t) = sum m in a..b : C, (sum j : D(j), t)`, `C` free of `j`, is read by `sum` (`Finset.sum_comm`, the clauses as
  indicators);
* over Mathlib, `pascal`: `sum j in 0..J, binom(j + k, k) / 2^j <= 2^(k + 1)` by induction on `k` for every `J`
  (Pascal's rule shifted, `S_(k+1)(J+1) = S_k(J+1) + S_(k+1)(J)/2`, and the absorption of the last term, the terms at
  least 0; the case `k = 0` the geometric sum), and `sum j in 0..J, (j + 1)^k / 2^j <= (prod i in 1..k, i) *
  2^(k + 1)` from `(j + 1)^k <= k! binom(j + k, k)` (`Nat.pow_succ_le_ascFactorial`,
  `Nat.ascFactorial_eq_factorial_mul_choose`); a file whose proofs use it imports
  `Mathlib.Algebra.BigOperators.Ring.Finset`. The module fixtures read `binom` as the checker's `choose`;
* over Mathlib, `choose`: `(m + 1)^d <= binom(m + d, d) * prod i in 1..d, i` (either order of the factors, or
  `>=`), the natural goal of Mathlib's `Nat.pow_le_choose` with the factorial written as a product
  (`Finset.prod_Ico_id_eq_factorial`), also as the clause of a `with` (`lem:zchoose`); a file whose proofs use it
  imports `Mathlib.Data.Nat.Choose.Bounds` and `Mathlib.Algebra.Order.Interval.Finset.SuccPred`;
* over Mathlib, `simplex`: the number of lattice points of a box `[0, c]` of `NN^r` whose coordinates add up to
  `m`, `(sum t <= c, iverson(sum k, t_(k) = m)) = binom(X, Y)` (either side), from `forall k : m <= c_(k)`: the
  weak compositions of `m` into `r` parts, `binom(r + m - 1, m)` (Mathlib's
  `Finset.card_finsuppAntidiag_nat_eq_choose`, by the bijection `Finsupp.equivFunOnFinite`; each coordinate of a
  composition is at most `m`, so the box does not cut it), with `X = r + m - 1` and `Y = m` or `Y = r - 1` checked
  by `omega` (`lem:zsimplex`); a file whose proofs use it imports `Mathlib.Algebra.Order.Antidiag.FinsuppEquiv`;
* over Mathlib, `parity`: the even and the odd points of a box `[0, e]` of `NN^n` with `forall i : e_(i) <= 1` (the
  subsets of a set of `n` members), the parity of a point `u` read by its halves `q in 0..n`: `EVEN(u) = sum q in
  0..n, iverson(sum i, u_(i) = 2 * q)` and `ODD(u)` the same at `2 * q + 1`. Two rows: `(prod i, x_(i)^(e_(i))) +
  (sum u <= e, ODD(u) * (prod i, w_(i)^(u_(i)))) = sum u <= e, EVEN(u) * (prod i, w_(i)^(u_(i)))` from `forall i :
  x_(i) + w_(i) = 1`, and `(sum u <= e, ODD(u)) = sum u <= e, EVEN(u)` from `1 <= sum i, e_(i)`. The proof reads
  each factor `x_(i)^(e_(i))` as the sum of `(-w_(i))^t` over `t in 0..e_(i)`, expands the product by the law of a
  box (`Finset.prod_univ_sum`), and reads the sign `(-1)^m` of a point of size `m <= n` as `EVEN - ODD`
  (`Nat.even_or_odd'`, `Finset.sum_ite_eq`); the rows are the expansion of a product of differences over the
  subsets (`Finset.prod_sub`) stated over Q>0 (`lem:parity` of `parity`). A file whose proofs use it imports
  `Mathlib.Algebra.BigOperators.Ring.Finset`;
* over Mathlib, `dyadic`: `exists z in NN : 1 / b^(z + 1) < w, w <= 1 / b^z` (`b` a numeral at least 2, `w` free of
  `z`), Mathlib's `exists_nat_pow_near_of_lt_one` at `1 / b` (`one_div_pow`), the bounds `0 < w` and `w <= 1` proved
  by `V`, also at a coordinate under `forall i` (`lem:zdyadic`); a file whose proofs use it imports
  `Mathlib.Algebra.Order.Archimedean.Basic`;
* over Mathlib, `choice`: a witness at each coordinate as one tuple, `exists z in T : forall i : P(i, z_(i))` (or
  `forall k : forall i : P(k, i, z_(k)_(i))` for a tuple of tuples) from a fact `forall i : exists x in S : P(i, x)`
  over the same coordinates, `S` one of `NN`, `QQ>=0`, `QQ>0` (`Classical.choose`, a rational witness with its sign);
  the fact a hypothesis or a step of `with` (`lem:zchoice`); over points, a map `exists S in T : forall u in X :
  forall s in Y : S(u) = s => P(u, s)` (`T` a type row of functions from `X` to `Y`, as `Sizes(n, r) := Exponent(n)
  -> Exponent(r)`) from a fact `forall u in X : exists s in Y : P(u, s)` (`Classical.choose`);
* over Mathlib, `enum`: the lattice points of a box `[0, b]` of `NN^n` (or `[0, c]^n`, `c` free of the coordinate)
  that meet a row `R` as a list without repeats, `exists N in NN : exists e in T(N, n) : (forall k : (forall i :
  e_(k)_(i) <= b_(i)), R(e_(k))), (forall u in X : (forall i : u_(i) <= b_(i)), R(u) => exists k : forall i :
  e_(k)_(i) = u_(i)), (forall u in X : (sum k, iverson(forall i : e_(k)_(i) = u_(i))) <= 1)` (`T(N, n)` a type of
  tuples of `N` tuples of `NN^n`): the filtered box enumerated (`Finset.equivFin`); `reindex`: with those three facts
  in scope, `(sum k, F(e_(k))) = sum u <= b, iverson(R(u)) * F(u)` (either side, the factors in either order), the
  list mapped onto the cut box injectively by the third fact and onto it by the second (`Finset.sum_nbij`); the term
  of the list must read the term of the box at `e_(k)` (`lem:zenum`);
* over Mathlib, `powdiff`: the bounds of a power difference, one per conjunct: `a^p * s <= a * W` (with `a <= l`)
  and `b * W <= b^p * s` (with `l + s <= b`), from the tie `l^p + p * W = (l + s)^p` among the hypotheses, `p` a
  natural number at least 1, `0 < a`, `0 <= l`, `0 < s`: that is `a^(p - 1) s <= W <= b^(p - 1) s`, without the
  subtraction. The proof is the geometric identity without subtraction, `(sum_(i < p) (s + l)^i l^(p - 1 - i)) s +
  l^p = (s + l)^p` (Mathlib's `geom_sum2_mul_add`, the 2 a subscript), each of its `p` terms between `a^(p - 1)`
  and `b^(p - 1)` (`pow_le_pow_left0`, the 0 a subscript). Under binders over coordinates (`forall iota : forall i :
  ...`, see below) it reads the tie at the indices of the goal. A file whose proofs use it imports `Mathlib.Algebra.Ring.GeomSum`;
* over Mathlib, `dual`: weak duality from a tie of forms, `(sum i, c_(i) * v_(i)) >= sum iota, y_(iota) * e_(iota)`
  from the tie `forall i : c_(i) + (sum iota, y_(iota) * N_(iota)_(i)) = sum iota, y_(iota) * P_(iota)_(i)` and the
  constraints `forall iota : (sum i, P_(iota)_(i) * v_(i)) >= (sum i, N_(iota)_(i) * v_(i)) + e_(iota)` (a
  hypothesis or the premise of an implication of the goal, a part of a conjunction too, the first universal whose two
  sides read a form, a sum over the coordinates alone or plus a term, and among several the first whose smaller side
  adds the `e_(iota)` of the goal; constraints between natural numbers are read in `QQ` through their casts,
  `lem:latdual(nat, match)`), `y_(iota)` at least 0: each constraint times its price,
  summed (`Finset.sum_le_sum`), the two sums swapped (`Finset.sum_comm`), the tie at each coordinate. With an offset,
  `(sum i, c_(i) * v_(i)) + (sum iota, y_(iota) * a_(iota)) >= ...` from the constraints `(sum i, P_(iota)_(i) *
  v_(i)) + a_(iota) >= ...`, the offset is carried through each constraint. With a form on the right, `... >= (sum
  i, d_(i) * v_(i)) + sum iota, y_(iota) * e_(iota)` from the tie `forall i : c_(i) + (sum iota, y_(iota) *
  N_(iota)_(i)) = d_(i) + sum iota, y_(iota) * P_(iota)_(i)`, the form is carried to the right (`lem:latdual`). The
  forms are on both sides, so no subtraction enters; a file whose proofs use it imports
  `Mathlib.Algebra.BigOperators.Ring.Finset`.
  A goal over coordinates, `forall i : P`, is read by its index introduced (`intro i`) and the hypotheses over the
  same coordinates instantiated at it (`have h_1_i := h_1 i`), those inside a conjunction too (`(hi1).1 i`), for
  every word. A universal goal whose name is a local in scope that a fact reads (the witness `i` of an existential
  that `with` destructed) introduces its name as `i_2` (`i_3`, ...), as `logic` names a clashing witness, so the
  facts on the old `i` keep their meaning and their Lean text; the words under the goal read `i_2` (`lem:zfresh`);
* over Mathlib, `cells`: two lists of boxes compared by their weights, `sum k, prod i, W_(k)_(i) <= sum k, prod i,
  W'_(k)_(i)`, from `1 <= q_(i)`, the ties `l_(k)_(i)^q_(i) + q_(i) * W_(k)_(i) = (l_(k)_(i) + s_(k)_(i))^q_(i)` of
  both lists (corners at least 0, sides in `QQ>0`), the separation of the first, `forall w in Point(n) : sum k,
  iverson(forall i : l_(k)_(i) < w_(i) < l_(k)_(i) + s_(k)_(i)) <= 1`, and its covering by the second, `forall k :
  forall w in Point(n) : (forall i : l_(k)_(i) <= w_(i) <= l_(k)_(i) + s_(k)_(i)) => exists j : forall i :
  l'_(j)_(i) <= w_(i) <= l'_(j)_(i) + s'_(j)_(i)`; each hypothesis is found by its shape (a row of a relation too).
  The proof counts cells. It takes a common denominator `D` of the corners and sides of both lists (the product of
  their denominators). A side of `D` grid units is the sum of the weights of its cells, `((u + 1)/D)^q - (u/D)^q`
  over `q` (a telescope, `Finset.sum_range_sub`), and a box is the sum over its cells of their products
  (`Finset.prod_univ_sum`). A cell of the first list lies in at most one of its boxes, by the separation at its
  centre `(2u + 1)/(2D)`, and in some box of the second, by the covering at the centre, since `2 D l' <= 2u + 1 <=
  2 D (l' + s')` lies between even numbers. The cell weights are at least 0. The difference is in the proof only, and
  the statement keeps its signs. A file whose proofs use it imports `Mathlib.Algebra.BigOperators.Ring.Finset`,
  `Mathlib.Data.Fintype.Pi`, `Mathlib.Algebra.BigOperators.Field` and
  `Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset`;
* over Mathlib, a relation in a conclusion, `(l #inner s ...)`, is proved by its fields (the anonymous
  constructor of its structure): one word per field in the order of the row, or one word per row with the bounds of
  its declarations by name first (a fact that states one, or its sign by its term), then by arithmetic; one
  reference proves it whole, and one word `V` or `logic` takes the fact
  in scope that states it (a step of `with`), else closes its fields from the facts; whatever the words, a fact
  in scope that states the relation as it is (a witness of a destruct, a step of `with`) closes it (`exact`). A name
  that a field binds and that is free in an argument is renamed in the instance (`C` bound in `#coefficient` at the
  region `C`: `C__1`), so that the argument is not captured; `take` still gives it by its own name (`lem:zcap`);
* over Mathlib, `take[x := t, l_(k)_(i) := F, ...; W]`: the witnesses of the existentials that lead the goal, in
  their order, then the word `W` (default `V`) on the rest. A number by a term (its bound, `NN>=1` or `QQ>0`, by
  arithmetic; a product of coordinates in `QQ>0`, alone or over or times a positive term, by `Finset.prod_pos`,
  `lem:zprodpos`); a tuple `x_(i) := F` or a tuple of tuples `l_(k)_(i) := F` by a formula in its indices (in Lean
  `fun k i => F`, each coordinate in `QQ>=0` or `QQ>0` with its sign built from the signs of the atoms of `F`), or by
  a name; a tuple or a tuple of tuples by `join(a, b)`, the coordinates (rows) of `a` then those of `b`
  (`Fin.append`). The witnesses are read into the rest: a coordinate of a formula is the formula at the index. The
  formula stays in the proof: no statement writes it. A formula that does not read the row of a tuple of tuples
  (the same box at every row) leaves the index of the rows with its range; over the rows of a list of one box
  (`Fin 1`) a universal is introduced as usual, an existential has the only row as its witness, and a sum or a
  product in a relation goal is its term (`Fin.sum_univ_one`). A bundle is given by all its parts, in any
  order and with no default: `take[Pr.P_(iota)_(i) := F, Pr.op_(iota) := G, Pr.d := t, ...; W]`, each part as a
  witness of its own type is given above (a part in `NN` by a term); the witness is the anonymous constructor of the
  bundle's structure, and the parts are read into the rest (`lem:zbundle`(build), (cert)). A bundle given by its
  parts is read through them, or whole as the argument of a relation, whose fields then read its parts
  (`lem:regular`(out) in `regular`: `pi #prices Pr #content c #value r / 2` with `Pr` built by `take`); `unfold` reads
  such a relation by its iff (`refine (R_iff _ ...).mpr ?_`) and the parts in;
* over Mathlib, a goal over the rows of a join is split at the seam: `forall k : P` into the two halves, each by the
  same word (`Fin.forall_fin_add`), `sum k, F` into the sum of the two sums (`Fin.sum_univ_add`), `exists k : P` into
  the disjunction of the two (proved in the file from `Fin.addCases`), the coordinates read by `Fin.append_left` and
  `Fin.append_right`; an index over the rows of a join used outside its coordinates is refused;
* over Mathlib, `logic` (`logic[W]`): a goal that first-order logic gives from the hypotheses. An existential or a
  conjunction that the goal introduced is destructed. Each hypothesis read as a rule (binders over points, objects or
  indices; memberships; premises) is applied when its premises are facts: the first matched with a fact of the round
  before (first those the goal introduced: a premise, the membership of a point; the binders by unification, up to
  the names that the sums bind, the names a substitution would capture renamed first), the others found among the
  facts, so that every application elaborates; in the first round each rule is also read at the point that the goal
  names, its conclusion matched with the goal binding its binders and each premise then a fact at that point (`b <= Q`
  by `0 <= Q`, not by the first fact `q <= Q`; `lem:zgoalpoint`). Its conclusion is destructed (an existential gives its witnesses, named as it binds them, with a
  suffix `_2`, `_3`, ... when a name is taken; a conjunction its parts) or kept as a fact; the same conclusion is
  not drawn twice (a rule and its instance at an index). A hypothesis `S subseteq T` is applied to each membership
  in `S`, a membership of a union or an intersection read as a disjunction or a conjunction. A universal over a type
  with no premise (`forall w in Point(n) : P`) is instantiated at each object of that type in scope when `logic`
  starts. Up to three rounds; an enclosing `logic` is not repeated. Then the word `W`, which reads the witnesses by
  their names; with no word, the goal by name first (the fact that `logic` drew, or a part of it, that states it, as
  for `V`); else the goal as an instance of a fact read as a rule, with no premise needed to apply it: its binders
  bound by matching its conclusion, or a conjunct or a link of it, with the goal (`h c (c + 1)`, `(h i j).2`), the
  binders the match leaves free by its premises matched with facts, each premise, membership and bound of a number
  then by name, and a field of a relation fact read as its projection (`h.h1 j`; `lem:zrulenamed`); else from a
  disjunction of the step whose every branch gives the goal or contradicts a fact (the negation of a case split,
  `A => not B` for a conjunction), by `Or.elim` with each branch by name (`lem:zdisjnamed`), or from two facts of the
  step that contradict each other (`False.elim`); an equation of one term with itself by `rfl` (`True.intro` once a
  witness given by its formula is read); then `tauto`. Facts and goals compare up to the names they bind, those
  of a sum over a whole index too, and `a >= b` as `b <= a`; a field of a relation fact is named by its projection
  (`lem:zfactkey`). The bound of a number that a rule binds (`k <= y` in `NN>=k`, `0 < y` in `QQ>0`) is given
  by name: a fact that states it, the bound `hp_y` of a count, the sign of a mass. Before the rounds, each hypothesis in scope that is an existential or a conjunction
  (of the row, of the given, a row of a relation hypothesis) is destructed once, as a copy. An existential over a
  number set (`QQ>0`, `QQ>=0`, `NN`, `NN>=k`) gives its witness with its bound as a fact (`0 < d`, `1 <= M`), in
  `logic` and in `with`. A universal over the coordinates that ends a rule, after its last membership or premise, is
  part of its conclusion (`forall w in B : forall i : P` gives `forall i : P` at each point of `B`), and a fact over
  the coordinates that `logic` draws is instantiated at each index the goal introduced over the same coordinates. An
  existential `exists v in B : forall i : v_(i) = w_(i)` is not drawn for a point `w` that already has a membership
  in `B`; destructed (by `logic`, `with`, `cases` or `ind`), with `w` a point in scope of the type of the points of
  `B`, it is the membership of `w` itself: `v` is identified with `w` (`funext` over the coordinates, the casts
  injective, then `subst`), so the rules over `B` apply at `w`. A rule that the goal or the proof brought in (a fact of
  a region named by `take`, a step of `with`) is applied in the first round to every fact and membership in scope,
  not only to the new ones. A binder over a number set is a binder of the rule, the bound of `NN>=k` or `QQ>0` a
  premise proved by arithmetic; a premise of several conjuncts, `(A, B, C) => D`, is matched conjunct by conjunct,
  each with a fact, and passed as one anonymous constructor. A rule that ends in an equivalence (`forall y in X : A
  <=> B`, a region by its characterization) is read as its two implications. A premise `exists v in B : forall i :
  v_(i) = y_(i)`, the membership of a point as the rows write it, is matched with a membership of a point in `B`
  (the point its own witness). An existential or a conjunction that an enclosing `logic` destructed is not
  destructed again: its parts are facts. The parts of an existential or a conjunction that `logic` destructs are rules
  as the hypotheses are (`forall y in R : P` inside a premise applies at a membership in `R`). A number binder of a
  rule may be matched to a term (`L := L' + D`), passed as it is. A relation fact (a step of `with`, a witness) gives its fields that are
  rules (`h.h1`, ...). With the default word, a membership of a union `B_1 cup B_2` is split by cases (`rcases`),
  each case a `logic` of its own with the membership in its region, so the rules over that region apply at the
  point; a case closes by the goal as a fact, by arithmetic (`exfalso; linarith`) or by `tauto`. A membership known
  already (in scope, or a union split in an enclosing case) is not drawn again, so a cycle of inclusions
  (`B subseteq B_1 cup B_2`, `B_2 subseteq B`) ends. An existential or a conjunction that the goal introduced is
  destructed from a copy: it stays a hypothesis for the words after `logic`, and its parts that are existentials or
  universals stay facts as they are (by their projections), so a rule whose premise has the same parts applies. A
  premise that is an existential over an index, `exists i : P_1, P_2`, is also given by its parts at an index in
  scope, each a fact (an existential destructed, a case of `cases`), as `<j, h_1, h_2>`. The premises and the facts
  are matched after the arithmetic of numerals that `push_cast` does on the goal (`0 + x`, `1 * x`, `x^1` as `x`,
  `0 * x` as `0`, `x^0` as `1`, numerals added and multiplied: the first case of `ind` reads `2^((0 + 1) * a_(i))`
  as `2^(a_(i))`), the argument then passed through the same arithmetic (`simpa only`). An equation of natural
  numbers `L = t` or `t = L` among the facts (a premise, a destructed fact, a step of `with`), `L` a name that the
  goal reads and that the given does not bind, `t` free of `L`, is substituted (`subst L`, which removes the
  equation, then `push_cast` at each fact that names `L`, by its name, and at the goal, so a cast of `L' + D` reads as
  the sum of the casts, as a `with` clause writes it): the
  goal and the facts read `t` in place of `L` (a fact that binds `L` again, the hypothesis of an induction, keeps its
  binder), so a relation at the level `L` is a fact at the level
  `L' + D` as it is (`lem:zsubst`); a goal that binds a name of `t` keeps `L`, and a part of a bundle (`Cl.m`) is not
  a name and is not substituted. On a goal `A subseteq B` (two regions
  of the same points), the point `w` (`w_2`, ... when `w` is taken) and its membership in `A` are introduced first,
  and the goal is the membership of `w` in `B` as the rows write it, a union `B_1 cup B_2` read as the disjunction of
  the memberships; the word after the rules names the point (`with[K(w) <= 2 by V; logic]`, `cases[K(w) <= 1; ...]`,
  `lem:zsubset`), also in a side goal `R subseteq S by logic`;
* over Mathlib, `cases[P; W1; W2]`: a case split on the clause `P` (in the names in scope, as for `with`), once the
  binders and premises of the goal are introduced: `W1` proves the goal with `P` as a fact, `W2` with the negation of
  `P` as a fact, pushed in (a relation flipped, `not a <= b` is `b < a`; `forall` and
  `exists` swapped; `not (A, B)` is `A => not B`; `not (A => B)` is `A, not B`; `not n = 0`, `n` a natural number,
  is `1 <= n`; `not a = b` otherwise is `a != b`; a relation is negated as it is, `not (s #feasible Pr #level L)`)
  by one proof term, a lemma for each step (`not_le`, `not_lt`, `Nat.one_le_iff_ne_zero`, `Classical.not_not`,
  `Classical.not_imp`, `not_and`, `Classical.not_forall`, `not_exists`), with no tactic;
  an existential or a conjunction among them is destructed first.
  A universal case clause over an index holds at each index in scope over the same range (`hc1_i`); an index that
  the destruct names (the witness of `exists i : ...`, named apart as `i_2` when `i` is in scope) carries the facts
  over every index (`lem:zcase`). Printed `\mathrm{cases}[P;\ W_1;\ W_2]`, which latex2qpp reads back;
* over Mathlib, a universal goal over several names, `forall L, kappa in NN : P` (no bound on the set), is
  introduced name by name, for every word but a reference, which proves it whole;
* over Mathlib, `with[CLAUSE by W; W']`: a step, once the binders and premises of the goal are introduced. The
  clause, written in the names in scope (those of the row, those the goal introduced, the witnesses of `logic` or of
  an earlier `with`), is proved by `W` (`have`), then is a fact for `W'` on the goal; a clause that is an
  existential or a conjunction is destructed first, as `logic` destructs one. `take` also gives an index (a name in
  scope) and a point of a region (a point in scope, with its membership);
* over Mathlib, `chain[A R B by W; R' C by W'; ...; W'']`: a chain of relations (`R`, `R'` among `<=`, `<`, `=`, `>=`,
  `>`), each link a step of `with`. A later link `R' C by W'` is the clause `B R' C`, `B` the right side of the link
  before it, so each term of the chain is written once. The word `W''` proves the goal from the links; left out,
  the links are composed as `calc` composes them (`Trans.trans`), and `V` runs only if that fails. A link's word may be a `with` of its own, for a fact that only that link needs. The Lean is that of the
  nested `with` steps;
* over Mathlib, `unfold[W]`: the relations of the goal read by their fields, wherever they stand, inside a
  bracket too: `simp only [R_iff]`, then `W` on that goal. Two sides that read the same once unfolded are equal,
  and `W` (`V` or `eq`) is then not run. A relation is a structure, decided classically inside a bracket
  (`iverson((s #feasible Pr #level L))`); as a hypothesis it is read by its fields as before (`h_k.h1`), and
  `unfold` also reads the relations that stand as fields of a given one (`h_k_1.h1`, the prices inside a
  certificate). A goal that is a relation is proved field by field; with `logic`, the relation is first tried as
  a whole, as one fact may give it;
* over Mathlib, a region by a predicate, `take[R := {w in X : P}; W]`, in a proof only: `R` is a new name of a type
  row `set(X)` (`X` a type row of tuples), the set `{w : X | P}` in Lean (`obtain` with its membership by
  `Iff.rfl`), with two facts in Q++ terms for `logic`, `take` and the references: `forall w in R : P` and `forall w
  in X : P => exists v in R : forall i : v_(i) = w_(i)` (the membership of a point as the rows write it). A
  reference takes `R` as data (`lem:y(k)[B := R]`), so a rule over regions applies to a region the proof names.
  Everywhere else `{w in X : P}` is refused (a row, a given, a definition, a relation, a context, a vocabulary line,
  a clause of `with`): a statement takes a region variable with its characterizing hypothesis. Refused cases:
  `qpp/examples/refused/terms.qpp`;
* over Mathlib, `sum[W]` first brings a factor free of the index into its sum (`c * sum k, F` is `sum k, c * F`,
  `Finset.mul_sum`; `Finset.sum_mul`) and merges two products over the same coordinates (`(prod i, A) * (prod i,
  B)` is `prod i, A * B`, `Finset.prod_mul_distrib`) and adds two sums over the same range (`(sum k, F) + (sum k,
  G)` is `sum k, F + G`, `Finset.sum_add_distrib`, the index of the second renamed to that of the first), on either
  side, then compares term by term; a product of powers of one base free of the index, `prod k, c^(e)`, is the power
  of the sum of the exponents, `c^(sum k, e)` (`Finset.prod_pow_eq_pow_sum`), unless both sides are products over
  the same range, and a relation with no sum or product left is proved by `W` (`lem:zsumfac(powsum, powd, powle)`);
  a side `r * t` (or `t * r`) against a sum over coordinates `sum j, F`, `r` the length of the tuples that `j`
  reads and `t` free of `j`, is the sum of `r` terms `t` (`Finset.sum_const`, `Finset.card_univ`,
  `Fintype.card_fin`), so `(sum j, F) <= r * x` follows from `forall j : F <= x`, and so do `>=` and `=`, in the
  type of the relation (a sum of natural numbers in Nat); a side `t^r` against a product over coordinates `prod j,
  F` is the product of `r` terms `t` the same way, for `=` (`Finset.prod_const`; `lem:zsumconst`; `sum j, x` and
  `prod j, x` themselves stay refused). At the index, a natural term with a numeral read in `QQ` (its
  casts at the leaves, so `(1 : N)` reads as the cast of 1) has the casts of its numerals dropped (`Nat.cast_one`,
  `Nat.cast_ofNat`, `Nat.cast_zero`); over a box, a fact `forall u in X : (forall i : u_(i) <= b_(i)) => P` has its
  premise discharged by the range of the index; over a range, a fact `forall r in NN : P(r)` is read at the index
  (`lem:zsumat`); two products over
  the same coordinates, or over the same range `lo..hi` with the facts at the index as for a sum
  (`lem:exchange`(period)), are compared term by term as sums, `=` by `Finset.prod_congr`, `<=` (or `>=`) by
  `Finset.prod_le_prod₀` with each factor of the smaller product at least 0 (its sign from its atoms, else
  `positivity`; `lem:zsumfac`), and two sides that read the same close the goal. Two nested sums in the other order
  on the right, `sum x in X, sum y in Y, F` and `sum y in Y, sum x in X, G` (ranges, coordinates or the lattice
  points of a box, `X` free of `y` and `Y` free of `x`; the term of the right read with a factor brought in), are
  swapped first (`Finset.sum_comm` on the left), then compared term by term.
  An equation of two Iverson brackets is the equivalence of their conditions (`if_congr`), one word each way; an
  inequality `iverson(P) <= iverson(Q)` (or `iverson(Q) >= iverson(P)`) by `logic` is the implication `P => Q`, proved
  by the word, also at the index of a sum (`lem:zivle`), the word on each part when `Q` is a conjunction. `V`
  reads a sum as one atom when a fact writes it as it is, up to the name of its index (a sum of counts too);
* over Mathlib, `term[J]` (`term[J; W]`): `t <= sum j in lo..hi, F` from the term of the sum at the index `J`
  (`Finset.single_le_sum`): each term at least 0, its sign built from the signs of its atoms, and `lo <= J <= hi`
  by an index term where it has one (`le_refl`, a fact by name, `Nat.le_add_right`, `Nat.le_add_left`, two
  numerals, `0 <= b`, `1 <= b` from a fact `0 < b`, `a + 1 <= b` from a fact `a < b`, `k <= y` from the bound of a
  count `y`, and `a <= b` from two facts `a <= m`, `m <= b` through a name `m` of the scope, either strict
  (`le_trans`, `le_of_lt`)), else by `omega`; over the coordinates of tuples, `t <= sum i, F`, `J` is a coordinate index in scope (the witness of an
  existential; `Finset.mem_univ`); `W` (default `V`) proves `t <= F` at `J`, nothing when the two read the same;
* over Mathlib, the closer's last steps: the chains among the facts the goal brought in, split into their links; the
  signs of the coordinates in `QQ>0` of the goal and of those facts (a subtype, which `positivity` does not read), a
  quotient by such a coordinate cleared (`field_simp`); the powers of a positive base with an exponent `L + D` split
  (`pow_add`, with `mul_pow` and `mul_add` read backwards), each power positive, for the products that `nlinarith`
  forms (a fact times a sign, an equation times a power); a count (`NN>=1`) that is a factor of a product among the
  goal and the facts, at least 1 read in `QQ` (so `q * W = q * Z` gives `W = Z`); a power of a numeral base at
  least 1 is at least 1, in `QQ` and in `NN` (`one_le_pow0`, the 0 a subscript); a relation of natural numbers from
  rational facts, the goal cast to `QQ` (`Nat.cast_lt`), a non-strict goal `k <= j` read as `k < j + 1`
  (`Nat.lt_add_one_iff`), so that `k <= x < j + 1` with `x` rational gives `k <= j`; then `omega` (the truncated
  difference and `max` over `NN`, the sums as atoms) and an equation `k = j` from rational facts (`Nat.cast_inj`);
  the same is the side of `mono` (`2^k <= 2^j`). Last, an alternative that `nlinarith` closes over `QQ` with more read from the facts in scope:
  the parts of their conjunctions and chains; an exponent with a sum or a factor 0 or 1 distributed (`(l + 1) * a`
  is `l * a + a`, the products over `NN` only) and the power split (`pow_add`), each summand's power positive and at
  least 1; a quotient by a positive term cleared (`k <= x / D` gives `k * D <= x`, `le_div_iff0` and its kin, the
  positivity of `D` by `positivity` or by its bound); a maximum split by cases (`max_def`, `split_ifs`); the
  relations between natural numbers of every fact, a step of `with` too, read in `QQ`, and each natural name at
  least 0 (at least 1 in `NN>=1`); the coordinates in `QQ>=0` at least 0; a goal with a quotient cleared by its
  lemma; a goal between natural numbers read in `QQ` (`k <= j` as `k < j + 1`). Before it, a sign `0 <= t` by
  `positivity`; after it, for an equation, the equations of the facts whose left side is a name or a value
  substituted (`simp only`), an equation over every index whose left side is a coordinate at that index
  (`forall i : u_(i) = F`) too, then `field_simp` (`w'_(i) = h_(i) * w_(i)`, `h_(i) = 1 / 2^(a_(i))` give
  `2^(a_(i)) * w'_(i) = w_(i)`). An equation of the facts between a natural value and a numeral (`a_(i) = 0`) gives
  each power with that exponent at its value (`2^(a_(i)) = 1`, by `simp` with the equation), and so does an
  exponent with that value as a factor (`2^(l * a_(i)) = 1` when `a_(i) = 0`); these values then also rewrite the
  facts and the goal. A quotient by a power of a numeral base at least 1 is at most its numerator (`div_le_self`)
  and, times the power, is its numerator (`field_simp`); a power of the goal against a power of the facts with the
  same base gives the comparison of the powers when the exponents compare (`pow_le_pow_right0`); an Iverson bracket
  is split by cases (`split_ifs`); when the facts are rewritten (`simp only ... at *`), the hints become hypotheses
  first. For an equation goal, an equation of natural numbers whose left side is not a name (a product of powers
  equal to one power, `lem:zprod`) is read in `QQ` and from right to left, then the goal is a fact up to casts
  (`assumption_mod_cast`). These alternatives come after the others, so a proof the earlier ones give is
  unchanged (`lem:zquot`). A goal `b^e <= b^f` with the same numeral base `b >= 1` tries first the monotony in the
  exponent, `e <= f` from a fact, by `omega`, from `m <= n` times a factor (`Nat.mul_le_mul_right`), or by
  `linarith`;
* `pow[j]` (`pow[j; W]`): `a <= b` from `a^j <= b^j` and `0 <= b`, or `a = 0` from `a^j = 0` and `0 <= a`, with
  `j` a count and `W` (default `V`) for the powers; the certificates know `0 <= b^n` when `0 <= b` has one, and
  `a^n = b^n` when `a = b` has one;
* `div[c]` (`div[c; W]`): `0 <= t`, `t <= 0` or `t = 0` from the same of `c * t`, with `0 < c`;
* a row of several clauses takes one word per clause, separated by `;`; a conjunction one word per conjunct, or one
  reference whose conclusion is the conjunction (the step of an induction over a pair of ties, `lem:moments`), and a
  chain `a <= b <= c` one word per link, separated by `,` (over Mathlib one `V` is `V` on each link); an implication
  introduces its hypothesis;
* a reference `lem:y(k)[x := t]` (`exact`), the key `k` of one word or several (`lem:lists(outer dilation)`, in
  Lean `lem_lists_outer_dilation`). Over Mathlib: a family by a formula in its index,
  `fact:termwise[b_(i) := c]` (`fun i => c`); a function on points by a formula in its point, `K(v) := t`, for a
  binder of a type row `X -> Y` with `X` a tuple type and `Y` one of `QQ>=0`, `QQ`, `NN` (`fun v => t`, a value in
  `QQ>=0` with its sign by `positivity`; `lem:zpointfun`, and `thm:pivots`(core weight) at `w(s) := t`); a family of
  such functions by a formula in its index and its point, `W_(p)(s) := t`, for a binder `W_(1..J)` of the same
  type (`fun p => fun s => t`; `lem:zfamfun`, a reader of `thm:pivots`(cover)); a family on the counts by a
  formula in its two indices, `W_(c)(d) := t`, for a binder `W_(0..P)` of a type `NN -> QQ>=0` (`fun c => fun d =>
  t`, the value with its sign by name; `lem:zfamformula`), whose defining hypothesis in the row, `forall b : ...
  => U_(b)(c) = t`, is then one term on both sides and closes by `rfl` (`lem:zfamdef`); and after `;` the side
  goals, `HYP by W; ...`: HYP is a hypothesis of the reference at the data, written in the names of the row, up to the
  names it binds (the names the rule binds are
  renamed before the substitution, so a name free in the data is never captured; a side goal that is no hypothesis,
  or one proved twice, is refused with the hypotheses the generator reads), proved by the word W (`have side_k : HYP
  := by ...`) and passed in its place, as in `fact:pigeon[f_(i) := G; (sum i in 1..N, G) < (sum i in 1..N, g_(i)) by
  fact:constsum[c := G]]`; each other hypothesis is first given by name where it has one: a fact of the step
  that states it at the data (`exact_mod_cast h`, or `h i` at an index), else a relation between indices or counts
  by its index term (as for `term[J]`), else a relation from the facts and the signs by name, as for `mono`; the guard of a binder at its datum (`0 < t`, `0 <= t`, `k <= t`) by the sign of the datum
  or the bound of a count, and the guard of a family binder at a family given whole by the family's own guard
  (`hp_e`, `fun i => (hp_e i).le` for `0 <= e_(i)`; `lem:zguardname`), or at a family given by a formula in its
  index (`z_(u) := t`) by the sign of `t` at a fresh index (`fun u => ...`); else a hypothesis of the step whose Lean
  statement is the hypothesis at the data, word for word (a relation of a bundle, `prices_content_value pi Pr c
  lambda`), and numerals alone by `norm_num`; else the instance of a rule of the step, as `logic` reads it with no
  word (`lem:zrulenamed`); then the default discharge (`assumption`, the beta redexes of a family by a formula, the
  guards of a family whose member is in the data). The data and the binders of the
  reference are read in the scope of the goal: the names of the row and those the proof bound (a region named by
  `take`, a witness of `logic`). At a point of a region that the goal introduced, a universal conclusion of the
  reference is applied at it, first written out (its conclusion at the data read as a rule, its binders at the names
  of the goal, its memberships and premises by name, as `logic` reads a rule with no word), then by `apply`
  (its membership by `assumption`), and so at a point of a type row (`forall y in
  Point(n) : P => Q`, its premise by `assumption`, `lem:zall`); a reference whose row concludes an implication
  `P => Q` is applied the same way, its premise `P` at the data by `assumption` (`lem:chamber`(upper) of `cells`,
  on (walk)). A reference on a universal or an implication goal is first tried whole (`exact` of its instance),
  before the binders and the premises of the goal are introduced (`lem:zwholeref`). A `with` step whose clause is the
  instance of the reference's row at the data, an implication or a universal included, is that row whole (`exact`),
  applied to the facts by the word after it (`logic`; the cores of `lem:pass`). A fact over several indices is applied
  at its indices in order (`h_7(l, i)`). The reading of a
  program row:
  `lem:y(k)[x := t; at v_1 := t_1, ..., v_k := t_k]` on a row `prog(...) = (l, m)` gives `l <= COST` at the point
  (`NAME.IsProg.le`, the IsLeast part of the atom); the point gives every scale and is feasible by `positivity` and
  linear arithmetic on the facts; the reading is stated in QQ (`hread`, the value cast back from NNRat, each name in
  `QQ>=0` by its sign) and closes the goal exactly or by linear arithmetic, from the reading alone first
  (`lem:zprogread`, `lem:zprogguard`; refused: a point without every scale or with a name that is no scale, and
  a row that is no program, `qpp/examples/refused/programs.qpp`); printed `[x:=t;\ \text{at}\ v_1:=t_1]`.
  Printed as written,
  `[f_i:=G;\ H\ \text{by}\ F]`, the composition `o` of def:syntax with its hypothesis named; latex2qpp reads it back. A
  side goal quantified over an index set `NN>=k` with a bound, `forall j in NN>=k : j <= N => P`, is the universal
  over `NN` with the premise `k <= j`. Refused cases:
  `qpp/examples/refused/references.qpp` (`--refused --given` names the cited rules that set them up).

A row with a hole or outside the fragment is listed with the reason in the header of the file, never `sorry`. With
`--check` each Lean error is printed at the Q++ line it comes from:

    means.qpp:23: error: linarith failed to find a contradiction ... [Lean line 29]

### The Palomar entry

The entry of the Lake project `lean/` is the module `corner`: the statements of its rows over Mathlib (namespace
`QppMathlib`). `python3 -m qpp.modlean --palomar corner` writes, from `lean/QppModules/Corner.lean`:

* `lean/QppPalomar/Corner/Challenge.lean`: the modules of Mathlib and of Lean core that the library reads; each
  `def NAME.statement : Prop` of the rows, repeated verbatim from the library with its source row in its docstring;
  then each theorem `NAME : NAME.statement` with `sorry`.
* `lean/QppPalomar/Corner/Solution.lean`: imports `QppModules.Corner`, which proves the theorems.
* `lean/comparator.json`: the Challenge, the Solution, the theorems in the order of the module, and the three axioms
  `propext`, `Quot.sound` and `Classical.choice`.

`lake comparator` checks that the Solution proves each statement of the Challenge with no axiom beyond those three;
Palomar replays the check in Lean's kernel, NanoDa and con-ron. `lean/formalization.yaml` is the metadata
of the entry (the article it formalizes, its scope, and the alignment of its theorems). A Challenge has at most
1,000 lines and 100 KiB, every Lean file of the project starts with the `module` header and has at most 10,000
lines, and the project has one licence file at its root.

Over the kernel the generator writes an entry too, for a source with a line `advertise lem:mean(1), lem:square` that
names its headline results (`--kernel-target NS`, as for `qpp/examples/means.qpp`). Beside `OUT.lean` it writes:

* `OUT/Statements.lean`: the advertised statements over the kernel words and the cited facts they take (namespace
  `Qpp.NS`, Lean core, importing `QppKernel.Words`); `OUT.lean` imports it and proves each statement from its Mathlib
  reading through the bridge.
* `OUT/Challenge.lean`: `QppKernel/Base.lean`, `QppKernel/Words.lean` and the statements, verbatim, then each
  advertised theorem with `sorry` (Lean core only).
* `OUT/Solution.lean`: imports `OUT.lean`.
* with `--comparator PATH`: the `comparator.json` of the pair.

A statement that names a word of its source (a type row, a relation, a define) stops this generator: those come with
their readings over Mathlib, and are not in a statements module. Every definition a statement over the kernel uses is
in `QppKernel/Base.lean` and `QppKernel/Words.lean`, so that the Challenge's copy of them compiles to the same
constants as the library. The Challenge and the Solution of `means` are built with those of `corner` in the library
`QppPalomar` of `lean/`.

## The LaTeX form

`qpp2latex` prints each statement row in a `stmt` display, one `\sit{key}{row}` per row, and each proof line in an
`expr` display, one `\eit{key}{word}` per line, in the canonical spelling of `texmath.py`; `latex2qpp` reads that
LaTeX back into Q++. The round trip Q++ -> LaTeX -> Q++ is a test (`tests/test_printers.py`): the modules printed
in full read back with no misreading (`tests/test_constructs.py`), and read back from that LaTeX they give their
source again (`tests/test_sources.py`).
`python3 -m qpp.latex2qpp FILE.tex --check` reports three counts for every row and proof line: *formal* (no hole
`?{...}`), *same* (the canonical LaTeX printed from the Q++ term reads back as the same term) and *spelled* (the
printed LaTeX has the tokens of the source, up to spaces and braces).

The reader reads a name by its scope, never by a guess:

* A subscript of digits is part of a name (`\kappa_1`), a subscript of letters an index (`a_i`, `M_{ij}`), and a mark
  that is no power is part of the name (`Y^+_R` is `Y_pos_(R)`, `a^0` is `a_nought`).
* A name before `(` is an application if the scope declares it a function (a declaration `F\colon\Q^n\to\Q`, a
  definition `e(a):=...`, a context row, an operator such as `\lg` or `\mathrm{Name}`), a product if it declares it a
  number, and a hole otherwise.
* A chain `a\le b<c` is the conjunction of its links, a family is `a_1,\dots,a_N`, and `\cref{lem:x}(2)` is the item
  (2) of `lem:x` (Q++ `@lem:x(2)`).
* `(x-t)_+` is the positive part `max(x - t, 0)`, `\mathbf 1[P]` the indicator `iverson(P)`, `\binom pi` the binomial
  coefficient, and `\lceil\lg N\rceil`, `\lfloor\lg N\rfloor` the ceiling and the floor of the logarithm in base 2 of
  a count.

The body of a row is

    item    := part (; part)*                      independent parts
    part    := clauses [(: | \Rightarrow) part]     context, then what holds in it
    clauses := clause (, clause)*                  (also \text{and}, \text{with})
    clause  := formula postfix*
    postfix := \text{if} H  |  \text{for} x\in S [\text{with} P]  |  \text{for} i\le N  |  \text{on} S  |  \text{or} B
             |  \ (H)  (a side condition)  |  \ (\text{...})  (a gloss)

A row `given` holds the context of every conclusion of its item, and the conclusions are keyed `(1)`, `(2)`, ... or by
a word. A declaration is `x,y\in S` or a noun after names (`a,b\ \text{masses}`); every other clause of a context is a
hypothesis, `h_1, h_2, ...` in order. In the data of a proof word a relation in parentheses cites the hypothesis that
reads the same (`\gEq[(x\preceq y)+2(y\preceq z)]` is `eq[h_1 + 2 * h_2]`), and a citation that matches no hypothesis
is an error. An index that is not declared ranges over its family and is bound at the smallest clause that holds all
its occurrences. A row `D:\ L:\iff R` defines the relation `L` by the formula `R`, and a row whose left side has words
defines a relational word (`x\ \text{close to}\ y:\iff|x-y|\le1`, Q++ `x #close_to y`); every use is replaced by its
definition, in Lean and on the rows of the fixtures.

Each construct of the reader has a test in `tests/test_constructs.py`, with its LaTeX in
`tests/fixtures/constructs.tex`.

## Fixtures

The tests of a module are fixtures, not code. A line `fix KEY ID` after a row names a fixture of the row `KEY`: the
file `modules/NAME/fixtures/ID.json` (a table) or `ID.py` (the standard library only; `rows()` yields the rows, and
`KIND` and `BOUNDS` are optional). The fixture lines are read from the source, not printed. A table, here the
counterexample `modules/mean/fixtures/mean.tie.nosym.json` of the row `(tie)` of `lem:mean` (its note left out):

    {"kind": "counterexample", "drop": "forall i : forall j : P_(i)_(j) = P_(j)_(i)",
     "rows": [{"n": 3, "P": [[0, 1, 1], [0, 0, 0], [0, 0, 0]], "x": [1, 1, 1], "y": [1, 0, 2]}]}

A row gives the names that the statement declares: a scalar by name, a family `a_(1..N)` under `a[]` as a list from
its first index or as a dict from index to value, a tuple as a list, a set as `{"box": [lo, hi]}` or as the list of
its points; numbers are integers or strings of rationals (`"3/2"`), never floats. The checker of
`tests/test_qpp.py` evaluates the statement on each row, in exact rational arithmetic: the row *holds*, *fails*, is
*vacuous* (a hypothesis is false) or is *undecided* (a value the row lacks, an exponent that is not an integer, a
quantifier over an infinite set without a bound). A quantifier over `ZZ>=c` runs to the bound that the fixture gives
(`bounds`), and one over `QQ`, `QQ>0`, ... over the sample points that the fixture lists for its variable
(`"bounds": {"x": ["1/3", 1, 5]}`); the check then says that it was bounded or sampled. A bounded or sampled check
in a hypothesis can admit a row that is not an instance, and in a conclusion it checks less than the statement says.

The kinds:

* `instances`: no row fails or is undecided, and some row holds;
* `witness`: every row holds, so the hypotheses of the statement can be met;
* `values` (a line `eqfix KEY ID`): the part of the row (`"part"`, 1 by default) is an equation, a chain of `=`; on
  every row its hypotheses hold and every side is the value `"="`, computed by hand;
* `counterexample` (a line `neqfix KEY ID`): `"drop"` names hypotheses of the row or of its given by their Q++ text
  (a string or a list); on every row the hypotheses kept hold, a dropped one fails and the conclusion fails, so the
  statement without them is false;
* `model`: the fixture of a cited rule over a context, which has no concrete instance in Q++, evaluated on the exact
  model of the contexts of the pair (`ctxmodel.py`).

A fixture file that no fixture line names fails the run, and so does a cited fact with no fixture and no `mathlib:`
row: its statement enters the theorems that use it as a hypothesis, and the fixture checks that it is not stated
wrong. No fixture is evaluated by enumeration: a check that would decide a clause by visiting the points of a set of
candidates (the lattice points of a box, the numbers up to a bound, the vertices of a polyhedron) stops there, and
its fixture is reported as not evaluated; `modules/enumerations.toml` lists these fixtures by module, and the run
fails unless the list is exactly the fixtures whose check enumerates.

Once Lean proves a statement, its rows add no logical content; what they still check is that the hypotheses can be
met (Lean proves a statement with inconsistent hypotheses without notice), that a hypothesis is needed (a
`counterexample`), and that a value is the one computed by hand. The checker and the Lean side read a statement in the
same way, through the helpers of `qpp2lean.py` (free indices, family ranges, defined relations): a difference between
them is a bug of one of them. A core row is read without the given of its item, as Lean states it.

    python3 qpp/tests/test_qpp.py qpp/tests/fixtures/a_slice.qpp qpp/tests/fixtures   # one file, row counts

## The kernel

`qpp/lean` is the Lake project of the kernel (`lakefile.toml`, no dependencies, the toolchain of `lean/`). Its
libraries are `QppKernel` and `QppTests`; nothing in them imports Mathlib or Batteries, every file is in the module
system, and every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. From `qpp/lean`:

    lake build QppKernel QppTests          # the kernel and its checks
    lake env lean QppTests/Axioms.lean     # the axiom audit
    QppTests/kernels.sh QppTests.Resultant Qpp.Tests.res_loss   # Lean's kernel, NanoDa and con-ron

Each definition is there because a statement of the modules cannot be written without it:

| definition | why it cannot be left out |
|---|---|
| `Count` (`one`, `succ`) (D1) | the counts are the unbounded parameters (degrees, numbers of variables, levels); `ind` and `neq` are its recursor and no-confusion |
| `Count.add`, `Count.mul`, powers by numerals | the sum and the product of counts; a power by a numeral is a product of a length given as data |
| `Pair`, `Mass` (the quotient by the tie) | the masses; the quotient makes `=` the tie, so functions of masses need no congruence at each use |
| `Mass.add`, `Mass.div`, `1` | the three symbols; product and inverse are derived from them |
| `<` on counts and on masses | the order, `∃ c, b = a + c`; it is not a word in `1`, `+`, `/` |
| `oadd`, `osum`, `card`, `sumTo` (D1) | sums of a number of terms that is a parameter; with no zero, the sum of no terms is absent |
| `Dyadic` (D5) | the dyadic masses `2^a / 2^b`; `Scale`, `Arch` and `Floor` are theorems about them (`Scale.lean`), not definitions |
| `CExpr`, `MExpr`, `IsPol` | the expressions that `qeq` reads, and the class of functions on which its check is sound |
| `SPoly`, `CheckBy`, `Tree` | the sparse normal forms, the choice between the two checks, and the values of the variables in a tree (a lookup in `log n` steps) |
| `Mon`, `Poly` (D2) | polynomials are data of a fixed arity whose number of variables is a parameter: finite lists of terms, absent where there is none |
| `Bal`, `Bal.Tie` (D3) | coefficients and values of both kinds: a pair `l, r` stands for `l - r`, with no quotient and no zero |
| `IsMin`, `IsLeast` (D4) | `min` is not a rational function, so it is a relation in the order |
| `Within`, `Asymp`, `AsympUnif`, `BigO` (D6) | the order of the quantifiers is the content: constants before the parameter or after it |
| `Law`, `Law.integral` (D7) | expectations: atoms plus antiderivatives of polynomial densities on rational cells |
| `Source`, `Cited` | a classical fact that is not proved: its statement over the core, taken as a hypothesis, and its DOI |

`qeq` closes an identity of polynomial expressions in counts, or of rational expressions in masses (through the
identity of counts `num a * den b = num b * den a`, the masses written over one common denominator). It has two
checks, both run by the kernel on Lean's numerals, which every kernel computes in binary; there is no
`native_decide`.

* At points (`CExpr.check`): both sides are evaluated at a few points, with bounds that make the agreement an
  identity (Kronecker's substitution, `IsPol.eq_of_points`). The numbers have as many digits as the dense size of
  the identity, the product over the variables of their degrees plus one: few variables of high degree are cheap.
  The Bezout identity of the resultant of the loss `((y^2-x^3)^2-x^5y)^2+x^14+y^14` and its derivative in `y`
  (2127 cofactor terms, coefficients up to 76 bits) checks in Lean's kernel in 3 s, in NanoDa in 2 s and in con-ron
  in 19 s.
* By sparse normal forms (`CExpr.scheck`): both sides are expanded into sorted lists of terms, a monomial packed
  into one number, its key `Σ e_i W^i`, with `W` above the total degree, so that the product of monomials is the sum
  of keys with no carry (`SPoly.valid_add`). Long sums and products are merged in a balanced way. The cost is the
  number of terms, each with a key of `n log W` bits: linear in the number of variables, with no dense factor.

`qeq` takes the check at points when the dense size is at most `2^16` and the normal forms otherwise; `qeq dense`
and `qeq sparse` force one. Times in Lean's kernel:

| identity | variables | terms | points | normal forms |
|---|---|---|---|---|
| NMF loss, `Σ ((AB)_ij + C_ij)^2` expanded, `A` 4x3, `B` 3x4 | 24 | 145 | 0.42 s | 0.29 s |
| `(x_0 + ... + x_9)^4` expanded | 10 | 715 | 2.7 s | 2.3 s |
| deep linear network, 4 layers of width 3, `Σ (W_4 W_3 W_2 W_1 + C)_ij^2` expanded, `C` fixed | 36 | 3403 | out of reach | 9.6 s |
| `Σ_i c_i (x_i + y_i) = Σ_i c_i x_i + Σ_i c_i y_i` | 400 | 400 | out of reach | 1.2 s |

No check by evaluation at points can be linear in the number of variables: a set of points on which no nonzero
polynomial of degree `d` in `n` variables vanishes has at least `C(n + d, d)` points, so a linear cost needs the
expressions themselves, which is what the normal forms use. The kernel spends about 0.1 ms on a step of a merge,
much more than on a digit of a number, so the check at points stays the cheaper one when the dense size is small.

Aliases. A name for a subexpression is an atom with a defining equation (in Lean, a variable `s` with `hs : s = e`,
or an irreducible definition and its equation lemma); `qeq` never unfolds it. `qeq [h₁, c₂ • h₂, ...]` closes
`L = R` from equations `hⱼ : aⱼ = bⱼ`: `L + Σ cⱼ bⱼ = R + Σ cⱼ aⱼ` is checked as an identity and the sums cancel
(`Count.eq_of_comb`, `Mass.eq_of_comb`), so each step costs its own size and each alias is checked once, by its
defining equation. A step whose cancellation needs a name expanded rewrites with its equation first. Names pay
when a subexpression is reused; they do not shrink a step whose statement is itself a long expansion (the 715-term
identity above takes 2.6 s with one alias for the square, and 8.7 s through the binomial chain of its tails).

Cited facts. A classical fact that the core does not prove is a `Cited`: its statement over the core, taken as a
hypothesis by the results that use it, and its `Source`, a DOI with the number of the statement when there is one.
The Python suite checks it on fixtures. The example is Polya's theorem on the simplex (`polya`, cited from Powers
and Reznick).

`farkas [h₁, c₂ • h₂, ...]` closes `L < R` or `L ≤ R` from hypotheses `aⱼ < bⱼ`, `aⱼ ≤ bⱼ` or `aⱼ = bⱼ` taken
`cⱼ` times: the certificate is the identity `R + Σ cⱼ aⱼ = L + Σ cⱼ bⱼ + s`, checked as `qeq` checks one, and the
tactic finds the slack `s`, which must have no negative monomial (the slack carries the positivity of the
variables, so this is Farkas' lemma over the masses). A point of a box `lo < x < hi` is `(lo c' + hi c)/(c + c')`
for two masses (`Mass.box`), so positivity on a box is a certificate in `c`, `c'` (the Bernstein coefficients),
and a box splits at a point (`Mass.split`); a count below `n + 1` is below `n` or is `n` (`Count.lt_succ_cases`). A covering LP in 20 masses with 30 rows and a
positivity on a box with three splits replay in Lean's kernel in 1.6 s, in NanoDa in 0.8 s and in con-ron in 10 s.

## Checking the generated Lean

A generated file is never edited: `python3 -m qpp.modlean NAME` writes `lean/QppModules/Name.lean` again from the
module, the modules it uses and its closer table, byte for byte. `lake build` in `lean/` compiles every module, each
part of a module in a Lean process of its own, and fails on an error or a `sorry`; only the Challenges of
`lean/QppPalomar` state their theorems with `sorry`, by design.

The audits print the axioms of every declaration they name, and each line must show `propext`, `Classical.choice`
and `Quot.sound` at most:

    cd lean && lake env lean Axioms.lean                  # every row over the kernel, in the namespace Qpp.Modules
    cd lean && lake env lean QppBridge/Axioms.lean        # the bridge
    cd qpp/lean && lake env lean QppTests/Axioms.lean     # the kernel and its checks

A theorem over the kernel is proved from its reading over Mathlib, so its line covers that proof too. The audits of
the bridge and of the kernel import each submodule with `import all`, so that their private declarations are
audited as well. The statements themselves name only the constants that `primitives_lean.toml` lists for the
primitives, read off each `NAME.statement` and the definitions it reaches; proofs are not audited this way.
