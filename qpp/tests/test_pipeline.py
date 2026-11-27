"""Tests of the Q++ pipeline without Lean: the term layer, latex2qpp and qpp2lean on the demo fixture.

The generated demo files are committed, and these tests check that they are up to date. Lean checks the generated
Lean file separately (qpp/README.md, "Checking the generated Lean")."""
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1]))
from qpp import latex2qpp, qpp2lean  # noqa: E402
from qpp import texmath as T  # noqa: E402

FIX = HERE / "fixtures"

FORMULAS = [
    (r"\kappa_1^{-1}u\le x\le\kappa_1u", "kappa_1^(-1) * u <= x <= kappa_1 * u", "\u03ba\u2081\u207b\u00b9 * u \u2264 x \u2227 x \u2264 \u03ba\u2081 * u"),
    (r"\gamma|y-y'|\le a+b", "gamma * |y - y'| <= a + b", "\u03b3 * |y - y'| \u2264 a + b"),
    (r"a_j\le\textstyle\sum_ia_i\le Na_k", "a_(j) <= (sum i, a_(i)) <= N * a_(k)", None),
    (r"c_12^{-\Lambda_1}\le c_22^{e-\Lambda_1}", "c_1 * 2^(-Lambda_1) <= c_2 * 2^(e - Lambda_1)",
     "c\u2081 * (2 : \u211a) ^ (-\u039b\u2081 : \u2124) \u2264 c\u2082 * (2 : \u211a) ^ (e - \u039b\u2081 : \u2124)"),
    (r"\exists i:\ g_i\ge T/N", "exists i : g_(i) >= T / N", "\u2203 i, g i \u2265 (T / N : \u211a)"),
    (r"\sum_{i=1}^Na_i\le NM", "(sum i in 1..N, a_(i)) <= N * M", "(\u2211 i \u2208 Finset.Icc 1 N, a i) \u2264 N * M"),
]


@pytest.mark.parametrize("tex,qpp,lean", FORMULAS)
def test_terms_three_ways(tex, qpp, lean):
    tree = T.parse_tex(tex)
    assert T.to_qpp(tree) == qpp
    assert T.parse_qpp(qpp) == tree
    if lean is None:
        with pytest.raises(T.Hole):  # a sum without a range needs its family in scope (qpp2lean)
            T.to_lean(tree)
    else:
        assert T.to_lean(tree) == lean
    assert T.round_trip(tex)[:2] == (True, True)


def test_holes_keep_the_latex():
    assert T.tex_to_qpp(r"\text{a box}") == r"?{\text{a box}}"
    assert not T.is_formal(T.tex_to_qpp(r"\partial_x(f+g)\ge0"))


def test_statement_forms():
    assert T.tex_to_qpp(r"a_1,\dots,a_N\in\Q_{\ge0}") == "a_(1..N) in QQ>=0"
    assert T.tex_to_qpp(r"x\in[\kappa_1^{-1},\kappa_1]u") == "x in [kappa_1^(-1), kappa_1]*u"
    assert T.tex_to_qpp(r"N\in\Z_{\ge1}") == "N in ZZ>=1"
    assert T.tex_to_qpp(r"P\in\Q[x]") == "P in QQ[x]"
    assert T.tex_to_qpp(r"\{K\le2^{-L}\}\cap C") == "{K <= 2^(-L)} cap C"
    for t in (r"a_1,\dots,a_N\in\Q_{\ge0}", r"|\bw|_\infty\le1", r"\mathcal B\subseteq\Z^n", r"A^\top\by=0"):
        assert T.round_trip(t)[:2] == (True, True), t


STATEMENTS = [  # conventions v1: a statement item, its Q++, and the number of glosses dropped
    (r"\mu\ge2,\ c\le C\ \text{masses},\ N\in\Z_{\ge1}", "mu >= 2, c, C in #mass, c <= C, N in ZZ>=1", 0),
    (r"g_1,\dots,g_N\in\Q_{\ge0},\ T\in\Q,\ \textstyle\sum_ig_i=T\Rightarrow\exists i,i':\ g_i\ge T/N\ge g_{i'}",
     "g_(1..N) in QQ>=0, T in QQ, (sum i, g_(i)) = T => exists i, i' : g_(i) >= T / N >= g_(i')", 0),
    (r"q\in\Z_{\ge1}:\ a\le a^q", "q in ZZ>=1 : a <= a^q", 0),
    (r"\gamma h\le g_{k+1}-g_k\le Mh\ (k<N);\ \delta>0:\ |g_k|\le\delta",
     "k < N => gamma * h <= g_(k + 1) - g_(k) <= M * h; delta > 0 : |g_(k)| <= delta", 0),
    (r"h(\bx)\ge0\ (h\in H)", "forall h in H : h(b_x) >= 0", 0),
    (r"|F(\bu)|>\delta\ \text{for}\ \bu\in Y", "forall b_u in Y : |F(b_u)| > delta", 0),
    (r"a\in\Q_{>0}\ (\text{a mass}):\ a\le 1", "a in QQ>0 : a <= 1", 1),
    (r"a_i\le a_k\ \text{for}\ 1\le i\le N", "forall i : 1 <= i <= N => a_(i) <= a_(k)", 0),
]


@pytest.mark.parametrize("tex,qpp,glosses", STATEMENTS)
def test_statements_v1(tex, qpp, glosses):
    parts, gl = T.parse_stmt(tex)
    assert T.stmt_print(parts, T.to_qpp) == qpp
    assert len(gl) == glosses
    assert T.parse_qpp_item(qpp) == parts
    assert T.stmt_round_trip(tex)[:2] == (True, True)


def test_statements_after_a_conversion():
    """a conversion leaves no names of its paper behind: a paper in which h is a number (so that h before a
    parenthesis is a product) does not change how the statements of another read h"""
    src = (r"\begin{lemma}\label{lem:h}\begin{stmt}\sit{given}{h\in\Q,\ h\ge1}\sit{(1)}{h(h+1)\ge2}"
           r"\end{stmt}\end{lemma}")
    latex2qpp.convert(src, "H")
    for tex, qpp, glosses in STATEMENTS:
        test_statements_v1(tex, qpp, glosses)


def test_prose_outside_the_vocabulary_is_a_hole():
    for tex in (r"a_j\le a_k\ (a_k\ \text{a largest})", r"\Phi\ \text{is constant on}\ Y",
                r"\text{the semifield laws of}\ \Q_{>0}"):
        with pytest.raises(T.Hole):
            T.parse_stmt(tex)


def test_vocabulary_rows():
    src = r"\begin{stmt}\sit{box}{\text{box}:=[0,1]}\sit{x}{\text{note}:=\text{prose}}\end{stmt}"
    v = latex2qpp.vocabulary_of(src)
    assert v["box"]["set"] == ("interval", ("num", "0"), ("num", "1"), None) and v["box"]["plural"] == "boxes"
    assert "note" not in v and "mass" in v


def test_named_slots_and_references():
    assert T.to_qpp(T.parse_tex(r"\text{half}{:=}\mathrm U")) == "half := U"
    assert T.to_qpp(T.parse_tex(r"\eqref{eq:D1}")) == "@eq:D1"


def test_words():
    w, _ = latex2qpp.word(r"\iota_{\rm chain}(\gV\circ\gI[|F(\bu)-F(\bv)|\le\delta<|F(\bu)|])")
    assert w == "iota_chain (V o I[|F(b_u) - F(b_v)| <= delta < |F(b_u)|])"
    w, _ = latex2qpp.word(r"\alpha\circ\alpha[h_2+h_3+h_4]")
    assert w == "alpha o alpha[h_2 + h_3 + h_4]"
    w, _ = latex2qpp.word(r"\gEq\circ\gNeq[h_2+h_3+h_4]")
    assert w == "eq o neq[h_2 + h_3 + h_4]"
    w, _ = latex2qpp.word(r"\gInd_k(\gV\circ\gI)")
    assert w == "ind_k (V o I)"


def test_demo_qpp_is_generated():
    text, rep = latex2qpp.convert((FIX / "demo.tex").read_text(encoding="utf-8"), "Demo",
                                  "qpp/tests/fixtures/demo.tex")
    assert text == (FIX / "demo.qpp").read_text(encoding="utf-8")
    s = latex2qpp.summary(rep)
    assert s["results"]["both"] == 3 and s["lines"]["formal"] == s["lines"]["same"] == 4


REL = ("relation e in QQ, x, c in #mass : x <= c * 2^(-e) :<=> forall q in ZZ>=1 : q * e in ZZ => "
       "x^q <= c^q * 2^(-(q * e))\n")


@pytest.mark.parametrize("typ, link, lean", [
    ("QQ", "x <= c * 2^(-e)", "x ^ q \u2264 c ^ q * (2 : \u211a) ^ (-n\u2081)"),
    ("QQ", "c * 2^(-e) <= x", "x ^ q \u2265 c ^ q * (2 : \u211a) ^ (-n\u2081)"),
    ("QQ", "x < c * 2^(-e)", "x ^ q < c ^ q * (2 : \u211a) ^ (-n\u2081)"),
    ("ZZ", "x <= c * 2^(-e)", "x \u2264 c * (2 : \u211a) ^ (-e)"),
])
def test_defined_relations_expand_by_type(typ, link, lean):
    q = ("paper X\nword mass := QQ>0\n" + REL + f"\nlemma lem:x\n  given: e in {typ}, x, c in #mass\n  (1): {link}\n"
         "proof lem:x\n  (1) alpha\n")
    text, made, _ = qpp2lean.generate(q)
    stmt = next(ln for ln in text.splitlines() if ln.startswith("  \u2200"))
    assert made == ["lem:x"] and lean in stmt and "2 ^ (-e)" not in stmt.replace(lean, "")
    if typ == "QQ":
        assert "\u2200 (q : \u2124), 1 \u2264 q \u2192 (\u2200 (n\u2081 : \u2124), ((n\u2081 : \u211a) = q * e) \u2192" in stmt


def test_label_map_reads_docstring_tags(tmp_path):
    from qpp import leanrefs
    (tmp_path / "X.lean").write_text("namespace P\nnamespace Q\n/-- [lem:a] (2) text -/\ntheorem foo : True := trivial\n"
                                     "end Q\n/-- [lem:a] [lem:b] more -/\ntheorem bar : True := trivial\nend P\n",
                                     encoding="utf-8")
    m = leanrefs.label_map(tmp_path)
    assert m["lem:a"] == [("P.Q.foo", "(2)", "theorem", "X.lean"), ("P.bar", None, "theorem", "X.lean")]
    assert m["lem:b"] == [("P.bar", None, "theorem", "X.lean")]
    # a named item (sums), (2a) is read like (2)
    (tmp_path / "Y.lean").write_text("/-- [lem:c] (sums) text -/\ntheorem baz : True := trivial\n", encoding="utf-8")
    assert leanrefs.label_map(tmp_path)["lem:c"] == [("baz", "(sums)", "theorem", "Y.lean")]


def test_label_map_reads_paper_prefixed_tags(tmp_path):
    """the tags of a library may name their paper, [first:lem:x], [second:thm:y]; the map is keyed by the
    label of the LaTeX, paper= keeps one paper's tags (and the unprefixed ones); items follow their own tag, and
    adjacent tags share the items after them; a second marker (base) or a phrase is not an item"""
    from qpp import leanrefs
    (tmp_path / "R.lean").write_text(
        "namespace First\n"
        "/-- [first:lem:cost] (a) [first:thm:effective] (2) The degrees. -/\ntheorem deg : True := trivial\n"
        "/-- [first:lem:cost] (d) (base) [first:con:dyadic] The forms. -/\ntheorem forms : True := trivial\n"
        "/-- [first:con:crossings] [first:lem:crosslist] (5) Two points. -/\nlemma two : True := trivial\n"
        "/-- [first:con:coprime] (the claim, stop) A move. -/\ntheorem move : True := trivial\n"
        "/-- [first:fact:bands] Ostrowski, a cited fact. -/\nstructure BandsGap : Prop where\n  h : True\n"
        "/-- [eq:D1] [lem:x] (1) unprefixed, after an equation tag. -/\ntheorem plain : True := trivial\n"
        "end First\n"
        "/-- [second:thm:rows] (4) Another paper. -/\ntheorem rows : True := trivial\n", encoding="utf-8")
    m = leanrefs.label_map(tmp_path, paper="first")
    assert m["lem:cost"] == [("First.deg", "(a)", "theorem", "R.lean"), ("First.forms", "(d)", "theorem", "R.lean")]
    assert m["thm:effective"] == [("First.deg", "(2)", "theorem", "R.lean")]
    assert m["con:dyadic"] == [("First.forms", None, "theorem", "R.lean")]
    assert m["con:crossings"] == m["lem:crosslist"] == [("First.two", "(5)", "lemma", "R.lean")]
    assert m["con:coprime"] == [("First.move", None, "theorem", "R.lean")]
    assert m["fact:bands"] == [("First.BandsGap", None, "structure", "R.lean")]
    assert m["eq:D1"] == m["lem:x"] == [("First.plain", "(1)", "theorem", "R.lean")]
    assert "thm:rows" not in m
    assert leanrefs.label_map(tmp_path)["thm:rows"] == [("rows", "(4)", "theorem", "R.lean")]
    assert "lem:cost" not in leanrefs.label_map(tmp_path, paper="second")


def test_match_intros_the_binders_not_the_names_in_their_types():
    """the match introduces one name per binder: a hypothesis forall i : Fin n, ... is one name (it was counted as
    its inner names), and a named item is matched by the declarations tagged with it"""
    assert qpp2lean.count_binders("(x u : \u211a) (n : \u2124)") == 3
    assert qpp2lean.count_binders("(h\u2081 : 0 < x) (h\u2082 : \u2200 i : Fin n.toNat, (1 / 2 : \u211a) < u i)") == 2
    q = ("paper X\nlemma lem:m\n  given: x, y in QQ, (forall z in QQ>0 : x <= y + z)\n  sums: x <= y + 1\n"
         "  (2): ?{x\\ \\text{inside}\\ \\mathcal K}\n")
    refs = {"lem:m": [("A.m_sums", "(sums)", "theorem", "A.lean"), ("A.m_two", "(2)", "theorem", "A.lean")]}
    lean, spans, skipped = qpp2lean.generate_match(q, refs, [])
    ex = lean.split("example : lem_m.item_sums.statement := by\n", 1)[1].split("\n\n", 1)[0]
    # first a plain type check by the declaration, then the intros and apply on what is left
    assert ex.startswith("  first\n  | exact A.m_sums\n  | skip\n  all_goals\n    intro _ _ _\n")
    assert "A.m_sums" in ex and "A.m_two" not in ex


def test_a_result_with_a_hole_is_listed_not_generated():
    """a hole clause of the given that mentions a name of the conclusion, not declared by a formal clause, blocks
    it; one that only constrains a declared name is left out (a stronger statement, generated)"""
    q = "paper X\nlemma lem:x\n  given: x in QQ, ?{y\\in\\mathcal K}\n  (1): y <= y\nproof lem:x\n  (1) I\n"
    text, made, skipped = qpp2lean.generate(q)
    assert not made and skipped == [("lem:x", "item given has a hole that mentions y, which a conclusion uses")]
    text, made, skipped = qpp2lean.generate(q.replace("y\\in", "x\\in").replace("y <= y", "x <= x"))
    assert made == ["lem:x"] and "without the given clauses with a hole (a stronger statement): x\\in\\mathcal K" in text


# ---------------------------------------------------------------- relational words

CLOSE = r"""\begin{stmt}\sit{}{x,y\in\Q:\ x\ \text{close to}\ y:\iff|x-y|\le1}\sit{}{x\in\Q:\ x\ \text{small}:\iff-1\le x\le1}
\sit{}{i\in\N,\ G,Q\in\Q:\ i\ \text{pivot of}\ G\ \text{on}\ Q:\iff i\le G+Q}\end{stmt}
\begin{lemmaS}\label{lem:close}\begin{stmt}\sit{given}{x,y\in\Q}\sit{(1)}{x\ \text{close to}\ y\Rightarrow y\ \text{close to}\ x}
\sit{(2)}{x\ \text{small},\ y\ \text{small}\Rightarrow x+y\ \text{close to}\ 0}\sit{(3)}{x\ \text{a pivot of}\ y\ \text{on}\ 1}
\end{stmt}\end{lemmaS}"""


def test_relational_words_read_print_and_expand():
    v = latex2qpp.vocabulary_of(CLOSE)
    assert v["#textrel"] == [("_", "close to", "_"), ("_", "small"), ("_", "pivot of", "_", "on", "_")]
    text, _ = latex2qpp.convert(CLOSE, "T")
    assert "  (1): x #close_to y => y #close_to x\n" in text and "  (3): x #pivot_of y #on 1\n" in text
    assert "relation x, y in QQ : (x #close_to y) :<=> |x - y| <= 1\n" in text
    lean, made, _ = qpp2lean.generate(text)
    stmt = next(ln for ln in lean.splitlines() if ln.startswith("  \u2200"))
    assert stmt == ("  \u2200 (x y : \u211a), ((|x - y| \u2264 1) \u2192 |y - x| \u2264 1) \u2227 ((-1 \u2264 x \u2227 x \u2264 1) "
                    "\u2192 (-1 \u2264 y \u2227 y \u2264 1) \u2192 |x + y - 0| \u2264 1) \u2227 (x \u2264 y + 1)")
    assert T.textrel_pattern(r"x\le y") is None and T.rel_word("is  a Pivot of ") == "pivot of"


# ---------------------------------------------------------------- functions, the context, sets of vectors, "on"

BOXES = r"""\begin{stmt}\sit{context}{n\in\N_{\ge1}}\sit{box}{\text{box}:=\{[\ba,\bb]:\ \ba,\bb\in\Q^n,\ \ba\le\bb\}}\end{stmt}
\begin{lemmaS}\label{lem:b}\begin{stmt}\sit{given}{S\subseteq\Q^n,\ B\ \text{a box},\ \bw\in B,\ K:\Q^n\to\Q}
\sit{(1)}{B\subseteq S\Rightarrow\bw\in S}\sit{(2)}{\ba,\bb\in\Q^n,\ \ba\le\bb\Rightarrow[\ba,\bb]\ \text{a box}}
\sit{(3)}{K\ge0\ \text{on}\ S,\ B\subseteq S\Rightarrow K\ge0\ \text{on}\ B}\sit{(4)}{K(\bw)>0\Rightarrow K\ge0\ \text{on}\ \{\bw\}}
\end{stmt}\end{lemmaS}
\begin{lemmaS}\label{lem:nodim}\begin{stmt}\sit{given}{e:\Q_{>0}\to\Z_{\ge0}}\sit{(1)}{e(1)\ge0}\end{stmt}\end{lemmaS}"""


def test_functions_context_sets_and_on():
    text, _ = latex2qpp.convert(BOXES, "T")
    assert "word box := {[b_a, b_b] : b_a, b_b in QQ^n, b_a <= b_b}\n" in text and "context n in NN>=1\n" in text
    assert "  given: S subseteq QQ^n, B in #box, b_w in B, K in (QQ^n -> QQ)\n" in text
    assert "  (2): b_a, b_b in QQ^n, b_a <= b_b => [b_a, b_b] in #box\n" in text
    lean, made, _ = qpp2lean.generate(text)
    b, e = [ln for ln in lean.splitlines() if ln.startswith("  \u2200")]
    assert b.startswith("  \u2200 (n : \u2115) (S B : Set (Fin n \u2192 \u211a)) (w : Fin n \u2192 \u211a) "
                        "(K : (Fin n \u2192 \u211a) \u2192 \u211a) (h\u2081 : 1 \u2264 n) "
                        "(h\u2082 : \u2203 (a b : Fin n \u2192 \u211a), a \u2264 b \u2227 B = Set.Icc a b) (h\u2083 : w \u2208 B),")
    # the names of the image are bound: [a, b] a box asks for other a', b'
    assert "\u2203 (a' b' : Fin n \u2192 \u211a), a' \u2264 b' \u2227 (Set.Icc a b) = Set.Icc a' b'" in b
    assert ("((\u2200 w' : Fin n \u2192 \u211a, w' \u2208 S \u2192 K w' \u2265 0) \u2192 (B \u2286 S) \u2192 "
            "\u2200 w' : Fin n \u2192 \u211a, w' \u2208 B \u2192 K w' \u2265 0)") in b
    # a statement that does not use the dimension does not get it
    assert e == "  \u2200 (e : \u211a \u2192 \u2124) (h\u2081 : \u2200 t : \u211a, 0 < t \u2192 0 \u2264 e t), e 1 \u2265 0"


# ---------------------------------------------------------------- vectors: components over Fin n, the strict order

VECS = r"""\begin{stmt}\sit{context}{n\in\N_{\ge1}}\sit{box}{\text{box}:=\{[\ba,\bb]:\ \ba,\bb\in\Q^n,\ a_i<b_i\ \text{for}\ i\le n\}}\end{stmt}
\begin{lemmaS}\label{lem:v}\begin{stmt}\sit{given}{\ba,\bb,\bw\in\Q^n,\ c\in\Q}
\sit{(1)}{\ba<\bb\Rightarrow[\ba,\bb]\ \text{a box}}\sit{(2)}{\bw>0\Rightarrow\bw\ge0,\ \bw\ne0}
\sit{(3)}{\bw\le c\Rightarrow\forall i\le n:\ w_i\le c}\sit{(4)}{\exists i\le n:\ w_i\ge0}
\sit{(5)}{w_i\ge0\ \text{for}\ i\le n\Rightarrow\textstyle\sum_iw_i\ge0}\sit{(6)}{2^iw_i\ge w_i\ \text{for}\ i\le n}
\end{stmt}\end{lemmaS}"""


def test_vector_components_and_strict_order():
    text, _ = latex2qpp.convert(VECS, "T")
    assert "word box := {[b_a, b_b] : b_a, b_b in QQ^n, forall i : i <= n => a_(i) < b_(i)}\n" in text
    assert "  (3): b_w <= c => forall i : i <= n => w_(i) <= c\n" in text and "  (4): exists i : i <= n, w_(i) >= 0\n" in text
    lean, made, _ = qpp2lean.generate(text)
    s = [ln for ln in lean.splitlines() if ln.startswith("  \u2200")][0]
    F = "Fin n \u2192 \u211a"
    # a < b on vectors is strict in every component (Lean's a < b on Fin n -> Q is a <= b and a != b)
    assert f"((\u2200 i, a i < b i) \u2192 \u2203 (a' b' : {F}), (\u2200 (i : Fin n), (a' i < b' i)) \u2227 (Set.Icc a b) = Set.Icc a' b')" in s
    # w > 0 componentwise; w >= 0 and w != 0 are Lean's order and equality on Fin n -> Q; w <= c componentwise
    assert "((\u2200 i, w i > 0) \u2192 (w \u2265 0) \u2227 (w \u2260 0))" in s
    # the components w_i, i <= n, run over Fin n: the bounds 1 <= i <= n are the type; i itself is i + 1
    assert "((\u2200 i, w i \u2264 c) \u2192 \u2200 (i : Fin n), (w i \u2264 c))" in s and "(\u2203 (i : Fin n), (w i \u2265 0))" in s
    assert "((\u2200 (i : Fin n), (w i \u2265 0)) \u2192 (\u2211 i : Fin n, w i) \u2265 0)" in s
    assert "(\u2200 (i : Fin n), (2 ^ ((i : \u2115) + 1) * w i \u2265 w i))" in s


# ---------------------------------------------------------------- folds with \dots, defined operators, min and max

FOLDS = r"""\begin{lemmaS}\label{lem:f}\begin{stmt}\sit{given}{N\in\Z_{\ge1},\ a_1,\dots,a_N\in\Q_{\ge0},\ e:\Q_{>0}\to\Z\ (\text{the exponent})}
\sit{sums}{a_j\le a_1+\dots+a_N\le Na_k\ \ (a_i\le a_k\ \forall i)}
\sit{masses}{a_i\ \text{masses},\ e_-:=\min_ie(a_i):}
\sit{}{e_-\le e(a_1\parallel\dots\parallel a_N)+\lceil\lg N\rceil}
\sit{parallel sum}{a_1\parallel\dots\parallel a_N:=(a_1^{-1}+\dots+a_N^{-1})^{-1}}\end{stmt}\end{lemmaS}
\begin{lemmaS}\label{lem:k}\begin{stmt}\sit{(1)}{\mathcal K\subseteq\Z,\ \theta_k\in\Q_{\ge0}\ \text{for}\ k\in\mathcal K,\ k^*\in\mathcal K,\ \theta:\Z\to\Q,\ \theta(k)\ge\theta_k\ \text{for}\ k\in\mathcal K\Rightarrow\theta(k^*)\ge0}
\end{stmt}\end{lemmaS}"""


def test_folds_defined_operators_min_max_and_contexts():
    text, _ = latex2qpp.convert(FOLDS, "T")
    # t_1 op \dots op t_N is a fold over 1..N; an item ending with ":" is the context of the items that continue it
    assert "  sums: (forall i : a_(i) <= a_(k)) => a_(j) <= (sum i in 1..N, a_(i)) <= N * a_(k)\n" in text
    assert "  masses: a_(i) in #mass, e_minus := min i, e(a_(i)) : e_minus <= e(par i in 1..N, a_(i)) + ceil(lg(N))\n" in text
    assert "  parallel sum: par i in 1..N, a_(i) := (sum i in 1..N, a_(i)^(-1))^(-1)\n" in text
    # the trailing quantifier of a hypothesis is parenthesized (it would take the arrow)
    assert "(forall k in cal_K : theta_(k) in QQ>=0), k_star in cal_K, theta in (ZZ -> QQ), (forall k in cal_K : theta(k) >= theta_(k)) => theta(k_star) >= 0" in text
    lean, made, skipped = qpp2lean.generate(text)
    f, k = [ln for ln in lean.splitlines() if ln.startswith("  \u2200")]
    S = "\u2211 i \u2208 Finset.Icc 1 N.toNat"
    # a free index is quantified at the smallest clause that holds all its occurrences: k, on both sides, at the
    # implication (a parameter: the largest term); j, in the conclusion only, there
    assert (f"(\u2200 k : \u2115, 1 \u2264 k \u2192 k \u2264 N \u2192 (\u2200 (i : \u2115), 1 \u2264 i \u2192 i \u2264 N \u2192 (a i \u2264 a k)) \u2192 "
            f"\u2200 j : \u2115, 1 \u2264 j \u2192 j \u2264 N \u2192 a j \u2264 ({S}, a i) \u2227 ({S}, a i) \u2264 N * a k)") in f
    # m := min i, t is a name with its definition; a_i masses for every i; the parallel sum by its definition;
    # the ceiling of lg N is Nat.clog 2
    assert ("\u2200 (e_minus : \u2124), (\u2200 i : \u2115, 1 \u2264 i \u2192 i \u2264 N \u2192 0 < a i) \u2192 "
            "(\u2200 (i : \u2115), 1 \u2264 i \u2192 i \u2264 N \u2192 (e_minus \u2264 e (a i))) \u2192 "
            "(\u2203 (i : \u2115), 1 \u2264 i \u2227 i \u2264 N \u2227 (e_minus = e (a i))) \u2192 "
            f"e_minus \u2264 e (({S}, (a i)\u207b\u00b9)\u207b\u00b9) + (Nat.clog 2 N.toNat : \u2124)") in f
    # a set of integers, a family over it, a function declared in the item and applied
    assert k == ("  \u2200 (cal_K : Set \u2124) (\u03b8 : \u2124 \u2192 \u211a) (k_star : \u2124) (\u03b8_val : \u2124 \u2192 \u211a), "
                 "(\u2200 t : \u2124, t \u2208 cal_K \u2192 0 \u2264 \u03b8 t) \u2192 (k_star \u2208 cal_K) \u2192 "
                 "(\u2200 (k : \u2124), k \u2208 cal_K \u2192 (\u03b8_val k \u2265 \u03b8 k)) \u2192 \u03b8_val k_star \u2265 0")


# ---------------------------------------------------------------- signs, intervals, sets, symbols

SIGNS_SETS = [  # a statement item and its Q++; each reads back from Q++ and from the canonical LaTeX
    (r"I_\pm\ne\varnothing", "I_plus != empty, I_minus != empty"),
    (r"x=a\pm b", "x = a + b or x = a - b"),  # one of two values: the sign on one side of an equation
    # the sign of the side: a term of a sum, a factor, a tuple component; one of two values
    (r"x=\pm y+1", "x = y + 1 or x = -y + 1"),
    (r"x=1\pm y", "x = 1 + y or x = 1 - y"),
    (r"x=\pm y\mp z", "x = y - z or x = -y + z"),
    (r"R=\pm a^kb^l", "R = a^k * b^l or R = -(a^k * b^l)"),
    (r"(a_0,b_0)=(\pm x^2,0)", "(a_0, b_0) = (x^2, 0) or (a_0, b_0) = (-x^2, 0)"),
    # a sign inside an argument, a subscript or an exponent: both readings hold
    (r"f(\pm x)=f(x)", "f(x) = f(x), f(-x) = f(x)"),
    (r"f(x\pm1)=f(x)", "f(x + 1) = f(x), f(x - 1) = f(x)"),
    (r"u_\pm=\pm v", "u_plus = v, u_minus = -v"),
    (r"2^{\pm e}=y", "2^e = y, 2^(-e) = y"),
    (r"\one\ne b_1,\ b_0\ne\bx", "b_one != b_1, b_0 != b_x"),  # the vector of ones and b with index 1
    (r"s\in\{\pm1\},\ \boldsymbol\varsigma\in\{\pm1\}^n", "s in {1, -1}, b_varsigma in {1, -1}^n"),
    (r"P_\pm:=\textstyle\sum_{A_\pm}|c_i|", "P_plus := (sum i in A_plus, |c_(i)|), P_minus := sum i in A_minus, |c_(i)|"),
    (r"Q_\pm(\bx):=\textstyle\sum_{\pm d_k>0}|d_k|",
     "Q_plus(b_x) := (sum k with d_(k) > 0, |d_(k)|), Q_minus(b_x) := sum k with -d_(k) > 0, |d_(k)|"),
    (r"x\in(0,1],\ y\in[0,1),\ \bu\in(\tfrac12,1]^n", "x in (0, 1], y in [0, 1), b_u in (1 / 2, 1]^n"),
    (r"\varepsilon\in\Q\cap(0,\tfrac1{8r}]", "varepsilon in QQ cap (0, 1 / (8 * r)]"),
    (r"j\in\{1,\dots,p-1\},\ m\in\{1,2\}", "j in {1..p - 1}, m in {1, 2}"),
    (r"k:=\min\{k:\ g_k\ge0\}", "k := min {k : g_(k) >= 0}"),
    (r"\lambda:=\min_{s_r>0}o_r/s_r", "lambda := min r with s_(r) > 0, o_(r) / s_(r)"),
    (r"\max_{2\le i\le j+1}|G_i|\le1", "(max i in 2..j + 1, |G_(i)|) <= 1"),
    (r"\#\{k:\ g_k\ge0\}\le1", "card({k : g_(k) >= 0}) <= 1"),
    (r"K\asymp K',\ A\mid B,\ U\supseteq V", "K asymp K', A divides B, U supseteq V"),
]


@pytest.mark.parametrize("tex,qpp", SIGNS_SETS)
def test_signs_intervals_sets_and_symbols(tex, qpp):
    parts, _ = T.parse_stmt(tex)
    assert T.stmt_print(parts, T.to_qpp) == qpp
    assert T.parse_qpp_item(qpp) == parts
    assert T.stmt_round_trip(tex)[:2] == (True, True)


def test_a_relation_symbol_without_a_row_is_a_hole_in_lean():
    with pytest.raises(T.Hole):
        T.to_lean(T.parse_tex(r"K\asymp K'"))
    # divisibility is read in Z (in Q it would always hold; a count is cast up)
    assert T.to_lean(T.parse_tex(r"A\mid B")) == "(A : \u2124) \u2223 (B : \u2124)"
    assert T.to_lean(T.parse_tex(r"x\in(0,1]")) if False else T.to_lean(T.parse_tex(r"(0,1]")) == "Set.Ioc 0 1"
    assert T.to_lean(T.parse_tex(r"[0,1)")) == "Set.Ico 0 1"
    assert T.to_lean(T.parse_tex(r"\{1,-1\}")) == "{1, -1}"


SIGNS = r"""\begin{lemmaS}\label{lem:s}\begin{stmt}\sit{given}{\epsilon,x,y,a,b\in\Q}
\sit{(1)}{\epsilon=\pm1\Rightarrow\epsilon^2=1}\sit{(2)}{|x\pm y|\le|x|+|y|}\sit{(3)}{x^2=y^2\Rightarrow x=\pm y}
\sit{(4)}{(a\pm b)^2=a^2\pm2ab+b^2}\end{stmt}\end{lemmaS}"""


def test_an_equation_with_a_sign_on_one_side_is_one_of_two_values():
    """x = \\pm y is x = y or x = -y (in a conclusion); a clause with the sign on both sides, or an order, is read
    twice (both readings hold); a part with the sign in its context is read twice as a whole, one sign at a time"""
    text, _ = latex2qpp.convert(SIGNS, "T")
    assert "  (1): epsilon = 1 => epsilon^2 = 1; epsilon = -1 => epsilon^2 = 1\n" in text
    assert "  (2): |x + y| <= |x| + |y|, |x - y| <= |x| + |y|\n" in text
    assert "  (3): x^2 = y^2 => x = y or x = -y\n" in text
    assert "  (4): (a + b)^2 = a^2 + 2 * a * b + b^2, (a - b)^2 = a^2 - 2 * a * b + b^2\n" in text
    lean, _, _ = qpp2lean.generate(text)
    s = [ln for ln in lean.splitlines() if ln.startswith("  \u2200")][0]
    assert "(((\u03b5 = 1) \u2192 \u03b5 ^ 2 = 1) \u2227 ((\u03b5 = -1) \u2192 \u03b5 ^ 2 = 1))" in s
    assert "((x ^ 2 = y ^ 2) \u2192 (x = y) \u2228 (x = -y))" in s


def test_a_parenthesized_equivalence_after_an_arrow():
    text, _ = latex2qpp.convert(r"\begin{lemmaS}\label{lem:e}\begin{stmt}\sit{(1)}{x\in\Q\Rightarrow(x\le1\iff x+1\le2)}"
                                r"\end{stmt}\end{lemmaS}", "T")
    assert "  (1): x in QQ => x <= 1 <=> x + 1 <= 2\n" in text
    lean, _, _ = qpp2lean.generate(text)
    assert "\u2200 (x : \u211a), (x \u2264 1) \u2194 (x + 1 \u2264 2)" in lean


@pytest.mark.parametrize("tex,data,qpp", [
    (r"(x\preceq y)+2(y\preceq z)", True, "(x preceq y) + 2 * (y preceq z)"),  # a certificate citing two hypotheses
    (r"\kappa_1^{-1}(\kappa_2^{-1}v\le u)+(\kappa_1^{-1}u\le x)", True,
     "kappa_1^(-1) * (kappa_2^(-1) * v <= u) + (kappa_1^(-1) * u <= x)"),  # symbolic coefficients
    (r"(y\le x)", True, "(y <= x)"),  # a citation keeps its parentheses
    (r"(y\le x)", False, "y <= x"),  # elsewhere a parenthesized relation is the relation
    (r"(x\preceq y)+2(y\preceq z)", False, None),  # a combination of claims only in the data of a word
    (r"\{K\le1\}\subseteq\{K\le2\}", False, "{K <= 1} subseteq {K <= 2}"),  # claims of a set builder are its own
    (r"b_k>0\ (k\ge1)", False, None),  # a side condition, not a factor
    (r"\xi_h:=1\ (h\ge3)", False, None),
    (r"2x\ (x\ge-t)", False, None),  # a piece of a case split
    (r"0\ (j<k)", True, None),
    (r"f((x\le1))", True, None),
])
def test_a_claim_in_parentheses_is_a_term_only_in_a_combination(tex, data, qpp):
    T.DATA_MODE[0] = data
    try:
        if qpp is None:
            with pytest.raises(T.Hole):
                T.parse_tex(tex)
        else:
            x = T.parse_tex(tex)
            assert T.to_qpp(x) == qpp and T.parse_qpp_list(qpp) == [x]
    finally:
        T.DATA_MODE[0] = False


def test_style_warnings_on_hypothesis_only_indices_and_min_max():
    """warnings, not errors: the statement is generated as it reads. An index only in a hypothesis reads 'for
    every index' there; a written range (j <= N) or a declaration says so and silences it; a min or a max asks
    for the semifield form"""
    src = r"""\begin{lemma}\label{lem:w}\begin{stmt}\sit{given}{N\in\Z_{\ge1},\ a_1,\dots,a_N\in\Q,\ m\in\Q}
\sit{(1)}{a_j\le m\Rightarrow\textstyle\sum_ja_j\le Nm}\sit{(2)}{a_j\le m\ \text{for}\ j\le N\Rightarrow\textstyle\sum_ja_j\le Nm}
\end{stmt}\end{lemma}
\begin{lemma}\label{lem:v}\begin{stmt}\sit{given}{K,L\in\Q}\sit{(1)}{\min(K,L)\le K}\end{stmt}\end{lemma}"""
    text, _ = latex2qpp.convert(src, "T")
    lean, made, skipped = qpp2lean.generate(text)
    w = qpp2lean.LAST_WARNINGS
    assert [lab for lab, _ in w] == ["lem:w", "lem:v"]
    assert w[0][1].startswith("the index j occurs only in a hypothesis") and "min or a max" in w[1][1]
    assert "/-! Warnings (2)" in lean


EDGES = r"""\begin{lemma}\label{lem:hname}\begin{stmt}\sit{given}{h_1,x\in\Q,\ h_1\ge0,\ x\le h_1}
\sit{(1)}{x\le2h_1}\end{stmt}\end{lemma}
\begin{proof}\begin{expr}\eit{(1)}{\alpha[(h_1\ge0)+(x\le h_1)]}\end{expr}\end{proof}
\begin{lemma}\label{lem:wrong}\begin{stmt}\sit{given}{x,y\in\Q,\ x\le y}\sit{(1)}{x\le y+1}\end{stmt}\end{lemma}
\begin{proof}\begin{expr}\eit{(1)}{\alpha[(y\le x)]}\end{expr}\end{proof}
\begin{lemma}\label{lem:flip}\begin{stmt}\sit{given}{x,y\in\Q,\ x\le y}\sit{(1)}{x\le y+1}\end{stmt}\end{lemma}
\begin{proof}\begin{expr}\eit{(1)}{\alpha[(y\ge x)]}\end{expr}\end{proof}
\begin{lemma}\label{lem:coef}\begin{stmt}\sit{given}{u,v,x,\kappa\in\Q,\ \kappa>0,\ u\le\kappa v,\ x\le\kappa u}
\sit{(1)}{x\le\kappa^2v}\end{stmt}\end{lemma}
\begin{proof}\begin{expr}\eit{(1)}{\alpha[(x\le\kappa u)+\kappa(u\le\kappa v)]}\end{expr}\end{proof}"""


def test_citation_edges():
    """the hypotheses of a paper with a variable h_1 get names it does not use (hyp_1, ...); a citation that
    matches no hypothesis is an error, not a claim; x >= y cites y <= x; a symbolic coefficient times a citation"""
    text, _ = latex2qpp.convert(EDGES, "T")
    assert "  (1) alpha[(y <= x)]\n" in text and "  (1) alpha[(x <= kappa * u) + kappa * (u <= kappa * v)]\n" in text
    lean, made, skipped = qpp2lean.generate(text)
    assert "(h\u2081 x : \u211a) (hyp\u2081 : h\u2081 \u2265 0) (hyp\u2082 : x \u2264 h\u2081)" in lean
    assert "qpp alpha[hyp\u2081 + hyp\u2082]" in lean
    assert dict(skipped)["lem:wrong"] == "stated; proof: the citation (y <= x) matches no hypothesis"
    assert "qpp alpha[h\u2081]" in lean.split("lem_flip")[2]
    assert "qpp alpha[h\u2083 + \u03ba * h\u2082]" in lean
    assert made == ["lem:hname", "lem:flip", "lem:coef"]



# ---------------------------------------------------------------- items one by one, members of families

ITEMS = r"""\begin{lemma}\label{lem:parts}\begin{stmt}\sit{given}{x,y\in\Q,\ x\le y}\sit{(1)}{x\le y+1}
\sit{(2)}{x\ \text{inside}\ \mathcal K}\sit{(3)}{z\in\Q,\ z\ge0\Rightarrow x\le y+z}\end{stmt}\end{lemma}
\begin{proof}\begin{expr}\eit{(1)}{\alpha[(x\le y)]}\eit{(3)}{\alpha[(x\le y)+(z\ge0)]}\end{expr}\end{proof}
\begin{lemma}\label{lem:givenhole}\begin{stmt}\sit{given}{x\in\Q,\ x\ \text{inside}\ \mathcal K}\sit{(1)}{x\le x}
\sit{(2)}{x\ge x}\end{stmt}\end{lemma}"""


def test_items_stand_one_by_one():
    """a hole in one conclusion does not block the others: each item with the given clauses is its own statement
    (lem_parts.item_1.statement), proved by its own line; a hole in the given that mentions a name of the
    conclusions (here the whole given, so x is declared by no formal clause) blocks every item"""
    text, rep = latex2qpp.convert(ITEMS, "T")
    lean, made, skipped = qpp2lean.generate(text)
    assert "abbrev lem_parts.item_1.statement : Prop :=" in lean and "abbrev lem_parts.item_3.statement" in lean
    assert "theorem lem_parts.item_1 " in lean and "theorem lem_parts.item_3 " in lean
    assert "abbrev lem_parts.statement" not in lean and "item_2" not in lean
    assert made == ["lem:parts(1)", "lem:parts(3)"]
    why = dict(skipped)
    assert why["lem:parts"] == "items: stated (1), (3); (2) item (2) has a hole"
    assert why["lem:givenhole"] == "item given has a hole that mentions x, which a conclusion uses"
    assert qpp2lean.LAST_ITEMS["lem:parts"]["proved"] == ["(1)", "(3)"]


@pytest.mark.parametrize("tex, lean", [
    # f_0 is the member f_(0) of the family f_0, ..., f_D (A, lem:constants (2))
    (r"D\in\Z_{\ge0},\ c\in\Q_{\ge0},\ f_0,\dots,f_D\in\Q,\ |f_{i+1}-f_i|\le c\ \text{for}\ i<D\Rightarrow|f_D-f_0|\le cD",
     "|f D.toNat - f 0| \u2264 c * D"),
    # a_1 is a member of the sequence a_i; x_0 is not a member of x_1, ..., x_N
    (r"a_i\in\Q_{\ge0}\Rightarrow a_1+a_2\ge0", "(\u2200 i : \u2115, 0 \u2264 a i) \u2192 a 1 + a 2 \u2265 0"),
    # W_j, W_{j+1} in Z>=0 with j declared: hypotheses at j and j + 1, not for every index; j in Z: W is a family
    # over the integers (no toNat, which would identify W_(-1) with W_(0))
    (r"j\in\Z_{\ge0},\ W_j,W_{j+1}\in\Z_{\ge0},\ W_{j+1}\ge2W_j\Rightarrow W_{j+1}\ge W_j",
     "\u2200 (j : \u2124) (W : \u2124 \u2192 \u2124), (0 \u2264 j) \u2192 (0 \u2264 (W j)) \u2192 (0 \u2264 (W (j + 1))) \u2192"),
])
def test_members_of_families(tex, lean):
    q = latex2qpp.stmt_formula(tex)[0]
    _bs, _hs, concl = qpp2lean.statement([("(1)", q)])
    assert lean in concl[0][1]


def test_a_numeric_name_outside_the_range_is_its_own_name():
    with pytest.raises(qpp2lean.Skip, match="undeclared \\['x_0'\\]"):
        qpp2lean.statement([("(1)", "x_(1..N) in QQ, N in ZZ>=1 => x_0 >= 0")])
    _bs, _hs, concl = qpp2lean.statement([("(1)", "a_(i) in QQ>=0, a_1 in QQ => a_1 + a_(2) >= 0")])
    assert "a\u2081 + a 2" in concl[0][1]


@pytest.mark.parametrize("tex, lean", [
    # the floor and the ceiling are Int.floor and Int.ceil: Nat.floor of a negative rational is 0
    (r"t\in\Q\Rightarrow\lfloor t\rfloor\le t", "\u2200 (t : \u211a), \u230a(t : \u211a)\u230b \u2264 t"),
    (r"t\in\Q\Rightarrow t\le\lceil t\rceil", "t \u2264 \u2308(t : \u211a)\u2309"),
    # the division of the semifield: n / 2 with n, m in Z is rational (Lean's n / 2 on Z truncates)
    (r"n,m\in\Z\Rightarrow n/2\le m", "(n / 2 : \u211a) \u2264 m"),
    (r"n\in\Z_{\ge0}\Rightarrow\lfloor n/2\rfloor\le n", "\u230a(n / 2 : \u211a)\u230b \u2264 n"),
    # an exponent that may be negative needs a rational base (zpow), also when no rational name is near
    (r"e,f\in\Z\Rightarrow2^{-e}\le2^{-f}", "(2 : \u211a) ^ (-e) \u2264 (2 : \u211a) ^ (-f)"),
    (r"n,m\in\Z_{\ge0}\Rightarrow m\le2^n-1", "m \u2264 (2 : \u211a) ^ n - 1"),
    (r"x\in\Q_{>0},\ k\in\Z\Rightarrow x^{-k}>0", "x ^ (-k) > 0"),
])
def test_printed_in_q(tex, lean):
    q = latex2qpp.stmt_formula(tex)[0]
    _bs, _hs, concl = qpp2lean.statement([("(1)", q)])
    assert lean in concl[0][1]


def test_operator_definitions_reach_every_item():
    """an operator definition of the result (a row parallel sum: a par b := R) is read by every item, like the given
    clauses, and is not an item of its own"""
    tex = (r"\begin{lemma}\label{lem:par}\begin{stmt}\sit{given}{a,b\in\Q_{>0}}\sit{(1)}{a\parallel b\le a}"
           r"\sit{(2)}{a\parallel b\ \text{inside}\ \mathcal K}\sit{parallel sum}{a\parallel b:=(a^{-1}+b^{-1})^{-1}}"
           r"\end{stmt}\end{lemma}")
    text, _ = latex2qpp.convert(tex, "T")
    lean, _, skipped = qpp2lean.generate(text)
    assert "abbrev lem_par.item_1.statement : Prop :=\n  \u2200 (a b : \u211a) (h\u2081 : 0 < a) (h\u2082 : 0 < b), " \
           "(a\u207b\u00b9 + b\u207b\u00b9)\u207b\u00b9 \u2264 a\n" in lean
    assert "parallel" not in lean.split("/-! Not generated")[0].replace("[lem:par(1)]", "")
    assert dict(skipped)["lem:par"].startswith("items: stated (1);")


def test_a_quantified_clause_of_the_context_is_kept():
    """the context row e : Q>0 -> Z, 2^(-e(x)-1) < x <= 2^(-e(x)) for x in Q>0 gives e with its spec (dropping the
    clause would leave any e, and a false statement); a clause naming what the context does not declare blocks"""
    tex = (r"\begin{stmt}\sit{context}{e:\Q_{>0}\to\Z,\ 2^{-e(x)-1}<x\le2^{-e(x)}\ \text{for}\ x\in\Q_{>0}}\end{stmt}"
           r"\begin{lemma}\label{lem:ex}\begin{stmt}\sit{given}{x\in\Q_{>0}}\sit{(1)}{x\le2^{-e(x)}}\end{stmt}"
           r"\end{lemma}")
    text, _ = latex2qpp.convert(tex, "T")
    lean, _, _ = qpp2lean.generate(text)
    assert ("\u2200 (e : \u211a \u2192 \u2124) (x : \u211a) (h\u2081 : \u2200 (x : \u211a), 0 < x \u2192 "
            "((2 : \u211a) ^ (-e x - 1 : \u2124) < x \u2227 x \u2264 (2 : \u211a) ^ (-e x : \u2124))) (h\u2082 : 0 < x), "
            "x \u2264 (2 : \u211a) ^ (-e x : \u2124)") in lean
    lean, _, skipped = qpp2lean.generate(text.replace("2^(-e(x) - 1) < x", "2^(-e(x) - 1) < y"))
    assert "lem_ex" not in lean and "the context does not declare" in dict(skipped)["lem:ex"]
    # a statement that declares its own e does not read the context's e
    own = text + "lemma lem:own\n  given: e in ZZ, x in QQ>0\n  (1): x <= 2^(-e) * x\n"
    lean, _, _ = qpp2lean.generate(own)
    assert ("abbrev lem_own.statement : Prop :=\n  \u2200 (e : \u2124) (x : \u211a) (h\u2081 : 0 < x), "
            "x \u2264 (2 : \u211a) ^ (-e) * x\n") in lean


@pytest.mark.parametrize("tex, qpp", [
    # a list of terms of one shape with the relation next to it: the relation for each
    (r"|S(\bw,a)|,|S(\bw,b)|\ge2\varepsilon", "|S(b_w, a)| >= 2 * varepsilon, |S(b_w, b)| >= 2 * varepsilon"),
    (r"x,y\ge0", "x >= 0, y >= 0"),
    (r"M\ge1,M\ge|U|,|V|,\ N\in\Z", "M >= 1, M >= |U|, M >= |V|, N in ZZ"),
    (r"M\ge|U|,|V|,M\ge X", "M >= |U|, M >= |V|, M >= X"),
    (r"\varepsilon\le\gamma,\ |S(\bw,a)|,|S(\bw,b)|\ge2\varepsilon",
     "varepsilon <= gamma, |S(b_w, a)| >= 2 * varepsilon, |S(b_w, b)| >= 2 * varepsilon"),
    (r"(l=1,2)\Rightarrow x_l\ge0", "l in {1, 2} => x_(l) >= 0"),
    # a reference to an item is not a product; a reference in parentheses after a clause is a gloss
    (r"\cref{lem:strata}(1)", "@lem:strata(1)"),
    (r"1-q=|P|\ (\cref{lem:valuation}(2))", "1 - q = |P|"),
    # a term where a clause is expected is a hole (it was read as a clause of its own)
    (r"|D|=4:\ (0,1),\ K=0", None),
    (r"\mathrm{Band}(Q,c,a,\varepsilon),\ 1\le a\le A_c", None),
    (r"G=I:\ (D_u)\ \text{with}\ \kappa_u=m_0", None),
    (r"M\ge|U|,|V|,|W|\ge2", None),
    (r"p=2\Rightarrow(\tfrac32,1)", None),
])
def test_lists_and_clauses(tex, qpp):
    assert T.stmt_round_trip(tex)[3] == qpp


@pytest.mark.parametrize("tex, functions, qpp", [
    # a letter applied to a number or a tuple is an application of a declared function, else a hole (never a product)
    (r"\rho(0)=1", (), None),
    (r"\Delta_P(\mathbf a_0,\boldsymbol\xi)\ne0", (), None),
    (r"\rho(0)=1", ("rho",), "rho(0) = 1"),
    (r"K\ge c(c_0^2+e^2)", (), "K >= c * (c_0^2 + e^2)"),
    (r"x\in u(0,1]", (), "x in u * (0, 1]"),
    # f_(theta_star)(b_x): an indexed function letter applied, read back by the Q++ reader
    (r"f_{\theta^*}(\bx_{i_0})\ge0", ("f",), "f_(theta_star)(b_x_(i_0)) >= 0"),
    # ^0 and ^\circ are labels, ^{(j)} a member of a family (a hole for now), never powers
    (r"a^0_h>0", (), "a_nought_(h) > 0"),
    (r"x^\circ\le1", (), "x_circ <= 1"),
    (r"h^{(j)}\le1", (), None),
    (r"2^0=1", (), "2^0 = 1"),
    # := defines a name, a member, a function at names, a tuple, an operator; not a value
    (r"\tfrac{k-3}{5+\infty}:=0", (), None),
    (r"cK:=1", (), None),
    (r"(\lambda,m):=(1,2)", (), "(lambda, m) := (1, 2)"),
    # the sign of one side of a chain of equations: one of the two values
    (r"N_{j,0}=N_{j,1}=\mp e", (), "N_(j, 0) = N_(j, 1) = -e or N_(j, 0) = N_(j, 1) = e"),
    # a binder that is not last in a list is parenthesized
    (r"c_0:=\textstyle\sum_ha_h,\ s:=1", (), "c_0 := (sum h, a_(h)), s := 1"),
    (r"h_+:=\max(\max_h\delta_h,0)", (), "h_plus := max((max h, delta_(h)), 0)"),
])
def test_letters_labels_and_definitions(tex, functions, qpp):
    r = T.stmt_round_trip(tex, functions)
    assert r[3] == qpp and (qpp is None or r[1])


def test_function_letters_of_a_paper():
    """a function is defined (rho_{a,d}(x') := ..., keyed rho_: a family is another name than rho) or declared
    (theta : Q^d -> Q); an application to a numeral or a tuple is evidence for its result or a hole elsewhere; a
    letter in a subscript, a superscript, a command, after an accent or in \\text is not a head; a pairing
    <w, x> has no comma"""
    src = (r"\rho_{\ba,\bd}(x'):=\sum_ha_h,\ \rho(0)=1,\ \Delta_P(\mathbf a_0,\boldsymbol\xi)\ne0,\ "
           r"\theta\colon\Q^d\to\Q,\ x\in(0,1],\ c(c_0^2+e^2),\ u(0,1],\ \gInd_s(2),\ R_j^\eta(x,y),\ \mathbf c(t):=t\one,\ "
           r"\dot z_{hi}(\vartheta):=0,\ a_h(\langle w_h,x\rangle+b_h),\ \text{see f(2)}")
    assert latex2qpp.functions_of(src) == {"rho_", "theta", "b_c"}
    assert latex2qpp.heads(latex2qpp.FUNC_NUM, src) == {"rho"}
    assert latex2qpp.heads(latex2qpp.FUNC_TUPLE, src) == {"Delta_"}
    for t, names in [(r"t\in[0,1]", {"t"}), (r"a\ \text{mass},\ q\in\Z_{\ge1}", {"a", "q"}), (r"g\in\Q[y]", set()),
                     (r"\bx\in\Q^n", {"b_x", "x_"}), (r"y_a\in\Q", {"y_"}), (r"\langle w,x\rangle\in\Q", set())]:
        assert latex2qpp.scalars_of(t) == names, t


SCOPES = (r"\begin{definition}\label{def:c}\begin{stmt}\sit{cost}{c(x):=x^2}\end{stmt}\end{definition}"
          r"\begin{lemma}\label{lem:num}\begin{stmt}\sit{given}{c,t\in\Q,\ a_h\in\Q}\sit{(1)}{c(t+1)\ge a_h(t-1)^2}"
          r"\end{stmt}\end{lemma}"
          r"\begin{lemma}\label{lem:cite}\begin{stmt}\sit{given}{y\in\Q}\sit{(1)}{c(y)\ge0\ \ (\cref{def:c})}\end{stmt}"
          r"\end{lemma}"
          r"\begin{lemma}\label{lem:far}\begin{stmt}\sit{given}{y\in\Q}\sit{(1)}{c(y)\ge0}\sit{(2)}{u(y+1)\ge0}"
          r"\end{stmt}\end{lemma}"
          r"\begin{lemma}\label{lem:zero}\begin{stmt}\sit{given}{y\in\Q}\sit{(1)}{\kappa(0)=0\Rightarrow\kappa(y)\ge0}"
          r"\end{stmt}\end{lemma}"
          r"\begin{lemma}\label{lem:fam}\begin{stmt}\sit{given}{t\in\Q,\ \bx\in\Q^n}\sit{(1)}{t_a(\bx)\ge t(1+t)}"
          r"\end{stmt}\end{lemma}"
          r"\begin{lemma}\label{lem:clash}\begin{stmt}\sit{given}{\ba\in\Q^n}"
          r"\sit{(1)}{N<P\ \text{masses}\Rightarrow P(\ba)>N}\end{stmt}\end{lemma}")


def test_a_name_before_a_parenthesis_reads_by_its_scope():
    """X(E) is an application if X is a function in the result (defined there, in a cited result, or in the paper
    and never a number; applied to a numeral there; a function letter), a product if X is a number there (its given
    or its item), and a hole otherwise: a guess either way is a misreading somewhere (a_h(x - delta_h)^p, a(z_q(v)))"""
    text, _ = latex2qpp.convert(SCOPES, "T")
    assert "  (1): c * (t + 1) >= a_(h) * (t - 1)^2\n" in text  # numbers of the given, c a function elsewhere
    assert "  (1): c(y) >= 0\n" in text  # c by the cited definition
    assert "  (1): ?{c(y)\\ge0}\n" in text  # c is a function and a number in the paper: no guess
    assert "  (2): ?{u(y+1)\\ge0}\n" in text  # u is neither
    assert "  (1): kappa(0) = 0 => kappa(y) >= 0\n" in text  # applied to a numeral in its result
    assert "  (1): ?{t_a(\\bx)\\ge t(1+t)}\n" in text  # t is a number, the family t_ is not declared
    assert "  (1): ?{N<P\\ \\text{masses}\\Rightarrow P(\\ba)>N}\n" in text  # P a function letter and a mass there


def test_a_proof_belongs_to_the_first_label():
    from qpp import syntax
    src = (r"\begin{lemma}\label{lem:slab}\label{lem:persist} x \begin{equation}\label{eq:a} y\end{equation}"
           r"\end{lemma}" "\n" r"\begin{proof}\begin{expr}\eit{(1)}{\alpha}\end{expr}\end{proof}")
    assert [s[2] for s in syntax.proof_spans(src)] == ["lem:slab"]


def test_an_operator_is_defined_once_for_the_paper():
    """a\\parallel b:=... in one result (def:mass) is a define row of the paper: a result that uses the operator
    without its own row expands it"""
    tex = (r"\begin{definition}\label{def:mass}\begin{stmt}\sit{parallel sum}{a\parallel b:=(a^{-1}+b^{-1})^{-1}}"
           r"\end{stmt}\end{definition}"
           r"\begin{lemma}\label{lem:p}\begin{stmt}\sit{given}{a,b\in\Q_{>0}}\sit{(1)}{a\parallel b\le a}\end{stmt}"
           r"\end{lemma}")
    text, _ = latex2qpp.convert(tex, "T")
    assert "define a par b := (a^(-1) + b^(-1))^(-1)\n" in text
    lean, _, _ = qpp2lean.generate(text)
    assert "(h\u2082 : 0 < b), (a\u207b\u00b9 + b\u207b\u00b9)\u207b\u00b9 \u2264 a\n" in lean


def test_statements_module():
    """--statements: the abbrevs alone, as a public module (the paper's Lean proves them by hand)"""
    text = (FIX / "review.qpp").read_text(encoding="utf-8")
    lean, made, _ = qpp2lean.generate_statements(text)
    assert lean.startswith("module\n\npublic import Mathlib\n") and "@[expose] public section\n" in lean
    assert "namespace Qpp.Review.Stated\n" in lean and "theorem" not in lean and "import QPP" not in lean
    assert made == ["lem:halfopen", "lem:pm", "lem:preceq", "lem:context", "lem:sets"]


BRIDGE_SLICE = r"""\begin{definition}\label{def:w}\begin{stmt}
\sit{}{a,p\in\Z:\ a\ \text{a square mod}\ p:\iff\exists x\in\Z:\ p\mid x^2-a}\end{stmt}\end{definition}
\begin{lemma}\label{lem:iff}\begin{stmt}\sit{given}{m\in\N_{\ge1},\ p:=2m+1,\ a\in\Z,\ p\nmid a}
\sit{(1)}{-1\ \text{a square mod}\ p\iff2\mid m}
\sit{(2)}{2\mid m\Rightarrow(a\ \text{a square mod}\ p\iff p\ \text{a square mod}\ a)}
\sit{(3)}{\#\{k\in\Z:\ 1\le k\le m,\ 4k>p\}=m-\lfloor p/4\rfloor}\end{stmt}\end{lemma}"""


def test_equivalences_and_conjunctions_in_statements():
    """a part may be an equivalence (A <=> B, not a definition :<=>); a relational word on either side of <=> is
    parenthesized in Q++; an equivalence after hypotheses is parenthesized in Lean (where <-> binds looser than ->);
    the conditions of a set builder are a conjunction; divisibility is read in Z (with \u00ac for \\nmid)"""
    text, rep = latex2qpp.convert(BRIDGE_SLICE, "T")
    assert all(i["formal"] for i in rep["items"])
    assert "  (1): (-1 #square_mod p) <=> 2 divides m\n" in text
    assert "  (2): 2 divides m => (a #square_mod p) <=> (p #square_mod a)\n" in text
    lean, _, skipped = qpp2lean.generate(text)
    assert "(h\u2083 : \u00ac((p : \u2124) \u2223 (a : \u2124)))" in lean
    assert "((2 : \u2124) \u2223 (m : \u2124)) \u2192 ((\u2203 (x : \u2124), ((p : \u2124) \u2223 (x ^ 2 - a : \u2124))) \u2194" in lean
    assert "{k : \u2124 | (1 \u2264 k \u2227 k \u2264 m) \u2227 (4 * k > p)}" in lean
    # a floor is the integer floor of a rational: p / 4 is not a division of counts, and a negative argument
    # keeps its sign
    assert "= m - \u230a(p / 4 : \u211a)\u230b" in lean
    assert dict(skipped)["lem:iff"] == "stated; proof: no proof lines"


def test_alias_heads_keep_their_slots_and_place():
    r"""an alias defined with slots prints them in brackets (alias Bez[a,b] := ...), and \mathrm{Scale}_p := ... is
    the definition of the alias Scale_p"""
    src = (r"\begin{itemize}\item \(\gBez[a,b]:=\gI[ua+vb=d]\circ\gEu[\Z]\), the identity."
           r"\item \(\mathrm{Scale}_p:=\gInd_k\circ\gEu[\Z]\), the scale at p.\end{itemize}")
    text, _ = latex2qpp.convert(src, "T")
    assert "alias Bez[a,b] := I[u * a + v * b = d] o Euclid[ZZ]\n" in text
    assert "alias Scale_p := ind_k o Euclid[ZZ]\n" in text


def test_status_page_lists_labels_declarations_and_cited_leaves(tmp_path):
    """qpp/status.py: a label is formalized (a theorem is tagged with it), defined, cited (a fact, with its
    hypothesis structure) or not formalized; the structures ... : Prop are the external cited leaves; the column
    compiled counts the match examples of a label (its statement compiles and a declaration is tagged with it)"""
    from qpp import status
    (tmp_path / "p" / "latex").mkdir(parents=True)
    (tmp_path / "p" / "lean" / "P").mkdir(parents=True)
    (tmp_path / "p" / "latex" / "p.tex").write_text(
        "\\begin{fact}[Ostrowski]\\label{fact:bands}x \\cite{O1940}\\end{fact}\n\\begin{lemma}\\label{lem:a}x"
        "\\begin{stmt}\\sit{given}{x\\in\\Q}\\sit{(1)}{x\\le x}\\end{stmt}\\end{lemma}\n"
        "\\begin{definition}\n\\label{def:b}x\\end{definition}\n\\begin{theorem}\\label{thm:c}x\\end{theorem}\n",
        encoding="utf-8")
    (tmp_path / "p" / "lean" / "P" / "A.lean").write_text(
        "/-- [p:fact:bands] Ostrowski's bound (Ostrowski 1940). More. -/\nstructure Gap : Prop where\n  h : True\n"
        "/-- [p:lem:a] (1) [p:def:b] The lemma. -/\ntheorem a (g : Gap) : True := trivial\n"
        "/-- [p:def:b] The word. -/\ndef b : Nat := 0\n"
        "/-- [p:thm:c] (step gap) A line of the proof. -/\ntheorem c_gap : True := trivial\n", encoding="utf-8")
    text = status.page("p", tmp_path)
    assert "| `fact:bands` | fact | cited (hypothesis Gap) | 1 | - | - | - | `Gap` |" in text
    # the statement of lem:a compiles, and a tagged declaration is to prove it: one match example
    assert "| `lem:a` | lemma | formalized | 1 | (1) | 1 | - | `a` |" in text
    assert "| `def:b` | definition | formalized | 2 | - | - | - | `a`, `b` |" in text
    # a declaration of a proof step (step ...) is counted apart
    assert "| `thm:c` | theorem | proof steps only | 0 | - | - | 1 |  |" in text
    assert "Labels with a compiled statement to match: 1; match examples: 1." in text
    assert "| `Gap` | `P/A.lean` | fact:bands | fact:bands | Ostrowski's bound (Ostrowski 1940). |" in text
    assert "not backed by the LaTeX" not in text


def test_match_takes_the_cited_facts_of_the_declaration(tmp_path):
    """a declaration that takes a cited fact (structure X : Prop with no parameters) is matched with the fact as a
    hypothesis of the example, so that the premise apply leaves is closed by assumption; a parameterized structure
    (a hypothesis about particular data) is not a cited fact of this kind"""
    from qpp import leanrefs
    (tmp_path / "F.lean").write_text(
        "namespace P\n"
        "/-- [p:fact:ms] Motzkin and Straus 1965, cited. -/\nstructure MS : Prop where\n  h : True\n"
        "/-- [p:fact:bands] Ostrowski, about particular data. -/\nstructure Bands (q : Nat) : Prop where\n  h : True\n"
        "/-- [p:lem:m] (sums) uses the fact. -/\ntheorem m_sums (hMS : MS) (x y : Nat) (hB : Bands x) : x \u2264 y + x := by omega\n"
        "/-- [p:lem:m] (2) does not. -/\ntheorem m_two : True := trivial\n"
        "end P\n", encoding="utf-8")
    prem = leanrefs.cited_premises(tmp_path)
    assert prem == {"P.m_sums": ["P.MS"]} and leanrefs.unregistered_facts(tmp_path) == []
    q = "paper X\nlemma lem:m\n  given: x, y in QQ\n  sums: x <= y + x\n"
    refs = leanrefs.label_map(tmp_path, paper="p")
    lean, spans, skipped = qpp2lean.generate_match(q, refs, [], premises=prem)
    assert "example (hc_1 : P.MS) : lem_m.statement := by" in lean and "given the cited facts P.MS" in lean
    lean0, _, _ = qpp2lean.generate_match(q, refs, [])
    assert "example : lem_m.statement := by" in lean0


def test_a_names_row_makes_a_subscripted_name_one_name():
    r"""\sit{names}{n_y, \kappa_{\rm new}, s_{\min}} declares names: n_y is one name, not the member n(y) of a family;
    a letter subscript elsewhere is still an index"""
    tex = (r"\begin{stmt}\sit{names}{n_y,n_e,\kappa_{\rm new},s_{\min}}\end{stmt}"
           "\n" r"\begin{lemma}\label{lem:a}x\begin{stmt}\sit{given}{n_y,n_e\in\Z_{\ge0},\ s_{\min},\kappa_{\rm new}\in\Q}"
           r"\sit{(1)}{n_e\le n_y+n_e}\sit{(2)}{s_{\min}\le s_{\min}+\kappa_{\rm new}^2}\end{stmt}\end{lemma}"
           "\n" r"\begin{lemma}\label{lem:b}x\begin{stmt}\sit{given}{a_i\in\Q}\sit{(1)}{a_y\le a_y}\end{stmt}\end{lemma}")
    text, rep = latex2qpp.convert(tex, "T")
    assert "  given: n_y, n_e in ZZ>=0, s_min, kappa_new in QQ\n" in text and "  (1): n_e <= n_y + n_e\n" in text
    assert "  (1): a_(y) <= a_(y)\n" in text and "names" not in text.split("lemma lem:a", 1)[1]
    assert all(i["formal"] and i["same"] for i in rep["items"])
    lean, made, skipped = qpp2lean.generate(text)
    assert "  \u2200 (n_y n_e : \u2124) (s_min \u03ba_new : \u211a) (h\u2081 : 0 \u2264 n_y) (h\u2082 : 0 \u2264 n_e)," in lean


def test_proof_steps_are_not_candidates_and_items_do_not_fall_back(tmp_path):
    """a declaration marked (step ...) is a proof step: label_map leaves it out and lists it with steps=True; the
    match tries for an item only the declarations tagged with it or with the label alone, and an item with none is
    listed as skipped instead of being tried with the declarations of other items"""
    from qpp import leanrefs
    (tmp_path / "S.lean").write_text(
        "/-- [p:lem:m] (sums) the item. -/\ntheorem m_sums : True := trivial\n"
        "/-- [p:lem:m] (step gap) a line of the proof. -/\nlemma m_gap : True := trivial\n", encoding="utf-8")
    refs = leanrefs.label_map(tmp_path, paper="p")
    assert refs["lem:m"] == [("m_sums", "(sums)", "theorem", "S.lean")]
    assert leanrefs.label_map(tmp_path, paper="p", steps=True)["lem:m"] == [("m_gap", None, "lemma", "S.lean")]
    q = "paper X\nlemma lem:m\n  given: x, y in QQ\n  sums: x <= y + x\n  (2): y <= y\n"
    lean, spans, skipped = qpp2lean.generate_match(q, refs, [])
    assert [t for t, _, _ in spans] == ["lem:m(sums)"] and "m_gap" not in lean
    assert ("lem:m(2)", "no declaration tagged with the item or with the label alone") in skipped


def _given_statement(given, item, names=None):
    rows = (r"\sit{names}{%s}" % names if names else "") + r"\sit{given}{%s}\sit{(1)}{%s}" % (given, item)
    text, _ = latex2qpp.convert(r"\begin{lemma}\label{lem:g}x\begin{stmt}" + rows + r"\end{stmt}\end{lemma}", "T")
    lean, made, skipped = qpp2lean.generate(text)
    return text, next((ln for ln in lean.splitlines() if ln.startswith("  \u2200")), None), skipped


@pytest.mark.parametrize("given, item, names, lean", [
    # a family by its equation for every pair of indices; theta_(i) at i in ZZ makes theta a family over ZZ
    (r"i,j\in\Z,\ \theta_i,\theta_j\in\Q;\ \sigma_{ab}:=\tfrac{\theta_a-\theta_b}{b-a}", r"\sigma_{ij}=\sigma_{ji}", None,
     "(\u03b8 : \u2124 \u2192 \u211a) (\u03c3 : \u2124 \u2192 \u2124 \u2192 \u211a) (h\u2081 : \u2200 (a : \u2124) (b : \u2124), "
     "\u03c3 a b = (\u03b8 a - \u03b8 b) / (b - a)), \u03c3 i j = \u03c3 j i"),
    # a function of a rational; a_h(E) with b_a declared is a product
    (r"k\in\N,\ \ba,\bd\in\Q^k;\ \rho(y):=\textstyle\sum_ha_h(y-\delta_h)^2", r"\rho(0)\ge0", None,
     "(\u03c1 : \u211a \u2192 \u211a) (h\u2081 : \u2200 (y : \u211a), \u03c1 y = \u2211 h : Fin k, a h * (y - \u03b4 h) ^ 2), \u03c1 0 \u2265 0"),
    # the member at a declared index
    (r"j,n\in\N,\ W_j\in\N;\ \beta'_j:=W_j+n", r"\beta'_j\ge n", None,
     "(W \u03b2' : \u2115 \u2192 \u2115) (h\u2081 : \u03b2' j = W j + n), \u03b2' j \u2265 n"),
    # a power with a negative exponent is rational, its exponent read in Z
    (r"n\in\N;\ \rho_y:=2^{-n-1}", r"\rho_y>0", r"\rho_y",
     "(\u03c1_y : \u211a) (h\u2081 : \u03c1_y = (2 : \u211a) ^ (-n - 1 : \u2124)), \u03c1_y > 0"),
    # the ceiling of lg of a term of N and of a term of Q
    (r"n\in\N,\ \kappa\in\Q_{>0};\ s_0:=\lceil\lg(n+1)\rceil+\lfloor\lg(\kappa/2)\rfloor", r"s_0\le s_0", r"s_0",
     "(h\u2082 : s\u2080 = (Nat.clog 2 (n + 1) : \u2124) + (Int.log 2 (\u03ba / 2 : \u211a))), s\u2080 \u2264 s\u2080"),
    # a sum over the components with a condition; a binomial coefficient
    (r"k,p\in\N,\ \bd\in\Q^k,\ y\in\Q", r"\textstyle\sum_{h:\delta_h<y}\binom p1\delta_h\le0", None,
     "(\u2211 h \u2208 Finset.univ.filter (fun h : Fin k => \u03b4 h < y), (Nat.choose p 1 : \u211a) * \u03b4 h) \u2264 0"),
    # a primed family, its numbered members primed either side of the subscript
    (r"U\in\N,\ k'_1,\dots,k'_U\in\N", r"k'_1+k_U'\ge0", None, "(k' : \u2115 \u2192 \u2115), k' 1 + k' U \u2265 0"),
    # varrho; a double negation is parenthesized (--x would open a Lean comment)
    (r"\varrho\in\Q_{>0},\ x\in\Q", r"-(-x)\cdot\varrho=x\varrho", None,
     "(h\u2081 : 0 < \u03f1), -(-(x * \u03f1)) = x * \u03f1"),
])
def test_definitions_in_the_given_and_new_terms(given, item, names, lean):
    """function, family and member definitions in a given, and terms of the papers (powers with an integer exponent,
    ceilings and floors of lg, sums under a condition, binomial coefficients, primed families, Greek letters, double
    negations); the shapes are compiled in Lean by the match fixture (lem:defs, lem:terms, lem:core)"""
    _text, stmt, skipped = _given_statement(given, item, names)
    assert stmt is not None, skipped
    assert lean in stmt, stmt


def test_definitions_that_stay_holes():
    """a parameter declared later in the given (rho_y := E, then y in QQ) is not guessed: a member or one name; a
    definition with some indices declared and some free is not read either"""
    _t, stmt, skipped = _given_statement(r"n\in\N;\ \rho_y:=2^{-n};\ y\in\Q", r"\rho_y>0")
    assert stmt is None and "y is declared later in the given" in skipped[0][1]
    _t, stmt, skipped = _given_statement(r"j\in\N,\ a_i\in\Q;\ \sigma_{jb}:=a_j+a_b", r"\sigma_{j1}\ge0")
    assert stmt is None and "some indices declared, some free" in skipped[0][1]


def test_a_hole_clause_of_the_given_is_left_out_when_no_conclusion_needs_it(tmp_path):
    """a part of the given with a hole is left out of an item that uses no name it mentions (other than names a
    formal clause of the given declares): the compiled statement has fewer hypotheses, so it is stronger than the
    paper's, and the docstrings and the status page say so; a conclusion that uses such a name keeps the item a hole"""
    _t, stmt, skipped = _given_statement(r"k\in\N,\ v\in\Q,\ \bd\in\Q^k;\ \text{(H2) at}\ v:=t^*;\ \beta'_0:=\min_h|\delta_h|",
                                         r"v\ge v")
    assert stmt is not None and "t" not in stmt.split(",")[-1]
    assert qpp2lean.STMT_DROPPED == [r"\text{(H2) at}\ v:=t^*"]
    _t, stmt, skipped = _given_statement(r"k\in\N;\ \text{(H2) at}\ v:=t^*", r"v\ge0")
    assert stmt is None and skipped[0][1] == "item given has a hole that mentions v, which a conclusion uses"
    _t, stmt, skipped = _given_statement(r"k\in\N,\ y\in\Q;\ \bd\in\Q^k\ \text{a chamber}", r"\textstyle\sum_h\delta_h\le y")
    assert stmt is None and "mentions delta" in skipped[0][1]
    q = ("paper X\nlemma lem:m\n  given: x in QQ; ?{\\text{(H1) at}\\ v}\n  (1): x <= x\n")
    refs = {"lem:m": [("m_one", "(1)", "theorem", "S.lean")]}
    lean, spans, skipped = qpp2lean.generate_match(q, refs, [])
    assert [t for t, _, _ in spans] == ["lem:m"] and qpp2lean.LAST_DROPPED == {"lem:m": [r"\text{(H1) at}\ v"]}
    assert "without the given clauses with a hole (a stronger statement): \\text{(H1) at}\\ v -/" in lean


def test_a_given_clause_that_does_not_compile_is_left_out_like_a_hole():
    """a formal clause on names declared nowhere (p = 1) and a definition the printer cannot read (s := delta_1, a
    numbered member of a vector) are left out of a conclusion that uses none of their names, and listed; a
    conclusion that uses such a name keeps the reason"""
    given = r"p=1;\ k\in\N_{\ge2};\ \bd\in\Q^k;\ \text{(H2) at}\ t^*;\ s:=\delta_1"
    _t, stmt, skipped = _given_statement(given, r"x\in\Q_{\ge0},\ 3x\ge1:\ x\ge\tfrac13")
    assert stmt is not None and "p" not in stmt.split(":")[0] and "(h\u2081 : 2 \u2264 k)" in stmt
    assert qpp2lean.STMT_DROPPED == [r"\text{(H2) at}\ t^*", "p = 1", "s := delta_1"]
    _t, stmt, skipped = _given_statement(given, r"p\ge1")
    assert stmt is None and skipped[0][1] == "undeclared ['p']"
    # the index of a family definition is bound by it: a conclusion with its own index h is not blocked
    _t, stmt, skipped = _given_statement(r"k\in\N_{\ge2},\ \bd\in\Q^k;\ u_h:=\delta_h-\delta_1",
                                         r"\textstyle\sum_{h\le k}\delta_h\le\textstyle\sum_{h\le k}\delta_h")
    assert stmt is not None and qpp2lean.STMT_DROPPED == ["u_(h) := delta_(h) - delta_1"]


def test_a_shared_index_without_a_range_is_warned_and_fix_keys_may_hold_spaces():
    """an index free in a hypothesis and its conclusion, of no family with a range, reads 'for every u in N' (a
    stronger statement than a range would give): a warning; a recurrence W_(i+1) = f(W_(i)) of the given is not one.
    A fix line keeps a key with a space (core 0)"""
    _t, stmt, _s = _given_statement(r"x\in\Q,\ a_i\in\Q", r"a_u\le x\Rightarrow a_u\le x+1")
    assert "\u2200 u : \u2115, (a u \u2264 x) \u2192 a u \u2264 x + 1" in stmt
    assert [w for _, w in qpp2lean.LAST_WARNINGS] == [
        "the index u is free in a hypothesis and in its conclusion and no family gives its range, so it reads "
        "'for every u in N' (declare it, or write the range)"]
    _t, stmt, _s = _given_statement(r"C\in\N,\ W_i\in\N;\ W_0=C,\ W_{i+1}=2W_i+C", r"W_1\ge W_0")
    assert "\u2200 i : \u2115, W (i + 1) = 2 * W i + C" in stmt and qpp2lean.LAST_WARNINGS == []
    src = r"\begin{lemma}\label{lem:t}\begin{stmt}\sit{given}{x\in\Q}\sit{core 0}{x\le x}\FIX{t.c0}\end{stmt}\end{lemma}"
    text, _ = latex2qpp.convert(src, "T")
    assert "  fix core 0 t.c0\n" in text and qpp2lean.read_qpp(text)["results"][0]["fixes"] == [("core 0", "t.c0")]


def test_core_items_stand_alone():
    """a core item (core, core0, core 1) declares its names before its colon: it is read without the given of its
    result, so a clause of the given in words does not block it and a given that compiles adds no hypothesis; a
    function may be defined before its colon; a name it does not declare is reported as such"""
    given = r"k\in\N_{\ge1},\ m:=k+1,\ \text{a prose clause on}\ k"
    src = (r"\begin{lemma}\label{lem:c}x\begin{stmt}\sit{given}{%s}\sit{(1)}{\text{prose}}"
           r"\sit{core}{k\in\N_{\ge1}:\ k+1\ge2}\sit{core1}{y\in\Q,\ \rho(t):=t^2+1:\ \rho(y)>0}"
           r"\sit{core 2}{m\ge2}\end{stmt}\end{lemma}" % given)
    text, _ = latex2qpp.convert(src, "T")
    q = qpp2lean.read_qpp(text)
    got = {k: (st[2][0][1] if st else why) for k, st, why in qpp2lean.item_results(q["results"][0], q["vocab"] or None)}
    assert got["core"] == "\u2200 (k : \u2115), (1 \u2264 k) \u2192 k + 1 \u2265 2"
    assert got["core1"] == "\u2200 (y : \u211a) (\u03c1 : \u211a \u2192 \u211a), (\u2200 (t : \u211a), \u03c1 t = t ^ 2 + 1) \u2192 \u03c1 y > 0"
    assert got["core 2"].startswith("undeclared ['m'] (a core item stands alone")
    assert got["(1)"] == "item (1) has a hole"
    assert [qpp2lean.is_core(k) for k in ("core", "core0", "core 12", "cores", "(core)")] == [True, True, True, False, False]
    # a given that compiles adds nothing to a core item
    _t, stmt, _s = _given_statement(r"k,n\in\N,\ n\ge1", r"k\le k")
    assert "(h\u2081 : n \u2265 1)" in stmt
    src2 = r"\begin{lemma}\label{lem:d}x\begin{stmt}\sit{given}{k,n\in\N,\ n\ge1}\sit{core}{k\in\N:\ k\le k}\end{stmt}\end{lemma}"
    text2, _ = latex2qpp.convert(src2, "T")
    lean, _m, _s = qpp2lean.generate(text2)
    assert "  \u2200 (k : \u2115), k \u2264 k" in lean.splitlines()


def test_positive_part_of_a_name_and_a_quantifier_index_without_a_lower_bound():
    """(y)_+ is the positive part of y, as (y - t)_+ is; an index of no family bound only above (for i <= D) runs
    from 0 in Lean: a warning"""
    assert T.to_qpp(T.parse_tex(r"(y)_+\ge0")) == "max(y, 0) >= 0" and T.to_qpp(T.parse_tex(r"e_+")) == "e_plus"
    for item, warned in ((r"c\cdot i\ge0\ \text{for}\ i\le D", True), (r"c\cdot i\ge0\ \text{for}\ 1\le i\le D", False),
                         (r"x_i\ge0\ \text{for}\ i\le D", False)):
        _t, stmt, _s = _given_statement(r"D\in\N,\ c\in\Q,\ x_1,\dots,x_D\in\Q", item)
        assert stmt is not None
        assert bool(qpp2lean.LAST_WARNINGS) == warned, (item, qpp2lean.LAST_WARNINGS)


def test_only_registered_cited_facts_are_hypotheses_of_a_match(tmp_path):
    """a structure X : Prop with no parameters is a cited fact only when its docstring carries a fact: tag or the
    tag of the table of facts; any other one (here a false proposition) is no hypothesis of the match example, so a
    declaration that takes it cannot be matched through it, and it is reported"""
    from qpp import leanrefs
    (tmp_path / "F.lean").write_text(
        "namespace P\n"
        "/-- [p:tab:facts] Motzkin and Straus 1965, a row of the table of facts. -/\nstructure MS : Prop where\n  h : True\n"
        "/-- [p:lem:m] A proposition of the library, not a cited fact. -/\nstructure Bad : Prop where\n  h : False\n"
        "/-- [p:lem:m] (sums) uses both. -/\ntheorem m_sums (hMS : MS) (hB : Bad) (x y : Nat) : x \u2264 y + x := by omega\n"
        "end P\n", encoding="utf-8")
    assert leanrefs.cited_premises(tmp_path) == {"P.m_sums": ["P.MS"]}
    assert leanrefs.unregistered_facts(tmp_path) == [("P.Bad", "F.lean")]
    assert leanrefs.registers_fact(" [first:prop:lower] [first:fact:cliques] Motzkin and Straus.")
    assert not leanrefs.registers_fact(" [first:prop:lower] Motzkin and Straus (`tab:facts`, Cliques).")


def test_status_page_says_when_a_match_covers_only_a_core(tmp_path):
    """a label matched only through its core items (they stand alone, without the given) is marked core only, so
    the page does not count it as a matched statement of the result"""
    from qpp import status
    (tmp_path / "p" / "latex").mkdir(parents=True)
    (tmp_path / "p" / "lean" / "P").mkdir(parents=True)
    (tmp_path / "p" / "latex" / "p.tex").write_text(
        "\\begin{lemma}\\label{lem:a}x\\begin{stmt}\\sit{given}{x\\in\\Q,\\ \\text{in words}}\\sit{(1)}{\\text{words}}"
        "\\sit{core}{x\\in\\Q:\\ x\\le x}\\end{stmt}\\end{lemma}\n"
        "\\begin{lemma}\\label{lem:b}x\\begin{stmt}\\sit{given}{x\\in\\Q}\\sit{(1)}{x\\le x}"
        "\\sit{core}{y\\in\\Q:\\ y\\le y}\\end{stmt}\\end{lemma}\n", encoding="utf-8")
    (tmp_path / "p" / "lean" / "P" / "A.lean").write_text(
        "/-- [p:lem:a] (core) The core. -/\ntheorem a (x : Rat) : x \u2264 x := le_refl x\n"
        "/-- [p:lem:b] The lemma. -/\ntheorem b (x : Rat) : x \u2264 x := le_refl x\n", encoding="utf-8")
    text = status.page("p", tmp_path)
    assert "| `lem:a` | lemma | formalized | 1 | (core) | 1 (core only) | - | `a` |" in text
    assert "| `lem:b` | lemma | formalized | 1 | - | 1 | - | `b` |" in text
    assert "Labels with a compiled statement to match: 2 (of which 1 by a core item only)" in text



def test_a_template_in_words_keeps_its_words_in_the_extract():
    """a template of a templates row has no formula: its alias line carries its words as a hole"""
    src = (r"\begin{definition}\label{def:t}x\begin{stmt}\sit{templates}{\Pt6:\ \text{a two-sided bound};\ "
           r"\Pt7[(\mathrm X){:=}E]:\ \text{each condition discharged by}\ E}\end{stmt}\end{definition}")
    text, _ = latex2qpp.convert(src, "T")
    assert "alias P6 := ?{\\text{a two-sided bound}}\n" in text
    assert "alias P7 := ?{\\text{each condition discharged by}\\ E}\n" in text



def test_status_page_checks_each_registered_fact_against_the_latex():
    """a structure registered as a cited fact is backed by the LaTeX when its fact: tag labels a fact environment
    that cites a reference, or when its tab:facts tag comes with the name of a cited row of the table of facts"""
    from qpp import status
    tex = ("\\begin{fact}[a]\\label{fact:a}x \\cite{A}\\end{fact}\n\\begin{fact}[b]\\label{fact:b}elementary\\end{fact}\n"
           "\\begin{tabular}{llll}\\hline\nname & fact & reference & used in\\\\\n\\hline\n"
           "Cliques & Motzkin and Straus & \\cite{MS1965} & here\\\\\nFolk & a folklore bound & elementary & here\\\\\n"
           "\\hline\n\\end{tabular}\n")
    envs, rows = status.fact_sources(tex)
    assert envs == {"fact:a": True, "fact:b": False} and rows == {"Cliques": True, "Folk": False}
    reg = lambda tags, doc: status.registration(tags, doc, envs, rows)
    assert reg(["fact:a"], "") == ("fact:a", True)
    assert reg(["fact:b"], "") == ("fact:b: no citation", False)
    assert reg(["fact:c"], "") == ("fact:c: no fact environment", False)
    assert reg(["prop:lower", "tab:facts"], "Motzkin and Straus (Cliques).") == ("tab:facts row Cliques", True)
    assert reg(["tab:facts"], "Motzkin and Straus.") == ("tab:facts: names no row", False)
    assert reg(["tab:facts"], "the Folk bound") == ("tab:facts row Folk: no citation", False)
    assert reg(["lem:x"], "") == ("-", True)
