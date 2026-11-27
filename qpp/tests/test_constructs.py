"""The constructs of the statement layer (qpp/README.md, "The LaTeX form"): for each, its Q++ spelling, the canonical
LaTeX printed back (the same Q++ when read again), and its Lean reading, on a short fixture. fixtures/constructs.tex
holds lines that use them, and latex2qpp generates fixtures/constructs.qpp from it."""
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1]))
from qpp import latex2qpp, modules, qpp2latex, qpp2lean, source  # noqa: E402
from qpp import texmath as T  # noqa: E402


def item(tex, scalars=(), functions=()):
    """the Q++ of a statement item read with the scope on (names before a parenthesis by their declarations), and
    whether it reads back the same; a hole raises"""
    T.SCOPED[0] = True
    T.SCALARS.clear()
    T.SCALARS.update(scalars)
    T.ELSEWHERE.clear()
    try:
        parts, _ = T.parse_stmt(tex, functions)
        r = T.stmt_round_trip(tex, functions)
        return T.stmt_print(parts, T.to_qpp), r[1]
    finally:
        T.SCOPED[0] = False
        T.SCALARS.clear()


def hole(tex, scalars=(), functions=()):
    with pytest.raises(T.Hole):
        item(tex, scalars, functions)


# ------------------------------------------------------------- a name before a parenthesis reads by its scope

def test_a_mark_is_part_of_the_name_and_a_parenthesis_reads_by_its_scope():
    """Y^+_R, f^*, a^0, w^\\circ, g^\\prime: a superscript that is no power is part of the name, before or after the
    subscript (Y_R^+ is Y^+_R); before a parenthesis the name reads by its scope like any other: an application if
    it is a function, a product if it is a number, a hole otherwise (never Y^+(x) as a product)"""
    assert item(r"Y^+_R\subseteq O") == ("Y_pos_(R) subseteq O", True)
    assert item(r"Y_R^+\subseteq O")[0] == "Y_pos_(R) subseteq O"
    assert item(r"\rho^*_i>0") == ("rho_star_(i) > 0", True)
    assert item(r"a^0_h=1") == ("a_nought_(h) = 1", True)
    hole(r"Y^+(\bx)\subseteq O")
    hole(r"a^0(x)=1")
    assert item(r"Y^+_R(\bx)\subseteq O", functions={"Y_pos_"}) == ("Y_pos_(R)(b_x) subseteq O", True)
    assert item(r"a^*(y+1)=0", scalars={"a_star"}) == ("a_star * (y + 1) = 0", True)
    # a function letter stays one with a mark or a prime
    assert item(r"f^*(x)\ge0") == ("f_star(x) >= 0", True)
    assert item(r"g^\prime(x)=0")[0] == "g'(x) = 0"
    # the declarations of a paper key the marked names as the term layer does
    assert latex2qpp.scalars_of(r"a^*,\vartheta,y\in\Q") == {"a_star", "vartheta", "y"}
    assert latex2qpp.scalars_of(r"\rho^*_i\in\Q") == {"rho_star_"}
    assert latex2qpp.functions_of(r"Y^+_R\colon X^+_R\to\Q,\ g_R^0(t):=2") == {"Y_pos_", "g_nought_"}


def test_an_inverse_before_a_parenthesis_and_names_side_by_side_in_a_subscript():
    """\\pi^{-1}(h) is the inverse map at h, never pi^(-1) * h; x^2(y+1) is a product.
    Letters side by side in a subscript are one index each (sigma_{mm'} as M_{ij}); names with their own subscripts
    side by side (T_{u_{a-1}mu_a}, V_{\\varphi\\one_O}) are a hole: indices with commas, a product with \\cdot"""
    hole(r"\pi^{-1}(h)<j")
    assert item(r"\pi^{-1}(h)<j", scalars={"pi"}) == ("pi^(-1) * h < j", True)
    assert item(r"x^2(y+1)>0") == ("x^2 * (y + 1) > 0", True)
    assert item(r"\sigma_{mm'}=1") == ("sigma_(m, m') = 1", True)
    assert item(r"M_{\alpha\beta}=1")[0] == "M_(alpha, beta) = 1"
    assert item(r"a_{2i}=1")[0] == "a_(2 * i) = 1"
    hole(r"T_{u_{a-1}mu_a}(\bx)=0")
    assert item(r"T_{u_{a-1},m,u_a}=0") == ("T_(u_(a - 1), m, u_(a)) = 0", True)


def test_the_check_counts_an_application_read_as_a_product(tmp_path):
    """the check of latex2qpp --check: a product of a name and a parenthesis whose name the scope does not declare a
    number is counted (none on a paper, as the scoped reading makes it a hole); without the scope it would be read"""
    T.SCOPED[0] = False
    T.JUXT.clear()
    try:
        T.parse_stmt(r"\ell(\bv)>0")
    finally:
        T.SCOPED[0] = True
    assert T.JUXT == [("l", False)]
    rep = {"items": [{"misread": ["l"]}], "lines": []}
    assert latex2qpp.misread(rep) == 1
    # the Q++ modules printed in full as one paper (qpp.modules.whole)
    whole = tmp_path / "modules.qpp"
    whole.write_text(modules.whole(HERE.parents[1]), encoding="utf-8")
    tex, _bib = qpp2latex.generate(source.read_file(whole), full=True)
    _text, report = latex2qpp.convert(tex, "modules")
    assert latex2qpp.summary(report)["misread"] == 0


def test_times_is_the_cartesian_product():
    """\\times is the cartesian product of sets (Q++ times, Lean the set product), never a product of numbers"""
    assert item(r"O':=O\times(0,\rho]") == ("O' := O times (0, rho]", True)
    assert item(r"A\in\Z^{m\times k}") == ("A in ZZ^(m times k)", True)
    assert T.to_lean(T.parse_qpp("A times B")) == "A \u00d7\u02e2 B"


# ------------------------------------------------------------- quantifiers in words and binders by relations

def test_a_quantifier_in_words_after_its_claim():
    assert item(r"x\ge0\ \text{for every}\ x\in S", scalars=("x",)) == ("forall x in S : x >= 0", True)
    assert item(r"x\ge0\ \text{for all}\ x\in S", scalars=("x",)) == ("forall x in S : x >= 0", True)
    assert item(r"x\ge0\ \text{for some}\ x\in S", scalars=("x",)) == ("exists x in S : x >= 0", True)


def test_a_binder_by_a_relation_and_where():
    assert item(r"\forall i\le n:\ x_i\ge0") == ("forall i : i <= n => x_(i) >= 0", True)
    assert item(r"\exists Z\subseteq O:\ Z\ne\varnothing") == ("exists Z : Z subseteq O, Z != empty", True)
    # a chain: the binder is the first name of the chain, every link a condition
    assert item(r"x\ge0\ \text{for every}\ \varnothing\ne S\subseteq\{1,\dots,k\}", scalars=("x",)) == (
        "forall S : empty != S subseteq {1..k} => x >= 0", True)
    assert item(r"f\ge0\ \text{where}\ x\ge1", scalars=("f", "x")) == ("f >= 0 on {x >= 1}", True)


def lean_of(given, *items, pre=""):
    """the Lean statement of a lemma with the given and the items (key, LaTeX), and the reasons of the file for what it
    does not state (latex2qpp then qpp2lean, as for a paper)"""
    rows = "".join(r"\sit{%s}{%s}" % kv for kv in ((("given", given),) if given else ()) + items)
    src = pre + r"\begin{lemma}\label{lem:t}\begin{stmt}" + rows + r"\end{stmt}\end{lemma}"
    text, rep = latex2qpp.convert(src, "T")
    assert all(it["formal"] and it["same"] for it in rep["items"]), [(it["tex"], it["qpp"]) for it in rep["items"]
                                                                       if not (it["formal"] and it["same"])]
    lean, _made, skipped = qpp2lean.generate(text)
    stated = [ln.strip() for ln in lean.splitlines() if ln.startswith("  \u2200") or ln.startswith("  (")]
    return " ".join(stated), " ".join(why for _lab, why in skipped)


# ------------------------------------------------------------- the connectives of the clause grammar

def test_then_so_within():
    """\\text{if}\\ H,\\ \\text{then}\\ C is H => C; \\text{so} is a conjunction (both claims kept, an arrow would drop
    the first); a\\ \\text{within}\\ W\\ \\text{of}\\ b is |a - b| <= W"""
    assert item(r"\text{if}\ x>0,\ \text{then}\ y>0", scalars=("x", "y")) == ("x > 0 => y > 0", True)
    assert item(r"x,y\in\Q,\ \text{if}\ x>0,\ \text{then}\ y>0") == ("x, y in QQ, (x > 0 => y > 0)", True)
    assert item(r"x>0\ \text{so}\ y>0", scalars=("x", "y")) == ("x > 0, y > 0", True)
    assert item(r"y\ \text{within}\ 2^{-s-5}\ \text{of}\ c", scalars=("y", "s", "c")) == ("|y - c| <= 2^(-s - 5)", True)
    hole(r"\text{if}\ x>0", scalars=("x",))
    lean, _ = lean_of(r"y,c\in\Q,\ s\in\Z", ("(1)", r"y\ \text{within}\ 2^{-s}\ \text{of}\ c\Rightarrow y\le c+2^{-s}"))
    assert "(|y - c| \u2264 (2 : \u211a) ^ (-s)) \u2192 y \u2264 c + (2 : \u211a) ^ (-s)" in lean


def test_negation_at_near():
    """\\neg(P) is not(P); P\\ \\text{at}\\ p is P with its functions at p; P\\ \\text{near}\\ p (one reading) is
    some box with p in its interior and P on it, the interior the product of the open intervals (no topology)"""
    assert item(r"\neg(x\ge0)", scalars=("x",)) == ("not(x >= 0)", True)
    assert item(r"f\ge0\ \text{at}\ p", scalars=("p",)) == ("f >= 0 at p", True)
    assert item(r"f\ge0\ \text{near}\ p", scalars=("p",)) == ("f >= 0 near p", True)
    assert T.to_lean(T.parse_qpp("not(x >= 0)")) == "\u00ac(x \u2265 0)"
    lean, _ = lean_of(r"K\colon\Q\to\Q,\ p\in\Q", ("(1)", r"K\ge0\ \text{at}\ p"), ("(2)", r"K\ge0\ \text{near}\ p"))
    assert "(K p \u2265 0) \u2227 (\u2203 a b : \u211a, a < p \u2227 p < b \u2227 \u2200 w : \u211a, a \u2264 w \u2192 w \u2264 b \u2192 K w \u2265 0)" in lean
    lean, _ = lean_of(r"n\in\N,\ K\colon\Q^n\to\Q,\ \bp\in\Q^n", ("(1)", r"K\ge0\ \text{near}\ \bp"))
    assert "\u2203 a b : Fin n \u2192 \u211a, (\u2200 i, a i < p i \u2227 p i < b i) \u2227 \u2200 w : Fin n \u2192 \u211a, (\u2200 i, a i \u2264 w i \u2227 w i \u2264 b i) \u2192 K w \u2265 0" in lean


def test_else_and_otherwise_are_the_complementary_case():
    """x:=t\\ (H),\\ y:=u\\ (\\text{else}) is H => x := t, not(H) => y := u; an index of H the case does not use is
    bound by exists inside the negation; Lean gives each case as a hypothesis on its name"""
    assert item(r"e_i:=h_i\ (h_i\ge0),\ \sigma_i:=-h_i\ (\text{else})") == (
        "(h_(i) >= 0 => e_(i) := h_(i)), (not(h_(i) >= 0) => sigma_(i) := -h_(i))", True)
    assert item(r"a_v:=b_j\ (v=t_j),\ a_v:=0\ \text{otherwise}")[0] == (
        "(v = t_(j) => a_(v) := b_(j)), (not(exists j : v = t_(j)) => a_(v) := 0)")
    hole(r"x:=1\ \text{otherwise}")
    lean, _ = lean_of(r"x\in\Q,\ y:=x\ (x\ge0),\ y:=-x\ (\text{else})", ("(1)", r"y\ge0"))
    assert "(h\u2081 : (x \u2265 0) \u2192 y = x) (h\u2082 : (\u00ac(x \u2265 0)) \u2192 y = -x)" in lean


# ------------------------------------------------------------- the constructs of the statement layer

def test_star_names_set_bounds_and_nested_binders():
    """O_* is a name of its own (O_ast, not O^* = O_star); \\Z_{\\ge M_0} is Z from a bound that is a term; a visible
    space after a comma starts the next group of a binder; a binder with no set is a count only when it is an index"""
    assert item(r"O_*\subseteq O,\ v_*\ne v^*", scalars=("v_ast", "v_star")) == ("O_ast subseteq O, v_ast != v_star", True)
    assert item(r"\forall M\in\Z_{\ge M_0},\ L\ge1:\ M\ge L") == ("forall M in ZZ_(>= M_0) : forall L : L >= 1 => M >= L",
                                                                  True)
    assert item(r"\forall\bx,s,\ V\in P:\ s\ge0")[0] == "forall b_x, s : forall V in P : s >= 0"
    assert item(r"\exists O_*=\textstyle\prod_i(0,\rho^*_i]\subseteq O,\ c,C,M_0\ \forall M\in\Z_{\ge M_0},\ L\ge1\ "
                r"\exists Z=Z_{M,L}\subseteq O_*:\ Z\ne\varnothing")[1]
    _, why = lean_of("", ("(1)", r"\exists c,C\ \forall M\in\Z:\ c\le C"))
    assert "the binder c has no set" in why


def test_filtered_sums_unions_and_point_sets():
    """\\sum_{x\\in X,\\ P}t and \\sum\\{t:\\ x\\in X,\\ P\\} are one sum (Lean finsum); \\bigcup over a family or a builder
    (one binder per name), \\bigcup U; {P} with the functions of P is the set of the points where P holds"""
    fs = {"a", "a_", "Y_", "l_"}
    assert item(r"\textstyle\sum\{2^{-\ell_R(\bx)}:\ \bx\in X_R,\ a(\bx)\ge L\}\le1", functions=fs) == (
        "(sum b_x in X_(R) with a(b_x) >= L, 2^(-l_(R)(b_x))) <= 1", True)
    assert item(r"\textstyle\sum_{\bx\in X_R,\ a(\bx)\ge L}2^{-\ell_R(\bx)}\le1", functions=fs)[0] == (
        "(sum b_x in X_(R) with a(b_x) >= L, 2^(-l_(R)(b_x))) <= 1")
    assert item(r"Z\cup\bigcup\{Y_R(\bx):\ R\in\Pi,\ \bx\in X_R,\ a_R(\bx)\ge L\}\subseteq O", functions=fs) == (
        "Z cup (union R in Pi, (union b_x in X_(R) with a_(R)(b_x) >= L, Y_(R)(b_x))) subseteq O", True)
    assert item(r"B\subseteq\textstyle\bigcup\mathfrak F") == ("B subseteq sunion(frak_F)", True)
    lean, _ = lean_of(r"n\in\N,\ X\subseteq\Q^n,\ K\colon\Q^n\to\Q,\ L\in\Z,\ Z\subseteq\Q^n",
                      ("(1)", r"\{K\le2^{-L}\}\subseteq Z\cup\textstyle\bigcup_{\bx\in X}\{\bx\}"),
                      ("(2)", r"\textstyle\sum_{\bx\in X,\ K(\bx)\ge0}K(\bx)\ge0"))
    assert "{w | K w \u2264 (2 : \u211a) ^ (-L)} \u2286 Z \u222a (\u22c3 x \u2208 X, {x})" in lean
    assert "\u2211\u1da0 (x) (_ : x \u2208 X) (_ : K x \u2265 0), K x" in lean


def test_polynomial_operators():
    """\\deg_yS, \\mathrm{lc}_y(S), \\mathrm{Res}_y(S,T) (an operator with its variable below), \\partial^k_yg (Q++
    deriv(g, y, k), applied when a parenthesis follows), S(\\bw,\\cdot) (a blank), \\Q^\\times, \\tfrac1N\\Z; Lean on
    Polynomial Q and Polynomial (MvPolynomial (Fin d) Q)"""
    assert item(r"\deg_yS=n") == ("deg_(y)(S) = n", True)
    assert item(r"\mathrm{Res}_y(S,T)\ne0") == ("Res_(y)(S, T) != 0", True)
    assert item(r"|\partial^l_yg(p,y)|\le1") == ("|deriv(g, y, l)(p, y)| <= 1", True)
    assert item(r"S(\bw,\cdot)\ne0") == ("S(b_w, dot) != 0", True)
    assert item(r"V\in\mathrm{Pat}_\delta(\bx)") == ("V in Pat_(delta)(b_x)", True)
    assert item(r"r\in\Q^\times,\ e\in\tfrac1N\Z") == ("r in nonzero(QQ), e in 1 / N * ZZ", True)
    lean, _ = lean_of(r"S\in\Q[y],\ t\in\Q", ("(1)", r"\deg_yS\ge1\Rightarrow\partial_yS(t)\ne\mathrm{lc}_y(S)"))
    assert "(S.natDegree \u2265 1) \u2192 (Polynomial.derivative S).eval t \u2260 S.leadingCoeff" in lean
    lean, _ = lean_of(r"d,l\in\N,\ \bp,\bw\in\Q^d,\ g\in\Q[\bw][y],\ u\in\Q",
                      ("(1)", r"\partial^l_yg(\bp,u)=0\Rightarrow\deg_y(g(\bp,\cdot))\le\deg_yg"))
    assert "(g : Polynomial (MvPolynomial (Fin d) \u211a))" in lean
    assert ("Polynomial.eval\u2082 (MvPolynomial.eval p) u (Polynomial.derivative^[l] g) = 0) \u2192 "
            "(Polynomial.map (MvPolynomial.eval p) g).natDegree \u2264 g.natDegree") in lean
    lean, _ = lean_of(r"N\in\Z_{\ge1},\ r\in\Q^\times,\ e\in\tfrac1N\Z", ("(1)", r"r\ne0"))
    assert "(h\u2082 : r \u2260 0) (h\u2083 : \u2203 n : \u2124, e = (1 / N : \u211a) * n)" in lean


def test_chains_with_dots_and_signs():
    """a_lo op \\dots op a_hi is the links over the range; another relation after it holds for every member;
    \\sigma=\\pm is sigma in {1, -1}"""
    assert item(r"W_0<\dots<W_{m+1}") == ("forall i : 0 <= i < m + 1 => W_(i) < W_(i + 1)", True)
    assert item(r"I_1<\dots<I_k\subseteq I_0") == (
        "(forall i : 1 <= i < k => I_(i) < I_(i + 1)), forall i : 1 <= i <= k => I_(i) subseteq I_0", True)
    assert item(r"\sigma_i=\pm\ (h_i\ne0)") == ("h_(i) != 0 => sigma_(i) in {1, -1}", True)
    hole(r"a<\dots<b<\dots<c")


def test_restriction_interior_and_set_operators():
    """h|_F=0 is h = 0 on F (restrict(h, F) as a term); \\mathring B the interior (of an interval in Lean: the open
    interval); \\dim F the dimension of the affine hull; \\mathcal P(S) the subsets of S"""
    assert item(r"h_i|_F=0") == ("restrict(h_(i), F) = 0", True)
    assert item(r"x\in\mathring B") == ("x in interior(B)", True)
    assert item(r"T\subseteq\mathcal P(\{0,\dots,k\})") == ("T subseteq powerset({0..k})", True)
    lean, _ = lean_of(r"n\in\N,\ F\subseteq\Q^n,\ h\colon\Q^n\to\Q,\ x,a,b\in\Q",
                      ("(1)", r"h|_F=0\Rightarrow\dim F\le n"), ("(2)", r"x\in\mathring{[a,b]}\Rightarrow x>a"))
    assert "(\u2200 w : Fin n \u2192 \u211a, w \u2208 F \u2192 h w = 0) \u2192 Module.finrank \u211a (vectorSpan \u211a F) \u2264 n" in lean
    assert "(a < x) \u2192 (x < b) \u2192 x > a" in lean


def test_asymptotic_notation_and_references():
    """O(...) is a hole with its reason; \\cref{lem:x}(k) is a proposition, \\cref{def:law}(H3)[t,\\eta] with the values
    of the free names of the condition; Lean lists them with the reason"""
    with pytest.raises(T.Hole, match="asymptotic"):
        item(r"N\le O(2^n)", scalars=("N", "n"))
    assert item(r"x>0,\ \cref{lem:x}(2)\Rightarrow y>0") == ("x > 0, @lem:x(2) => y > 0", True)
    assert item(r"\cref{def:law}(H3)[t^*,\eta]") == ("@def:law(H3)[t_star, eta]", True)
    _, why = lean_of(r"t\in\Q", ("(1)", r"\cref{def:law}(H3)[t]\Rightarrow t=t"))
    assert "the reference @def:law(H3) as a hypothesis" in why


def test_maps_by_juxtaposition_and_composition():
    """a map declared with \\colon is applied by juxtaposition (\\pi_\\phi\\bxi), never multiplied; g\\circ\\pi composes"""
    T.MAPS.add("pi_(phi)")
    try:
        assert item(r"\pi_\phi\bxi=\bx", functions={"pi_"}) == ("pi_(phi)(b_xi) = b_x", True)
    finally:
        T.MAPS.discard("pi_(phi)")
    assert item(r"\ell_\phi:=\ell_R\circ\pi_\phi+\sigma_\phi") == ("l_(phi) := l_(R) comp pi_(phi) + sigma_(phi)", True)
    lean, _ = lean_of(r"k,m\in\N,\ \pi\colon\Q^k\to\Q^m,\ \ell\colon\Q^m\to\Q,\ \bxi\in\Q^k,\ \bx\in\Q^m",
                      ("(1)", r"\pi\bxi=\bx\Rightarrow(\ell\circ\pi)(\bxi)=\ell(\bx)"))
    assert "(\u03c0 \u03be = x) \u2192 (l \u2218 \u03c0) \u03be = l x" in lean


def test_scaled_intervals_the_least_attained_and_tuples():
    """u[a,b] is [a,b]u (Lean the image of the interval); m:=\\min S,\\ \\text{attained} (the least element, a member);
    (|f|)_{f\\in\\mathcal J} the tuple of the values over a set"""
    assert item(r"B\subseteq2^{-z}[2^{-D},2]") == ("B subseteq [2^(-D), 2]*2^(-z)", True)
    assert item(r"\lambda=\min\{\ell_R(\bx):\bx\in S\},\ \text{attained}", functions={"l_"}) == (
        "lambda = (min {l_(R)(b_x) : b_x in S}) attained", True)
    assert item(r"K\asymp P((|f|)_{f\in\mathcal J})") == ("K asymp P(tuple f in cal_J, |f|)", True)
    lean, _ = lean_of(r"S\subseteq\Z,\ \lambda\in\Z,\ \lambda=\min\{x:\ x\in S\},\ \text{attained}", ("(1)", r"\lambda\in S"))
    assert "lam \u2208 S" in lean


def test_vocabulary_rows():
    """a unary and a relational word by rows (a source adds the rows where the notions are
    defined): expanded where they are used"""
    pre = (r"\begin{definition}\label{def:w}\begin{stmt}\sit{feasible}{R\subseteq\Q:\ R\ \text{feasible}:\iff "
           r"R\ne\varnothing}\sit{child}{N,N'\subseteq\Q:\ N'\ \text{a child of}\ N:\iff N'\subseteq N}\end{stmt}"
           r"\end{definition}")
    lean, _ = lean_of(r"A,A'\subseteq\Q", ("(1)", r"A\ \text{feasible},\ A'\ \text{a child of}\ A\Rightarrow A\ \text{feasible}"),
                      pre=pre)
    assert "(A \u2260 \u2205) \u2192 (A' \u2286 A) \u2192 A \u2260 \u2205" in lean


def test_worked_examples_of_context_rows_and_vocabulary_rows():
    """a context row and a vocabulary row (the domain of K, a unary word), and another pair (the size of the model,
    a relational word); a statement that uses a name of the context
    reads the row whole, first, and a word is replaced by its row"""
    pre = (r"\begin{definition}\label{def:r}\begin{stmt}\sit{context}{d\in\Z_{\ge1},\ O\subseteq\Q^d,\ K\colon\Q^d\to"
           r"\Q,\ K\ge0\ \text{on}\ O}\sit{feasible}{n\in\N,\ S\subseteq\Q^n:\ S\ \text{feasible}:\iff S\ne\varnothing}"
           r"\end{stmt}\end{definition}")
    lean, _ = lean_of("", ("(1)", r"L\in\Z_{\ge1},\ \{K\le2^{-L}\}\ \text{feasible}\Rightarrow\{K\le2^{-L}\}\ne\varnothing"),
                      pre=pre)
    assert lean.startswith("\u2200 (d : \u2124) (O : Set (Fin d.toNat \u2192 \u211a)) (K : (Fin d.toNat \u2192 \u211a) \u2192 \u211a) (h\u2081 : 1 \u2264 d)")
    assert "({w | K w \u2264 (2 : \u211a) ^ (-L)} \u2260 \u2205) \u2192 {w | K w \u2264 (2 : \u211a) ^ (-L)} \u2260 \u2205" in lean
    pre = (r"\begin{definition}\label{def:l}\begin{stmt}\sit{context}{k\in\Z_{\ge1},\ a^*\in\Q,\ a^*\ne0}\sit{child}{N,N'"
           r"\subseteq\Z:\ N'\ \text{a child of}\ N:\iff N'\subseteq N,\ N'\ne N}\end{stmt}\end{definition}")
    lean, _ = lean_of("", ("(1)", r"N,N'\subseteq\{0,\dots,k\},\ N'\ \text{a child of}\ N\Rightarrow N'\subseteq N"),
                      pre=pre)
    assert "(k : \u2124) (a_star : \u211a) (h\u2081 : 1 \u2264 k) (h\u2082 : a_star \u2260 0)" in lean
    assert "((N' \u2286 N) \u2227 (N' \u2260 N)) \u2192 N' \u2286 N" in lean


def test_the_counting_convention():
    """the statement items of a paper: the rows whose key is not origin, classical, reference or names; a result is
    fully compiled when every one of them is formal and same"""
    src = (r"\begin{lemma}\label{lem:c}\begin{stmt}\sit{given}{x\in\Q}\sit{(1)}{x^2\ge0}\sit{origin}{\text{classical}}"
           r"\end{stmt}\end{lemma}\begin{lemma}\label{lem:d}\begin{stmt}\sit{(1)}{\text{prose}}\end{stmt}\end{lemma}")
    _text, rep = latex2qpp.convert(src, "T")
    s = latex2qpp.summary(rep)["statement items"]
    assert (s["n"], s["formal"], s["same"], s["results"], s["results fully compiled"]) == (3, 2, 2, 2, 1)


def test_settled_readings():
    """the readings of lists with a range, operators with no argument, the coefficient at a point, and maps by their
    declared form (qpp/README.md, the settled readings)"""
    fs = {"CL", "cr_"}
    # 1: (I_j) is the list of the I_j, which needs its range; with the range it is a tuple over it
    with pytest.raises(T.Hole, match="a list needs its range"):
        item(r"\mathrm{cr}_i(S,\bw):=\{I_i:\ (I_j)\in\mathrm{CL}(S,\bw)\}", functions=fs)
    assert item(r"\mathrm{cr}_i(S,\bw):=\{I_i:\ (I_j)_{j\le k}\in\mathrm{CL}(S,\bw)\}", functions=fs) == (
        "cr_(i)(S, b_w) := {I_(i) : (tuple j <= k, I_(j)) in CL(S, b_w)}", True)
    # 2: \mathrm{rank} with no argument is no term; with one it applies
    with pytest.raises(T.Hole, match="without its argument"):
        item(r"r_{j'}:=\mathrm{rank}\ (j'\le j+1)")
    assert item(r"\operatorname{rank}B'=\operatorname{rank}B")[0] == "rank(B') = rank(B)"
    # 3: a pair at a point with no function to take there is the coefficient, bound by a binding: a hole
    with pytest.raises(T.Hole, match="the coefficient at a point"):
        item(r"(\lambda,m)=(\tfrac r2,1)\ \text{at}\ \btheta_0")
    # 4: a sign below a name in a context is both names; a sign of a term reads the part once per sign
    assert item(r"c_\pm>0,\ x>0\Rightarrow c_+x>0", scalars=("c_plus",)) == (
        "c_plus > 0, c_minus > 0, x > 0 => c_plus * x > 0", True)
    # 5: a sign per member of a family
    assert item(r"\epsilon_{R,f}=\pm1\ (f\in\mathcal J)") == ("forall f in cal_J : epsilon_(R, f) in {1, -1}", True)
    # 6: a name the paper declares a map and a number is no product before a name
    T.MAP_CLASH.add("pi_(phi)")
    try:
        with pytest.raises(T.Hole, match="name clash"):
            item(r"\pi_\phi\zeta=0")
    finally:
        T.MAP_CLASH.discard("pi_(phi)")
    # 7: a relation after a dots range holds for the terms before it too
    assert "W_0 in ZZ" in item(r"1\le W_0<W_1<\dots<W_{k+1}\in\Z")[0]
    # 8: the printer: \cdot before a parenthesis, bold Greek with a digit, an equivalence in a list, a minus after -
    assert item(r"C_p\cdot(r-l)\le1", scalars=("C_p",)) == ("C_(p) * (r - l) <= 1", True)
    assert T.tex_name("b_theta_0") == r"\btheta_0" and T.tex_name("b_delta_1") == r"\bd_1"
    assert item(r"x\ge1,\ (x=1\iff y=1)", scalars=("x", "y"))[1]
    assert item(r"a-(-b)=a+b", scalars=("a", "b"))[1]
    # 10: an index of the condition that is declared is no index of its own
    assert item(r"a_v:=b_j\ (v=t_j),\ a_v:=0\ \text{otherwise}", scalars=("j",))[0] == (
        "(v = t_(j) => a_(v) := b_(j)), (not(v = t_(j)) => a_(v) := 0)")


def test_guards_against_wrong_formal_items():
    """readings that would make a line formal and wrong (a divided difference, a list before its relation, a
    condition on data, a box of a network, a proof line of a superposition): each is a hole, and its neighbours that
    read correctly stay formal"""
    # 1: a capital before a polynomial applied is an operator on it (D_iP, the divided difference), not a product
    with pytest.raises(T.Hole, match="an operator on P"):
        item(r"|D_iP(\bw,\bw')|\le1", functions={"P"})
    assert item(r"N_R\theta_{R,f}(\bv)\in\Z", functions={"theta_"})[0] == "N_(R) * theta_(R, f)(b_v) in ZZ"
    assert item(r"D_iP(\bw)\le1", scalars=("D_",), functions={"P"})[0] == "D_(i) * P(b_w) <= 1"
    # 2: a name the item defines as a number and applies as a function is two objects under one name
    with pytest.raises(T.Hole, match="defined as a number and applied as a function"):
        item(r"j:=j(\bx_0),\ F:=F(\bx_0)", functions={"j", "F"})
    assert item(r"\psi(x'):=x'+1")[0] == "psi(x') := x' + 1"
    # 3: a gloss with a formula would be dropped (a hypothesis or a case lost) or read as a premise: a hole; a gloss
    # of words and references, with letters and item numbers, is dropped as before
    with pytest.raises(T.Hole, match="a gloss with a formula"):
        item(r"\Delta_T:=W'-c_ND\ (\text{less}\ \Sigma_2\ \text{at the second stage})")
    with pytest.raises(T.Hole, match="a gloss with a formula"):
        item(r"R\in\Pi\ (\text{an atlas of}\ \mathrm{Base}(\mathcal J'))")
    with pytest.raises(T.Hole, match="a gloss with a formula"):
        item(r"\Delta_T\ge s_0+E_j\ (\cref{lem:bandcell}(2):\ s'\ge s_0)")
    assert item(r"\Delta_T\ge E_j+W'\ (\cref{lem:bandcell}(2),\ \text{off the band})")[0] == "Delta_(T) >= E_(j) + W'"
    assert item(r"\beta'_j\ge e_1+8\ (\cref{lem:bandcell}(1),\ \text{case (ii)})")[0] == "beta'_(j) >= e_1 + 8"
    assert item(r"a\le m\ (\text{the same:}\ j\ \text{free})")[0] == "a <= m"
    # 4: O(...) is the order wherever the paper applies O, never an application
    with pytest.raises(T.Hole, match="asymptotic notation"):
        item(r"N\le(2d)^{O(2^n)}", functions={"O"})
    # 5: a set builder whose condition does not use its variable is all or nothing
    with pytest.raises(T.Hole, match="its condition does not use it"):
        item(r"\Theta_B:=\{\btheta:\ (c,a_h)\in B,\ \bw\in W\}")
    assert item(r"C:=\{\bd\in\Q^k:\ \delta_h\ge0\}")[0] == "C := {b_delta in QQ^k : delta_(h) >= 0}"
    # 6 (proof lines): the members of a list before its relation are holes, a named fact stays a claim
    assert latex2qpp.word(r"|1-a|,\ |\beta|\le\tfrac14:\ T\le3")[0] == "{?{|1-a|}}, {|beta| <= 1 / 4} : T <= 3"
    assert latex2qpp.word(r"\mathrm{Cones}\circ\text{(U1)}")[0] == "{Cones} o (U1)"
    # 7: a linear relation on data the given only declares, false for some of their values, is a condition (beta:
    # the inequalities an admissible choice meets), not a conclusion; a relation that holds
    # for every value, one on a constrained or a defined name and a non-linear one stay formal
    src = (r"\begin{lemma}\label{lem:k}\begin{stmt}\sit{given}{\beta,n,D\in\N,\ D\ge1;\ e:=\beta+1}"
           r"\sit{(1)}{\beta\ge n+2}\sit{(2)}{2\beta+1>\beta}\sit{(3)}{D+\beta\ge1}\sit{(4)}{\beta^2\ge n}"
           r"\sit{(5)}{e\ge1}\end{stmt}\end{lemma}")
    _text, rep = latex2qpp.convert(src, "T")
    got = {r["key"]: (r["qpp"], r["formal"]) for r in rep["items"] if r["key"] != "given"}
    assert got["(1)"] == (r"?{\beta\ge n+2}", False)
    assert got["(2)"] == ("2 * beta + 1 > beta", True)
    assert got["(3)"] == ("D + beta >= 1", True)
    assert got["(4)"] == ("beta^2 >= n", True)
    assert got["(5)"] == ("e >= 1", True)


# ------------------------------------------------------------- the constructs of laws, integrals and programs

def test_integrals():
    """\\int g\\,dq against a law, \\int_a^bg\\,d\\mu in a variable, \\int_a^bP of a polynomial in its variable: Q++
    int(g, q), int(g, mu, a, b), int(P, dot, a, b); Lean: bound by a binding of the paper, listed"""
    fs = {"f_", "f_star", "P"}
    assert item(r"K(\bw):=\int(f_\bw-f^*)^2dq", functions=fs | {"K"}) == ("K(b_w) := int((f_(b_w) - f_star)^2, q)", True)
    assert item(r"c\le\int_l^rP^2\le C", functions=fs) == ("c <= int(P^2, dot, l, r) <= C", True)
    assert item(r"T:=\int_0^1(\mu-(\mu a+\beta)_+)^2d\mu")[0] == "T := int((mu - max(mu * a + beta, 0))^2, mu, 0, 1)"
    _, why = lean_of(r"P\in\Q[x]", ("(1)", r"\int P^2\,dq\ge0"))
    assert "an integral (bound to the paper's library by a binding" in why


def test_function_families_and_composition_folds():
    """g_l\\colon\\Q\\to\\Q\\ \\text{for}\\ 1\\le l\\le L declares a family of functions; g_L\\circ\\dots\\circ g_1 is their
    composition, applied when a parenthesis follows (Lean: a fold over [1, ..., L])"""
    assert item(r"G:=g_L\circ\dots\circ g_1") == ("G := comp i in L..1, g_(i)", True)
    lean, _ = lean_of(r"L\in\N,\ g_l\colon\Q\to\Q\ \text{for}\ 1\le l\le L,\ y\in\Q",
                      ("(1)", r"(g_L\circ\dots\circ g_1)(y)=y"))
    assert "(g : \u2115 \u2192 (\u211a \u2192 \u211a))" in lean
    assert "((List.range' 1 L).foldl (fun acc i => (g i) \u2218 acc) id) y = y" in lean


def test_tropical_sums_and_constants_free_of():
    """\\bigoplus over a range or over several names; \\text{constants free of}\\ x,y after a clause"""
    assert item(r"(\lambda,m)=\textstyle\bigoplus_{j\le J}(\lambda_j,m_j)") == (
        "(lambda, m) = (oplus j <= J, (lambda_(j), m_(j)))", True)
    assert item(r"(\lambda,m)=\bigoplus_{\pi,T}(L_{\pi,T},m_{\pi,T})")[0] == (
        "(lambda, m) = (oplus pi, (oplus T, (L_(pi, T), m_(pi, T))))")
    assert item(r"K\asymp K_\pi\ \text{on}\ C_\pi,\ \text{constants free of}\ \ba,\bd") == (
        "(K asymp K_(pi) on C_(pi)) uniform_in(b_a, b_delta)", True)


def test_matrices():
    """Q^{m x n} the matrices (Mathlib's Matrix); \\det, \\tr, ^\\top, ^{-1}; a matrix times a vector, a row times a
    matrix, a row times a column; G\\succ0 positive definite (symmetric, x^T G x > 0); \\bd^{\\otimes d} a tensor power"""
    lean, _ = lean_of(r"p\in\N,\ G\in\Q^{p\times p},\ \bv\in\Q^p",
                      ("(1)", r"G\succ0\Rightarrow\bv^\top G\bv\ge0"), ("(2)", r"\det G\ne0\Rightarrow\tr(G)=\tr(G^\top)"))
    assert "(G : Matrix (Fin p) (Fin p) \u211a)" in lean
    assert "Matrix.transpose G = G \u2227 \u2200 x : Fin p \u2192 \u211a, x \u2260 0 \u2192 0 < \u2211 i, \u2211 j, x i * G i j * x j" in lean
    assert "(\u2211 \u03b9, (Matrix.vecMul v G) \u03b9 * v \u03b9) \u2265 0" in lean
    assert "(G.det \u2260 0) \u2192 G.trace = (Matrix.transpose G).trace" in lean
    assert item(r"G_d:=\bd^{\otimes d}") == ("G_(d) := tensor(b_delta, d)", True)


def test_differentials_and_small_arithmetic():
    """d before a declared map is its differential (jac); [P] the Iverson bracket, k! the factorial, \\dist(x,[a,b]);
    a part with \\pm in its context is two parts (one sign at a time)"""
    T.MAPS.add("R")
    try:
        assert item(r"dR(\bw_0)\ne0", functions={"R"}) == ("jac(R)(b_w_0) != 0", True)
    finally:
        T.MAPS.discard("R")
    assert item(r"\lambda=1+[\eta(k-2)=3]", scalars=("eta",)) == ("lambda = 1 + iverson(eta * (k - 2) = 3)", True)
    assert item(r"m\le(k+1)!\,H^k") == ("m <= fact(k + 1) * H^k", True)
    assert item(r"\delta:=t_1-t_2,\ 0<\pm\delta\le s:\ K=\kappa_\pm|\delta|")[0] == (
        "delta := t_1 - t_2, 0 < delta <= s : K = kappa_plus * |delta|; "
        "delta := t_1 - t_2, 0 < -delta <= s : K = kappa_minus * |delta|")
    lean, _ = lean_of(r"k,H\in\N,\ x,a,b\in\Q",
                      ("(1)", r"k!\,H^k\le(k+1)!\,H^k,\ 1+[k=2]\ge1,\ \dist(x,[a,b])\ge0"))
    assert "(Nat.factorial k : \u211a) * H ^ k \u2264 (Nat.factorial (k + 1) : \u211a) * H ^ k" in lean
    assert "1 + (if k = 2 then (1 : \u211a) else 0) \u2265 1" in lean
    assert "max (max (a - x) (x - b)) 0 \u2265 0" in lean


def test_no_infinity_and_guards():
    """\\infty is a hole outside the subscript of a norm (no infinity in a statement); letters side by side that no
    declaration makes numbers are prose; a capital before a vector is a matrix or a map unless declared a number"""
    with pytest.raises(T.Hole, match="infinity"):
        item(r"\lambda:=\infty")
    assert item(r"|\bw|_\infty\le1") == ("|b_w|_(inf) <= 1", True)
    hole(r"x\le the")
    hole(r"\eta=\beta J\bs", scalars=("beta",))
