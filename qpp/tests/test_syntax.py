"""Tests of qpp/syntax.py on small sources (no git, no papers)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from qpp import syntax as syn  # noqa: E402


def heads(expr):
    items, gloss, nmath, keyed = syn.parse_line(expr)
    return [syn.chain_syms(ch) for ch in items], gloss, syn.classify(items, nmath, keyed)


def test_a_line_is_a_word():
    syms, gloss, cls = heads(r"\iota_{\rm chain}(\gV\circ\gI[|F(\bu)-F(\bv)|\le\delta<|F(\bu)|])")
    assert syms == [["iota_chain(V o I)"]]
    assert cls == "G"


def test_gloss_and_references():
    syms, gloss, cls = heads(r"\Pt3[(S_0,t-F),\ M];\ \cref{lem:resultant}(2),(3)[N\ne0]:\ \text{a bound}")
    assert syms == [["P3"], ["ref"], ["self"]]
    assert gloss.startswith(r"\text{a bound}")
    assert cls == "G"


def test_case_then_word_and_formula_lines():
    assert heads(r"\text{right of}\ h_+:\ \gV[(c_0y)^2\le3e^2]")[2] == "K"
    assert heads(r"K''\ge Q^2+Y,\ \le CL^{m'-1}")[2] == "F"
    assert heads(r"\cref{lem:gram}(4),\ \cref{lem:a}")[2] == "R"
    assert heads(r"\gV[a\le b]\circ x_1+x_2\circ\gI[c=d]")[2] == "M"


def test_comparators():
    assert heads(r"\gInd_{\rm chain}(\gV\circ\gI[x])")[0] == [["ind_chain(V o I)"]]
    assert heads(r"\gNeq[h]\circ\gEq")[0] == [["neq", "eq"]]
    assert heads(r"\gEq^\vee\circ\gInd_k")[0] == [["eq^v", "ind_level"]]
    assert heads(r"\mathrm{Scale}\circ\gV[x]")[0] == [["Scale", "V"]]
    rep = syn.analyse({"P": "\\begin{proof}\n\\begin{expr}\n\\eit{(1)}{\\gInd\\circ\\gI[c=d]}\n\\end{expr}\n\\end{proof}\n"})
    assert [i["what"] for i in rep["papers"]["P"]["issues"] if i["rule"] == "T3"] == ["bare ind"]
    assert syn.collapse(["eq", "I", "V"]) == ["I", "V"]


def test_old_names_are_reported():
    src = "\\begin{proof}\n\\begin{expr}\n\\eit{(1)}{\\alpha\\circ\\iota_k[x\\le1]}\n\\eit{(2)}{\\gEq\\circ\\gInd_k[x\\le1]}\n\\end{expr}\n\\end{proof}\n"
    rep = syn.analyse({"P": src})
    assert [i["what"] for i in rep["papers"]["P"]["issues"] if i["rule"] == "T8"] == ["alpha (use eq)", "iota (use ind)"]


def test_beta_as_atom_or_variable():
    assert heads(r"\beta\circ\gV[x]")[0] == [["beta", "V"]]
    assert heads(r"\gV[x]:\ \beta\le1")[0] == [["V"]]
    syms, _, cls = heads(r"\beta_0\le\gamma")
    assert cls == "F"


def test_dual_marks_and_parts():
    syms, _, _ = heads(r"\cref{lem:balance}(2)^\vee[F:=G]\circ\Pt1(2)^\vee")
    assert syms == [["ref^v", "P1(2)^v"]]


def test_nested_aliases_expand_and_cycles_are_errors():
    defs = {"Pig": {"rhs": r"\gV\circ\iota", "slots": "", "line": 0},
            "Hensel_p": {"rhs": r"\gPig\circ\gV_p\circ\gI", "slots": "", "line": 0},
            "Loop": {"rhs": r"\Cx{Loop2}", "slots": "", "line": 0},
            "Loop2": {"rhs": r"\Cx{Loop}", "slots": "", "line": 0}}
    ex = syn.Expander(defs)
    assert [t for t in ex.expand("Hensel_p") if t not in "()"] == ["V", "o", "iota", "o", "V", "o", "I"]
    try:
        ex.expand("Loop")
    except ValueError as e:
        assert "cycle" in str(e)
    else:
        raise AssertionError("cycle not detected")


SRC = r"""
\newcommand{\gPig}{\mathrm{Pig}}
\item \(\gPig:=\gV\circ\iota\) on counts.
\begin{lemma}\label{lem:x}
\end{lemma}
\begin{proof}
\begin{expr}
\eit{(1)}{\gPig[x]\circ\gI[a=b]}
\eit{(2)}{\gSwap[S]\circ\cref{lem:y}}
\eit{(3)}{\iota\circ\gI[c=d]}
\eit{(4)}{\gV\circ\cref{lem:z}}
\end{expr}
\end{proof}
"""


def test_checker_rules_on_a_small_paper():
    rep = syn.analyse({"P": SRC})
    d = rep["papers"]["P"]
    assert d["lines"] == 4
    assert "Pig" in d["defined_here"]
    assert d["undefined"] == ["Swap"]
    rules = sorted({i["rule"] for i in d["issues"]})
    assert "T1" in rules and "T3" in rules


def test_collapse_and_repair():
    assert syn.collapse(["V", "V", "I", "alpha", "V", "I"]) == ["V", "I"]
    rules = syn.repair([["V", "iota", "ref"], ["V", "iota"], ["x", "V", "iota"], ["V", "iota", "y"]], min_count=3)
    assert rules[0][1:] == ("V", "iota", 4)


def test_prime_instance():
    """an alias defined at a prime p, used at p = 2: the instance Name_2 is Name_p[p:=2]"""
    src = (r"\item \(\gHen_p:=\gV_p\circ\gI\), the pivot at \(p\)." "\n"
           r"\begin{proof}" "\n" r"\eit{(1)}{\gHen_2[G:=y]\circ\gV}" "\n" r"\end{proof}")
    d = syn.analyse({"P": src})["papers"]["P"]
    assert d["undefined"] == [] and d["used_without_definition_here"] == []
    assert d["records"][0]["word"] == "( V o I ) o V"


def test_cited_facts_and_templates_are_opaque_leaves():
    r"""the first column of a 'name & fact & reference' table declares cited facts (S, \Pt1--\Pt4, \Kt, Bands), and a
    row 'templates' declares templates in words (\Pt6, \Pt7): no T1, no expansion in atoms, each one leaf
    cite:NAME or tpl:NAME"""
    src = ("\\begin{tabular}{ll}\nname & fact & reference & used in\\\\\n\\hline\n"
           "S, \\(\\Pt1\\)--\\(\\Pt4\\), \\(\\Kt\\) & the patterns & elementary & everywhere\\\\\n"
           "Bands & one term dominates & \\cite{O} & here\\\\\n\\Rf1--\\Rf2, \\Mf & the continuum & \\cite{B} & there\\\\\n"
           "\\hline\n\\end{tabular}\n"
           "\\begin{stmt}\\sit{templates}{\\Pt6:\\ \\text{a two-sided bound};\\ \\Pt7[(\\mathrm X){:=}E]:\\ \\text{each condition}}"
           "\\end{stmt}\n"
           "\\begin{proof}\n\\begin{expr}\n\\eit{(1)}{\\Pt3\\circ\\Kt(2)[x]}\n\\eit{(2)}{\\Pt6[x]\\circ\\Pt7[y]}\n"
           "\\end{expr}\n\\end{proof}\n")
    d = syn.analyse({"P": src})["papers"]["P"]
    assert {"S", "P1", "P2", "P3", "P4", "K", "Bands", "R1", "R2", "M"} <= set(d["cited"])
    assert not [i for i in d["issues"] if i["rule"] == "T1"] and not d["used_without_definition_here"]
    assert d["expansions"]["P3"] == "cite:P3" and d["expansions"]["P6"] == "tpl:P6"
    assert [r["word"] for r in d["records"]] == ["( cite:P3 ) o ( cite:K )", "( tpl:P6 ) o ( tpl:P7 )"]


def test_scale_words_digit_aliases_and_beta_constants():
    r"""Scale, Arch, Floor are verbs (no T1); an alias name may end in digits; \beta as a constant of the paper
    (\beta_T:=n+2, \beta(\kappa,n), a member of a list of terms) is neither the old atom nor an alias"""
    src = ("Let \\(\\mathrm{P3}:=\\gV\\circ\\gI\\) and \\(\\beta_T:=n+2\\), \\(\\beta_*:=\\beta(2n,n)\\).\n"
           "\\begin{proof}\n\\begin{expr}\n\\eit{(1)}{\\mathrm{Arch}[q>x]\\circ\\mathrm{Floor}\\circ\\mathrm{Scale}}\n"
           "\\eit{(2)}{\\gV[\\text{fixed}:\\ \\kappa_c,\\ \\beta,\\ c_N]}\n\\end{expr}\n\\end{proof}\n")
    d = syn.analyse({"P": src})["papers"]["P"]
    assert d["defined_here"] == ["P3"] and d["expansions"]["P3"] == "V o I"
    assert not [i for i in d["issues"] if i["rule"] in ("T1", "T8")]
    assert heads(r"\mathrm{Arch}[q>x]\circ\mathrm{Floor}")[0] == [["Arch", "Floor"]]
