"""The Q++ 0.2 source (qpp/source.py), its LaTeX (qpp/qpp2latex.py) and its Lean over the kernel (qpp/kernel.py).

The section qpp/examples/means.qpp is the round-trip test: its LaTeX reads back through latex2qpp to the same items and
proof lines, and its Lean (qpp/lean/QppGen/Means.lean, compiled by the memo unit qpp-kernel) is what the generator
writes now. The cited fact of the section is checked on fixtures in exact arithmetic.
"""
import random
import re
from fractions import Fraction
from pathlib import Path

import pytest

from qpp import kernel as K
from qpp import latex2qpp as L
from qpp import qpp2latex as P
from qpp import source as S

ROOT = Path(__file__).resolve().parents[2]
EX = ROOT / "qpp" / "examples" / "means.qpp"
RNG = random.Random(20261109)


def doc():
    return S.read_file(EX)


# the source


def test_reader_blocks_and_lines():
    d = doc()
    kinds = [type(b).__name__ for b in d.blocks]
    assert kinds[:3] == ["Prose", "Section", "Item"]
    cit = d.item("fact:powermean")
    assert cit.kind == "cit" and cit.title == "power means" and cit.prose
    assert cit.row("doi").text == "10.1017/CBO9781139020411"
    assert [r.key for r in cit.stmt_rows()] == ["given", "(1)"]
    mean = d.item("lem:mean")
    assert EX.read_text().splitlines()[mean.row("(2)").line - 1].strip().startswith("(2):")
    pr = d.proofs()["lem:square"]
    assert pr.prose == ["The cross term is a name: the identity uses its definition, never its expansion."]
    assert [(r.key, r.text) for r in pr.lines] == [("(1)", "eq[h_c]"), ("(2)", "V[h_c]")]


def test_reader_errors_name_the_line():
    with pytest.raises(S.SourceError, match=r"x\.qpp:2: the cited fact fact:y needs a row 'doi"):
        S.read("paper p\ncit fact:y\n  given: u in QQ>0\n", "x.qpp")
    with pytest.raises(S.SourceError, match=r":3: a proof of lem:z, which no item states"):
        S.read("paper p\n\nproof lem:z\n  (1) eq\n", "x.qpp")
    with pytest.raises(S.SourceError, match=r":2: an indented line outside"):
        S.read("paper p\n  given: u in QQ>0\n", "x.qpp")


def test_prose_above_an_item_is_its_description():
    d = S.read("-- Q++ 0.2\npaper p\n-- free\n\n-- about x\nlemma lem:x [t]\n  (1): 1 < 2\n", "x.qpp")
    assert isinstance(d.blocks[0], S.Prose) and d.blocks[0].lines == ["free"]
    assert d.item("lem:x").prose == ["about x"] and d.item("lem:x").title == "t"


# the LaTeX and the round trip


def canon_word(w):
    """a proof word up to the spelling of hypothesis names: h_(c) is h_c"""
    return re.sub(r"\bh_\((\w+)\)", r"h_\1", w)


def test_latex_round_trip():
    """qpp -> LaTeX -> latex2qpp gives back every item and proof line"""
    d = doc()
    tex, _ = P.generate(d, EX.parent / d.bib, full=True)
    back = S.read(re.sub(r"^-- Q\+\+ 0\.1.*\n", "", L.convert(tex, paper="means")[0]),
                  "back.qpp")
    for it in d.items():
        b = back.item(it.label)
        assert b is not None, it.label
        assert [(r.key, r.text) for r in it.stmt_rows()] == [(r.key, r.text) for r in b.rows]
    for label, pr in d.proofs().items():
        assert [(r.key, r.text) for r in pr.lines] == \
            [(r.key, canon_word(r.text)) for r in back.proofs()[label].lines]


def test_latex_is_current():
    d = doc()
    tex, bib = P.generate(d, EX.parent / d.bib, source="qpp/examples/means.qpp")
    assert tex == EX.with_suffix(".tex").read_text()
    assert bib == EX.with_suffix(".bib").read_text()


def test_bib_reuses_the_entry_with_the_doi():
    d = doc()
    _, bib = P.generate(d, EX.parent / d.bib)
    assert "@book{HornJohnson2013," in bib
    _, bib2 = P.generate(d, None)
    assert "@misc{doi_10_1017_CBO9781139020411," in bib2 and "doi  = {10.1017/CBO9781139020411}" in bib2


def test_word_tex():
    assert P.word_tex("V[1 / 2 * h_1]") == "\\gV[1/2 h_1]"
    assert P.word_tex("fact:powermean(1)[D := 2]") == "\\cref{fact:powermean}(1)[D:=2]"
    assert P.word_tex("eq o ind_k") == "\\gEq\\circ \\gInd_{k}"


# the Lean over the kernel


def test_lean_report():
    _, srcmap, report = K.generate(doc(), source="means.qpp")
    got = {(label, key): why for label, key, _, ok, why in report}
    assert got[("fact:powermean", "(1)")] == "cited"
    assert got[("lem:mean", "(1)")] == got[("lem:square", "(1)")] == got[("lem:sumsq", "(1)")] == "proved"
    assert got[("lem:sumsq", "(2)")] == "a hole"


def test_lake_messages_at_their_qpp_lines():
    """Lake's form `error: F.lean:L:C: m`; a message of an imported file keeps its file and is at Q++ line 0"""
    _, srcmap, _ = K.generate(doc(), source="means.qpp")
    out = ("\u2716 [5/7] Building QppGen.Means\nerror: ./QppGen/Means.lean:30:2: farkas: no certificate\n"
           "error: ./QppGen/Means/Statements.lean:9:0: unknown identifier 'x'\nerror: Lean exited with code 1\n")
    (q, sev, msg, ln), (q2, _, msg2, _) = K.map_messages(out, srcmap, "means.qpp", lean_name="Means.lean")
    assert (sev, ln, msg) == ("error", 30, "farkas: no certificate") and q == srcmap[29]
    assert q2 == 0 and msg2.startswith("./QppGen/Means/Statements.lean:9: unknown identifier")


def test_docstrings_cannot_close_early():
    assert K.doc_text("a/-b-/c") == "a/ -b- /c"


# the cited fact on fixtures (exact arithmetic)


def test_power_mean_fixture():
    """fact:powermean: (sum u)^(E+1) <= J^E sum u^(E+1), for masses, on random fixtures; equal masses attain it"""
    for _ in range(300):
        J, E = RNG.randint(1, 6), RNG.randint(1, 5)
        u = [Fraction(RNG.randint(1, 30), RNG.randint(1, 30)) for _ in range(J)]
        assert sum(u) ** (E + 1) <= J ** E * sum(x ** (E + 1) for x in u)
        c = u[0]
        assert (J * c) ** (E + 1) == J ** E * J * c ** (E + 1)
