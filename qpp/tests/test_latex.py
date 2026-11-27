r"""The LaTeX side of the fixtures. A source's LaTeX names a fixture of an item with \FIX{id}, after the item. For the
slice qpp/tests/fixtures/a_slice.tex:

* the extracted .qpp file is the output of latex2qpp on the LaTeX, so test_qpp.py checks the fixtures on the
  statements as the source writes them;
* every statement with a \FIX compiles to Q++ (no hole in its items), and its Lean statement is generated (qpp2lean;
  Lean elaborates it in the Lean build, not here); a \FIX after an item needs only that item and the given clauses,
  as the item is then its own statement.

The rows themselves are checked by test_qpp.py, on the extracted .qpp."""
from functools import lru_cache
from pathlib import Path

import pytest

from qpp import latex2qpp, qpp2lean

REPO = Path(__file__).resolve().parents[2]
SLICE = REPO / "qpp" / "tests" / "fixtures" / "a_slice.tex"


def papers():
    """(LaTeX source, name, extracted .qpp) of the slice. The fixtures of the Q++ modules are checked by
    qpp/modfix.py"""
    return [(SLICE, "ASlice", SLICE.with_suffix(".qpp"))]


@lru_cache(maxsize=None)
def compiled(tex, name):
    text, report = latex2qpp.convert(Path(tex).read_text(encoding="utf-8"), name, str(Path(tex).relative_to(REPO)))
    _lean, made, skipped = qpp2lean.generate(text)
    return text, report, made, dict(skipped), {k: dict(v) for k, v in qpp2lean.LAST_ITEMS.items()}


def fixed(text):
    """[(label, item or None, id)]: the fix lines of a .qpp text"""
    return [(r["label"], k, fid) for r in qpp2lean.read_qpp(text)["results"] for k, fid in r.get("fixes", [])]


@pytest.mark.parametrize("tex,name,qpp", papers(), ids=[p[1] for p in papers()])
def test_extracted_qpp_is_current(tex, name, qpp):
    assert Path(qpp).read_text(encoding="utf-8") == compiled(tex, name)[0], f"regenerate {qpp} with latex2qpp"


CASES = [(tex, name, label, item, fid) for tex, name, _ in papers() for label, item, fid in fixed(compiled(tex, name)[0])]


@pytest.mark.parametrize("tex,name,label,item,fid", CASES, ids=[f"{c[1]}:{c[4]}" for c in CASES])
def test_statement_with_a_fixture_compiles(tex, name, label, item, fid):
    _text, report, made, skipped, items = compiled(tex, name)
    # a fixture of an item needs that item to be formal, a fixture of the result every conclusion; the given is read
    # as qpp2lean reads it (a clause with a hole that no conclusion needs is left out, a core item stands without
    # the given), so whether it blocks is the Lean statement's question, asked below
    key, holes = None, []
    for i in report["items"]:
        if i["label"] != label:
            continue
        key = i["key"] or key
        if not i["formal"] and key != "given" and (item is None or key == item):
            holes.append(key)
    assert not holes, f"{label}: the items {holes} do not compile"
    stated = label in made or skipped.get(label, "").startswith("stated") or (
        item is not None and item in items.get(label, {}).get("stated", []))
    assert stated, f"{label}: no Lean statement ({skipped.get(label)})"
