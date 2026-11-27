"""The Q++ 0.2 sources: the modules of modules/, read as one paper (qpp.modules.whole: every module, dependencies
first) inside a small frame, print to LaTeX, and the migration from that LaTeX gives the source back.

The article leaves out the `core` rows, the proof lines keyed `core` and the fixtures, which only the checks read;
the full printing keeps them, and the checks read it.

The migration test is the check of qpp/migrate.py: the module set printed in full, migrated again, is the same source,
and the migration's own check (the printed paper reads, through latex2qpp, as the LaTeX it came from) passes in one
round.
"""
from pathlib import Path

import pytest

from qpp import modules as Mod
from qpp import qpp2latex as P
from qpp import source as S

ROOT = Path(__file__).resolve().parents[2]
FRAME = "\\documentclass{amsart}\n\\begin{document}\n" + P.BODY + "\n\\bibliography{references}\n\\end{document}\n"


@pytest.fixture(scope="module")
def whole(tmp_path_factory):
    """the manifest of every module with its frame, its doc, the article and the full printing"""
    tmp = tmp_path_factory.mktemp("whole")
    src, frame = tmp / "modules.qpp", tmp / "frame.tex"
    src.write_text(Mod.whole(ROOT).replace("\n\n", "\nframe frame.tex\n\n", 1), encoding="utf-8")
    frame.write_text(FRAME, encoding="utf-8")
    doc = S.read_file(src)
    art, _ = P.generate(doc, frame=FRAME, source="modules.qpp")
    full, _ = P.generate(doc, frame=FRAME, source="modules.qpp", full=True)
    return src, frame, doc, art, full


def test_the_manifest_includes_every_module_after_its_uses(whole):
    src, _frame, doc, _art, _full = whole
    assert doc.frame == "frame.tex"
    order = [line.split()[1] for line in src.read_text(encoding="utf-8").split("\n") if line.startswith("include ")]
    assert sorted(order) == Mod.all_modules(ROOT)
    for i, name in enumerate(order):
        assert set(S.read_module(name, ROOT).uses) <= set(order[:i]), name


