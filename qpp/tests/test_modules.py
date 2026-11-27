"""Tests of qpp/modules.py and the manifests of qpp/source.py on a small paper."""

import pytest

from qpp import modules as M
from qpp import source as S

PAPER = """-- Q++ 0.2
paper toy

section sec:intro Introduction
-- We read \\cref{lem:b} in \\cref{sec:a}.
section sec:setting Setting
subsection sec:def Definitions
definition def:x
  given: x in QQ>=0
remark rem:x
  (1): ?{\\text{compare}\\ \\cref{lem:b}}
subsection sec:prior Prior work
-- Nothing here is new.
section sec:a Results
lemma lem:b
  given: x in QQ>=0
  (1) ?{x\\ge0\\ \\text{by}\\ \\cref{def:x}}
proof lem:b
  (1) direct, see \\cref{sec:intro}
"""

PLAN = [("front", ["sec:intro", "sec:prior"]), ("defs", ["sec:setting", "sec:def"]), ("results", ["sec:a"])]


def test_a_split_flattens_back_and_takes_its_uses_from_the_proofs(tmp_path):
    src = tmp_path / "toy.qpp"
    src.write_text(PAPER, encoding="ascii")
    manifest, modules = M.write_split(src, PLAN, root=tmp_path)
    # the front takes two runs, so it is included run by run and cut at the heading of the second
    assert "include front sec:intro\ninclude defs\ninclude front sec:prior\ninclude results\n" in manifest
    assert S.flatten(manifest, str(src), tmp_path)[0] == PAPER
    # results uses defs (def:x in a proof line); the reference to sec:intro is a pointer, not a use
    assert modules["results"].split("\n")[2] == "uses defs"
    assert modules["front"].split("\n")[2] == ""  # prose may point anywhere
    assert modules["defs"].split("\n")[2] == ""  # and so may a remark: rem:x reads lem:b ahead
    assert src.read_text(encoding="ascii") == manifest


def test_a_split_keeps_every_section_in_a_module(tmp_path):
    src = tmp_path / "toy.qpp"
    src.write_text(PAPER, encoding="ascii")
    with pytest.raises(ValueError, match="sec:a"):
        M.write_split(src, PLAN[:2], root=tmp_path)
    assert src.read_text(encoding="ascii") == PAPER


def test_a_use_outside_the_closure_and_a_cycle_are_refused(tmp_path):
    def module(name, uses, body):
        p = S.module_path(name, tmp_path)
        p.parent.mkdir(parents=True)
        p.write_text("-- Q++ 0.2\nmodule %s\n%s\n%s" % (name, f"uses {uses}\n" if uses else "", body),
                     encoding="ascii")

    module("one", "", "lemma lem:one\n  (1) ?{\\cref{lem:two}}\n")
    module("two", "one", "lemma lem:two\n  (1) ?{\\cref{lem:one}}\n")
    both = [S.read_module("one", tmp_path), S.read_module("two", tmp_path)]
    with pytest.raises(S.SourceError, match="does not use"):
        S.check_modules(both, tmp_path)  # lem:two is not in the closure of one
    p = S.module_path("one", tmp_path)
    p.write_text(p.read_text().replace("module one\n", "module one\nuses two\n"), encoding="ascii")
    with pytest.raises(S.SourceError, match="cycle"):
        S.check_modules([S.read_module("one", tmp_path)], tmp_path)


def test_a_label_in_two_modules_is_refused(tmp_path):
    """the modules are one set, whichever papers include them: a label names one item"""
    for name, body in (("one", "lemma lem:same\n  (1) ?{a}\n"), ("two", "remark lem:same\n  (1) ?{b}\n")):
        p = S.module_path(name, tmp_path)
        p.parent.mkdir(parents=True)
        p.write_text(f"-- Q++ 0.2\nmodule {name}\n\n{body}", encoding="ascii")
    with pytest.raises(S.SourceError, match="lem:same is defined in module"):
        S.check_modules([S.read_module("one", tmp_path), S.read_module("two", tmp_path)], tmp_path)
