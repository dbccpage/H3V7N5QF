"""The citation/report gate bites on a missing Lean-generated receipt."""

from __future__ import annotations

import shutil
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "ci"))

import check_axiom_citations as gate  # noqa: E402


def test_citation_report_gate_is_clean() -> None:
    assert gate.main([]) == 0


def test_missing_cited_report_line_bites_and_restoration_passes(tmp_path: Path) -> None:
    lean = tmp_path / "lean4" / "Second" / "Proof.lean"
    paper = tmp_path / "paper" / "second" / "paper.md"
    ledger = tmp_path / "paper" / "second" / "claim_ledger.md"
    report = tmp_path / "evidence" / "second" / "lean_axioms.txt"
    for path in (lean, paper, ledger, report):
        path.parent.mkdir(parents=True, exist_ok=True)
    lean.write_text("namespace Seed.Second\n@[simp] theorem witness : True := by trivial\nend Seed.Second\n", encoding="utf-8")
    paper.write_text("The proof is `Seed.Second.witness`.\n", encoding="utf-8")
    ledger.write_text("| D1 | witnessed | derived | `Seed.Second.witness` |\n", encoding="utf-8")
    good = "'Seed.Second.witness' does not depend on any axioms\n"
    report.write_text(good, encoding="utf-8")
    assert gate.check(tmp_path, ("second",)) == []
    report.write_text("'Seed.Second.other' does not depend on any axioms\n", encoding="utf-8")
    assert gate.check(tmp_path, ("second",)) == [
        "second: Seed.Second.witness absent from own axiom report"
    ]
    report.write_text(good, encoding="utf-8")
    assert gate.check(tmp_path, ("second",)) == []


def test_real_second_parent_citation_report_line_bites(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Remove F003's actual Reach.legal receipt, then restore it."""
    for source, dest in (
        (REPO / "paper" / "second" / "paper.md", tmp_path / "paper" / "second" / "paper.md"),
        (REPO / "paper" / "second" / "claim_ledger.md", tmp_path / "paper" / "second" / "claim_ledger.md"),
        (REPO / "evidence" / "second" / "lean_axioms.txt", tmp_path / "evidence" / "second" / "lean_axioms.txt"),
    ):
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, dest)
    monkeypatch.setattr(gate, "declarations", lambda _root: {"Reach.legal"})
    report = tmp_path / "evidence" / "second" / "lean_axioms.txt"
    good = report.read_text(encoding="utf-8")
    line = next(row for row in good.splitlines(keepends=True) if row.startswith("'Seed.Reach.legal' "))
    assert gate.check(tmp_path, ("second",)) == []
    report.write_text(good.replace(line, "", 1), encoding="utf-8")
    assert gate.check(tmp_path, ("second",)) == [
        "second: Reach.legal absent from own axiom report"
    ]
    report.write_text(good, encoding="utf-8")
    assert gate.check(tmp_path, ("second",)) == []
