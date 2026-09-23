"""Refusal reaches the same results as the base exploration."""

from __future__ import annotations

from pathlib import Path
from typing import cast

import pytest

from twentyfirst import evidence
from twentyfirst.evidence import audit, write_all
from twentyfirst.refusal import refusal_result
from xry.state import Sameness, State, given


def test_a_refusal_returns_the_state() -> None:
    start = given(False, Sameness.ANCHORED)
    assert refusal_result(start) == start
    assert evidence.refusal_changes(start, start) is False
    assert evidence.refusal_changes(State.of(1, [], (0, 0)), start) is True
    assert evidence.answer_is_new(start, {start: 0}) is False
    assert evidence.answer_is_new(State.of(1, [], (0, 0)), {start: 0}) is True
    assert evidence.has_unobstructed(start) is True


def test_refusal_matches_the_base_inside_two_terms() -> None:
    clean = audit(False, Sameness.ANCHORED, 2, 4)
    assert clean.outside_the_base == []
    assert clean.answer_buys_a_result == []
    assert clean.stopped_at_the_start == []


def test_audit_records_each_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "refusal_changes", lambda _answer, _state: True)
    assert audit(False, Sameness.ANCHORED, 2, 2).outside_the_base
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "refusal_changes", lambda _answer, _state: False)
    monkeypatch.setattr(evidence, "refusal_result", lambda _state: State.of(1, [], (0, 0)))
    assert audit(False, Sameness.ANCHORED, 2, 2).outside_the_base
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "answer_is_new", lambda _got, _depth: True)
    assert audit(False, Sameness.ANCHORED, 2, 2).answer_buys_a_result
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "has_unobstructed", lambda _state: False)
    assert audit(False, Sameness.ANCHORED, 2, 2).stopped_at_the_start == ["2:01:0-1"]


def test_write_and_check(tmp_path: Path) -> None:
    summary = write_all(tmp_path, 3, 12)
    runs = {
        (row["bra"], row["sameness"]): row
        for row in cast(list[dict[str, object]], summary["runs"])
    }
    assert runs[(False, "anchored")]["results"] == 109
    assert runs[(False, "anchored")]["last_new_round"] == 10
    assert runs[(False, "anchored")]["frontier_exits"] == 700
    assert runs[(True, "anchored")]["results"] == 109
    assert runs[(True, "anchored")]["last_new_round"] == 11
    assert runs[(False, "free")]["results"] == 20
    assert runs[(False, "free")]["last_new_round"] == 6
    assert runs[(False, "free")]["frontier_exits"] == 112
    assert runs[(True, "free")]["results"] == 20
    assert runs[(True, "free")]["last_new_round"] == 5
    for row in runs.values():
        assert row["outside_the_base"] == []
        assert row["answer_buys_a_result"] == []
        assert row["stopped_at_the_start"] == []
        assert cast(int, row["answers_checked"]) > 0
    from twentyfirst.__main__ import main

    small = tmp_path / "small"
    write_all(small, 2, 2)
    assert main(["--out", str(small), "--check", "--bound", "2", "--rounds", "2"]) == 0
    (small / "summary.json").write_text("{}\n", encoding="utf-8", newline="\n")
    assert main(["--out", str(small), "--check", "--bound", "2", "--rounds", "2"]) == 1
    assert main(["--out", str(tmp_path / "missing"), "--check"]) == 1
