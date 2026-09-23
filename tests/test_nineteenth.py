"""Identification rewrites one assertion and does not erase a term."""

from __future__ import annotations

from pathlib import Path
from typing import cast

import pytest

from nineteenth import evidence
from nineteenth.changes import between_the_two, obstructed, other_changes, partials, perform_partial
from nineteenth.evidence import audit, write_all
from nineteenth.explore import PartialExploration, explore_partial
from xry.changes import Change, Kind, changes, perform
from xry.state import Sameness, State, given


def test_one_sided_rewrite_keeps_the_terms_and_a_cooccurrence_is_a_loop() -> None:
    state = State.of(3, [(0, 2)], (0, 1))
    one_sided = [item for item in partials(state) if item.u == 0 and item.v == 1]
    assert len(one_sided) == 1
    assert one_sided[0].survivor == 1
    assert not between_the_two(one_sided[0])
    outcome = perform_partial(state, one_sided[0])
    assert outcome.n == state.n and outcome.has(1, 2) and not outcome.has(0, 2) and outcome.legal
    assert [item for item in partials(state, True) if item.u == 0 and item.v == 1] == []
    assert partials(state, True)
    both = [item for item in partials(state) if {item.u, item.v} == {0, 2}]
    assert both and all(between_the_two(item) and obstructed(state, item) for item in both)
    start = given(False, Sameness.ANCHORED)
    assert partials(start, True) == partials(start)
    assert all(obstructed(start, item) for item in partials(start))
    assert all(change.kind is not Kind.IDENTIFY for change in other_changes(start))
    assert any(change.kind is Kind.IDENTIFY for change in changes(start))
    assert perform(start, Change(Kind.IDENTIFY, 0, 1)).n == 1


def test_exploration_refuses_a_loop_and_records_a_performed_rewrite() -> None:
    start = given(False, Sameness.ANCHORED)
    with pytest.raises(ValueError, match="xrx"):
        explore_partial(State.of(1, [(0, 0)], (0, 0)), 3, 1)
    with pytest.raises(ValueError, match="bound"):
        explore_partial(start, 1, 1)
    logged = explore_partial(start, 3, 3, keep_log=True)
    assert logged.new_per_round[0] == 1
    assert logged.log
    assert any(line.startswith("obstructed ") for line in logged.log)
    assert logged.min_terms == 2


def test_the_two_readings_agree_inside_two_terms() -> None:
    clean = audit(False, Sameness.ANCHORED, 2, 2)
    assert clean.sets_differ == []
    assert clean.extra_beyond_base == []
    assert clean.term_dropped == []
    assert clean.cooccur_performed == []
    assert clean.obstruction_not_between == []
    assert clean.removal_answer_outside == []


def test_audit_records_each_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    real = explore_partial

    def plant(
        start: State, bound: int, rounds: int = 12, cooccur_only: bool = False, keep_log: bool = False
    ) -> PartialExploration:
        del keep_log
        exp = real(start, bound, rounds, cooccur_only, False)
        exp.depth = dict(exp.depth)
        if cooccur_only:
            exp.depth[State.of(2, [(1, 0)], (1, 0))] = 1
            exp.performed_partials = 1
        else:
            exp.depth[State.of(1, [], (0, 0))] = 1
            exp.depth[State.of(3, [], (0, 1))] = 1
        return exp

    monkeypatch.setattr(evidence, "explore_partial", plant)
    planted = audit(False, Sameness.ANCHORED, 2, 2)
    assert planted.sets_differ
    assert planted.extra_beyond_base
    assert planted.term_dropped
    assert planted.cooccur_performed == ["cooccur performed"]
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "obstructed", lambda _state, _partial: False)
    assert audit(False, Sameness.ANCHORED, 2, 2).obstruction_not_between
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "canonical", lambda _state: State.of(3, [], (0, 0)))
    assert audit(False, Sameness.ANCHORED, 2, 2).removal_answer_outside


def test_write_and_check(tmp_path: Path) -> None:
    summary = write_all(tmp_path, 3, 12)
    assert summary["anchored_closures_equal_for_both_bra"] is True
    assert summary["free_closures_equal_for_both_bra"] is True
    runs = {
        (row["bra"], row["sameness"]): row
        for row in cast(list[dict[str, object]], summary["runs"])
    }
    anchored = runs[(False, "anchored")]
    assert anchored["partial_results"] == 68
    assert anchored["base_results"] == 109
    assert anchored["missing"] == 41
    assert anchored["missing_names_one_term"] == 41
    assert anchored["missing_one_term_count"] == 1
    assert anchored["extra"] == 0
    assert anchored["min_terms"] == 2
    assert anchored["performed_partials"] == 384
    assert anchored["obstructed_partials"] == 392
    assert anchored["cooccur_performed"] == 0
    assert anchored["frontier"] == 64
    assert anchored["new_per_round"] == [1, 3, 9, 20, 22, 11, 2, 0]
    assert anchored["sets_differ"] == []
    free = runs[(False, "free")]
    assert free["partial_results"] == 19
    assert free["base_results"] == 20
    assert free["missing"] == 1
    assert free["missing_one_term_count"] == 1
    assert free["performed_partials"] == 96
    assert free["frontier"] == 16
    assert free["new_per_round"] == [1, 3, 5, 4, 4, 1, 1, 0]
    assert runs[(True, "anchored")]["partial_results"] == 68
    assert runs[(True, "anchored")]["new_per_round"] == [1, 3, 11, 29, 20, 4, 0]
    assert runs[(True, "free")]["partial_results"] == 19
    assert runs[(True, "free")]["new_per_round"] == [1, 2, 5, 9, 1, 1, 0]
    from nineteenth.__main__ import main

    small = tmp_path / "small"
    write_all(small, 2, 2)
    assert main(["--out", str(small), "--check", "--bound", "2", "--rounds", "2"]) == 0
    (small / "summary.json").write_text("{}\n", encoding="utf-8", newline="\n")
    assert main(["--out", str(small), "--check", "--bound", "2", "--rounds", "2"]) == 1
    assert main(["--out", str(tmp_path / "missing"), "--check"]) == 1
