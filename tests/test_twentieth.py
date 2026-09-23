"""The round counts changes. Additions are a different ranking."""

from __future__ import annotations

from pathlib import Path
from typing import cast

import pytest

from twentieth import evidence
from twentieth.evidence import audit, witness, write_all
from twentieth.order import _bfs as real_bfs
from twentieth.order import additions_priority, changes_priority, rankings_differ
from xry.explore import explore
from xry.state import Sameness, State, given


def test_a_single_result_has_no_ranking_witness() -> None:
    start = given(False, Sameness.ANCHORED)
    assert rankings_differ({}) is None
    assert rankings_differ({start: 0}) is None
    assert witness({}) is None
    assert witness({start: 0}) is None
    with pytest.raises(ValueError, match="xrx"):
        real_bfs(State.of(1, [(0, 0)], (0, 0)), 3, 1, False)
    with pytest.raises(ValueError, match="bound"):
        real_bfs(start, 1, 1, True)
    with pytest.raises(ValueError, match="xrx"):
        additions_priority(State.of(1, [(0, 0)], (0, 0)), 3, 1)
    with pytest.raises(ValueError, match="bound"):
        additions_priority(start, 1, 1)
    assert set(additions_priority(start, 2, 0)) == {start}
    assert set(changes_priority(start, 2, 0)) == {start}
    finished = real_bfs(start, 2, 6, False)
    assert 1 <= len(finished) < 109


def test_listings_agree_inside_two_terms() -> None:
    clean = audit(False, 2, 4)
    assert clean.layer_mismatch == []
    assert clean.frontier_mismatch == []
    assert clean.additions_track_rounds == []
    assert clean.differs_from_base == []
    assert clean.o2_closure_differs == []


def test_both_rankings_run_to_the_base_closure() -> None:
    for bra in (False, True):
        for sameness in (Sameness.ANCHORED, Sameness.FREE):
            start = given(bra, sameness)
            closure = set(explore(start, 3, 12).depth)
            assert set(additions_priority(start, 3, evidence.UNCAPPED)) == closure
            assert set(changes_priority(start, 3, evidence.UNCAPPED)) == closure


def test_audit_records_each_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    def shorten(start: State, bound: int, rounds: int, by_additions: bool) -> dict[State, int]:
        depth = real_bfs(start, bound, rounds, by_additions)
        if by_additions:
            return {state: depth[state] for state in depth if state.n < bound}
        root = min(depth, key=lambda state: depth[state])
        return {root: 0}

    monkeypatch.setattr(evidence, "_bfs", shorten)
    broken = audit(False, 2, 2)
    assert broken.layer_mismatch
    assert broken.frontier_mismatch
    assert broken.differs_from_base
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "rankings_differ", lambda _depth: None)
    assert audit(False, 2, 2).additions_track_rounds == ["no witness"]
    monkeypatch.undo()

    def stop_early(start: State, bound: int, expansions: int) -> dict[State, int]:
        del expansions
        return additions_priority(start, bound, 1)

    monkeypatch.setattr(evidence, "additions_priority", stop_early)
    assert audit(False, 2, 2).o2_closure_differs


def test_write_and_check(tmp_path: Path) -> None:
    summary = write_all(tmp_path, 3, 12)
    runs = {
        (row["bra"], row["sameness"]): row
        for row in cast(list[dict[str, object]], summary["runs"])
    }
    without = runs[(False, "anchored")]
    assert without["results"] == 109
    assert without["frontier_exits"] == 700
    assert without["last_new_round"] == 10
    witness = cast(dict[str, object], without["witness"])
    assert witness["fewer_additions"] == "1:00:"
    assert witness["fewer_additions_added"] == [-1, -1]
    assert witness["fewer_additions_round"] == 2
    assert witness["sooner"] == "2:01:"
    assert witness["sooner_added"] == [0, -1]
    assert witness["sooner_round"] == 1
    with_bra = runs[(True, "anchored")]
    assert with_bra["results"] == 109
    assert with_bra["last_new_round"] == 11
    with_bra_witness = cast(dict[str, object], with_bra["witness"])
    assert with_bra_witness["fewer_additions_round"] == 3
    assert with_bra_witness["sooner_round"] == 2
    free = runs[(False, "free")]
    free_witness = cast(dict[str, object], free["witness"])
    assert free["results"] == 20
    assert free["frontier_exits"] == 112
    assert free_witness["fewer_additions"] == "1::"
    assert free_witness["fewer_additions_round"] == 2
    assert free_witness["sooner_round"] == 1
    true_free = cast(dict[str, object], runs[(True, "free")]["witness"])
    assert true_free["fewer_additions_round"] == 3
    assert true_free["sooner"] == "2::"
    capped = {row["bra"]: row for row in cast(list[dict[str, object]], summary["capped_by_round_2"])}
    assert capped[False]["expanded"] == 12
    assert capped[False]["leave"] == []
    assert len(cast(list[object], capped[False]["enter"])) == 17
    assert capped[True]["expanded"] == 11
    assert len(cast(list[object], capped[True]["leave"])) == 4
    assert len(cast(list[object], capped[True]["enter"])) == 18
    assert capped[True]["leave"] == [
        "3:01:0-1.0-2.1-0",
        "3:10:0-1.0-2.1-0",
        "3:01:0-1.1-0.2-0",
        "3:10:0-1.1-0.2-0",
    ]
    for bra, leave, enter in ((False, 5, 4), (True, 5, 3)):
        assert capped[bra]["o1_expansions_to_round_2"] == 4
        assert capped[bra]["o1_at_that_cap_is_round_2"] is True
        assert len(cast(list[object], capped[bra]["matched_leave"])) == leave
        assert len(cast(list[object], capped[bra]["matched_enter"])) == enter
    for row in runs.values():
        assert row["o2_closure_differs"] == []
    from twentieth.__main__ import main

    small = tmp_path / "small"
    write_all(small, 2, 2)
    assert main(["--out", str(small), "--check", "--bound", "2", "--rounds", "2"]) == 0
    (small / "summary.json").write_text("{}\n", encoding="utf-8", newline="\n")
    assert main(["--out", str(small), "--check", "--bound", "2", "--rounds", "2"]) == 1
    assert main(["--out", str(tmp_path / "missing"), "--check"]) == 1
