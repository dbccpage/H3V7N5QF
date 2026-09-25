"""The evidence writer, and an injection test for every disagreement branch of every check."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from ninth.explore import explore as real_ninth
from seventh.explore import explore as real_seventh
from twentysecond import evidence
from twentysecond.changes import Change, Kind, perform
from twentysecond.evidence import (
    JointCheck,
    Plan,
    audit,
    check_changes,
    check_reach,
    check_readings,
    check_results,
    check_sameness,
    compare_with_ninth,
    compare_with_seventh,
    run_tag,
    write_all,
)
from twentysecond.explore import Exploration, count_shortest_sequences, explore
from twentysecond.state import DState, empty

SMALL = Plan(
    bound=2,
    rounds=4,
    ninth_rounds=4,
    deep_bound=3,
    deep_rounds=4,
    deep_ninth_rounds=3,
    two_term_rounds=5,
    two_term_ninth_rounds=4,
    log_bound=2,
    log_rounds=2,
    reach_bound=2,
    reach_rounds=3,
    same_bound=1,
    same_total=2,
    readings_bound=2,
    readings_rounds=4,
    layers_upto=5,
    count_upto=3,
    count_total_upto=4,
    closed_form_upto=6,
)


def small() -> tuple[Exploration, dict[DState, int]]:
    expl = explore(empty(), 2, 4)
    return expl, count_shortest_sequences(expl)


def test_plan_and_tag() -> None:
    assert Plan().runs() == ((5, 8, 8), (3, 10, 9), (2, 24, 12))
    assert run_tag(3, 4) == "bound3_rounds4"


def test_audit_is_clean() -> None:
    check = audit(2, 4, 4, 1, 2)
    assert check.clean()
    assert set(check.as_dict()) == {f for f in JointCheck.__dataclass_fields__}


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    assert summary["every_check_clean"] is True
    names = {p.name for p in tmp_path.iterdir()}
    assert {"given.json", "summary.json", "counts.csv", "readings.json", "MANIFEST.sha256"} <= names
    assert "results_bound2_rounds4.csv" in names and "reach_bound2_rounds3.csv" in names
    assert "attempts_bound2_rounds2.jsonl" in names
    given = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given["the_first_change_can_only_add_a_term"] is True
    assert given["undoing"]["the_third_is_the_first_result_here"] is True
    assert given["undoing"]["ninth_sizes"] == [1, 2, 3]
    assert given["removing_ara_from_a_state_of_the_one_term_result_is_adding_asa_to_it"]["same_result"] is True
    assert given["an_addition_lowers_what_is_recorded"]["recorded_after"] == [1, 0, 0]
    assert given["the_ninth_does_not_map_one_to_one"]["one_result_here"] is True
    assert given["the_eighth_does_not_map_one_to_one"]["different_eighth_states"] is True
    assert given["the_eighth_does_not_map_one_to_one"]["one_result_here"] is True
    assert given["the_map_back"]["of_the_result_of_a_asa"] is None and given["the_map_back"]["a_asa_costs"] == 2
    assert given["two_additions_on_different_pairs_that_undo_up_to_writing"]["same_result"] is True
    runs = summary["runs"]
    assert isinstance(runs, dict)
    for run in runs.values():
        assert run["attempts_equal_formula"] and run["frontier_entries_are_1_per_state_with_N_terms"]
        assert all(run["rounds_agreeing_with_unbounded_formula"])
        assert "some_pair_in_both" in run["statements_holding_in_no_result"]
        assert "nothing_at_all" in run["statements_that_do_not_follow"]


# --- injections: each forces one disagreement and proves its branch fires ------------------


def test_round_and_cost_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    expl, seq = small()
    monkeypatch.setattr(evidence, "cost", lambda s: 5 * s.n)
    check = JointCheck()
    check_results(expl, seq, check)
    check_changes(expl, check)
    assert check.round_not_cost and check.cost_raised_by_more_than_one


def test_one_term_and_exchange_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    expl, _ = small()
    check = JointCheck()
    check_results(expl, {s: 2 for s in expl.depth}, check)
    assert check.one_term_not_one_sequence
    monkeypatch.setattr(evidence, "swap", lambda s: s)
    check = JointCheck()
    check_results(expl, count_shortest_sequences(expl), check)
    assert check.exchange_mismatch and not check.one_term_not_one_sequence


def test_undo_branch(monkeypatch: pytest.MonkeyPatch) -> None:
    expl, seq = small()

    def twice(state: DState, x: int, y: int) -> DState:
        return perform(perform(state, Change(Kind.ADD_ASSERTION, "r", x, y)), Change(Kind.ADD_ASSERTION, "r", x, y))

    monkeypatch.setattr(evidence, "add_r_then_s", twice)
    check = JointCheck()
    check_results(expl, seq, check)
    assert check.undo_failed


def test_count_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    expl, seq = small()
    monkeypatch.setattr(evidence, "counts_within", lambda _b, _r: {})
    monkeypatch.setattr(evidence, "two_term_round_count", lambda _r: -1)
    check = JointCheck()
    check_results(expl, seq, check)
    assert check.count_mismatch and check.two_term_mismatch


def test_one_term_bound_skips_the_two_term_form() -> None:
    expl = explore(empty(), 1, 3)
    check = JointCheck()
    check_results(expl, count_shortest_sequences(expl), check)
    assert check.clean()


def test_change_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    expl, _ = small()
    monkeypatch.setattr(evidence, "predicted_move", lambda _s, _c: (9, 9))
    monkeypatch.setattr(evidence, "is_addition", lambda _c: False)
    monkeypatch.setattr(evidence, "result_changes", lambda _s: ())
    check = JointCheck()
    block = check_changes(expl, check)
    assert check.record_move_mismatch and check.raising_not_addition and check.removal_outside
    assert block["removals_from_states_not_plain_checked"]


def test_seventh_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    expl, seq = small()

    def fewer(start: Any, bound: int, rounds: int = 100, keep_log: bool = False) -> Any:
        return real_seventh(start, bound, rounds - 1, keep_log)

    monkeypatch.setattr(evidence, "explore_seventh", fewer)
    monkeypatch.setattr(evidence, "count_shortest_sequences_seventh", lambda e: {m: 0 for m in e.depth})
    monkeypatch.setattr(evidence, "read_back", lambda _s: None)
    monkeypatch.setattr(evidence, "smallest_none", lambda _e: None)
    check = JointCheck()
    block = compare_with_seventh(expl, seq, check)
    assert check.seventh_mismatch and check.read_back_mismatch
    assert block["first_result_answered_none"] is None and block["its_round"] is None


def test_ninth_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    expl, _ = small()
    check = JointCheck()
    compare_with_ninth(expl, 6, check)
    assert any("image of" in m for m in check.ninth_mismatch)
    monkeypatch.setattr(evidence, "is_plain", lambda _g: True)
    check = JointCheck()
    compare_with_ninth(expl, 4, check)
    assert any("round is not its cost" in m for m in check.ninth_mismatch)
    monkeypatch.setattr(evidence, "is_plain", lambda _g: False)
    check = JointCheck()
    compare_with_ninth(expl, 4, check)
    assert any("at the round of their cost" in m for m in check.ninth_mismatch)


def test_ninth_branch_with_nothing_taken(monkeypatch: pytest.MonkeyPatch) -> None:
    expl, _ = small()

    class Nothing:
        depth: dict[DState, int] = {}

    monkeypatch.setattr(evidence, "explore_ninth", lambda _s, _b, _r: Nothing())
    check = JointCheck()
    block, taken = compare_with_ninth(expl, 4, check)
    assert check.ninth_mismatch and block["most_ninth_results_taken_in_by_one_result"] == 0 and taken == {}


def test_ninth_fewer_rounds(monkeypatch: pytest.MonkeyPatch) -> None:
    expl, _ = small()

    def fewer(start: Any, bound: int, rounds: int = 100, keep_log: bool = False) -> Any:
        return real_ninth(start, bound, rounds - 1, keep_log)

    monkeypatch.setattr(evidence, "explore_ninth", fewer)
    check = JointCheck()
    compare_with_ninth(expl, 4, check)
    assert check.ninth_mismatch


def test_reach_branch(monkeypatch: pytest.MonkeyPatch) -> None:
    expl, _ = small()
    monkeypatch.setattr(evidence, "reachable", lambda _s, _t: True)
    check = JointCheck()
    check_reach(expl, check)
    assert check.reach_mismatch


def test_sameness_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    check = JointCheck()
    block = check_sameness(2, 2, check)
    assert check.clean() and block["classes"] == block["results"]
    monkeypatch.setattr(evidence, "same", lambda s, t: s == t)
    check = JointCheck()
    check_sameness(1, 2, check)
    assert any("joined but not" in m for m in check.sameness_mismatch)


def test_sameness_not_joined(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "result_of", lambda _s: DState(0, (), ()))
    check = JointCheck()
    check_sameness(1, 1, check)
    assert any("not joined" in m for m in check.sameness_mismatch)


def test_readings_branches(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "cost_j2", lambda _k: -1)
    monkeypatch.setattr(evidence, "round_count_j2", lambda _k, _b: -1)
    monkeypatch.setattr(evidence, "cost_j3", lambda _s: -1)
    monkeypatch.setattr(evidence, "count_j3", lambda _n, _d: [])
    monkeypatch.setattr(evidence, "padding_witness", lambda _k: (DState(1, (0,), (0,)), DState(1, (0,), (0,)), 0))
    check = JointCheck()
    check_readings(2, 3, check)
    joined = " ".join(check.readings_mismatch)
    for part in ("C-J2 round of", "C-J2 round 0", "C-J3 round of", "orbit count", "padding witness"):
        assert part in joined
