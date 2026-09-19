from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from fifth import __main__ as cli
from fifth import evidence
from fifth.changes import REMOVAL_IS_REFUSAL, Change, Kind
from fifth.evidence import (
    Plan,
    check_changes,
    check_free_cost,
    compare_with_fourth,
    destroyed,
    run_tag,
    two_term_round_count,
    write_all,
    write_census,
    write_given,
    write_reach,
    write_run,
)
from fifth.explore import Exploration, attempt, count_shortest_sequences, explore, performed
from fifth.state import MState, canonical, given
from fourth.explore import explore as explore_fourth
from xry.state import Sameness

SMALL = Plan(
    free_bound=3,
    anchored_bound=3,
    rounds=4,
    census_bound=4,
    deep_bound=3,
    deep_rounds=5,
    two_term_rounds=6,
    log_bound=2,
    log_rounds=3,
    reach_bound=3,
    reach_rounds=4,
    reach_extra=3,
    layers_upto=4,
    count_upto=3,
    count_total_upto=5,
)


def test_plan() -> None:
    assert Plan().bound(Sameness.FREE) == 5 and Plan().bound(Sameness.ANCHORED) == 4
    assert Plan().rounds == 8 and Plan().two_term_rounds == 100 and Plan().census_bound == 5
    assert Plan().runs(Sameness.FREE) == ((5, 8), (3, 12), (2, 100))
    assert SMALL.runs(Sameness.ANCHORED) == ((3, 4), (3, 5), (2, 6))
    assert run_tag(Sameness.FREE, True, 3, 4) == "bound3_rounds4_free_with_bra"
    assert [two_term_round_count(False, r) for r in range(6)] == [1, 3, 5, 6, 8, 10]
    assert [two_term_round_count(True, r) for r in range(6)] == [1, 4, 6, 7, 8, 10]


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    reach = summary["reachability"]
    census = summary["anchored_census"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(census, dict)
    assert len(runs) == 12 and len(reach) == 4 and len(census) == 2
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["answers_removing_the_obstruction"] > 0
        assert run["changes_checked"] > 0
        assert run["changes_lowering_the_round"] > 0 and run["changes_keeping_the_round"] == 0
        assert run["changes_lowering"]["terms"] > 0 and run["changes_lowering"]["a_multiplicity"] > 0
        assert run["results_with_fewer_terms_or_assertions_than_given"] > 0
        assert run["results_with_a_two_change_cycle"] == run["results"]
        assert run["results_that_reach_what_is_given"] > 1
        assert run["results_with_exact_sequence_count"] <= run["results"]
        assert run["results_containing_what_is_given"] == run["fourth_derivation_results"] < run["results"]
        assert run["statements_holding_in_every_result"] == ["at_least_one_term", "no_xrx"]
        for name in ("something_asserted", "nothing_twice", "nothing_asserted", "at_least_two_terms"):
            assert name in run["statements_that_do_not_follow"], (tag, name)
        if "anchored" in tag:
            assert "arb_asserted" in run["statements_that_do_not_follow"]
            assert run["results_with_the_names_one_term"] > 0
            assert "names_merged" in run["statements_that_do_not_follow"]
            assert run["results_that_reach_what_is_given"] == run["results"] - run["results_with_the_names_one_term"]
        else:
            assert run["results_that_reach_what_is_given"] == run["results"]
    for tag, pairs in reach.items():
        assert cli.reach_ok(pairs), tag
        assert pairs["disagreements"] == [] and pairs["reachable_under_the_fourth_seed_but_not_the_fifth"] == 0
        assert pairs["of_which_reachable_under_the_fifth_seed"] > pairs["of_which_reachable_under_the_fourth_seed"]
        if "anchored" in tag:
            assert pairs["ordered_pairs_unreachable"] > 0
        else:
            assert pairs["ordered_pairs_unreachable"] == 0
    for count in census.values():
        assert cli.census_ok(count) and count["bound_on_terms"] == 4 and count["rounds"] == 4
    two = runs["anchored/without_bra/bound2_rounds6"]
    assert two["results"] == sum(two_term_round_count(False, r) for r in range(7)) == 45
    assert two["two_term_rounds_equal_closed_form"] is True and two["two_term_sequences_equal_binomial"] is True
    assert runs["free/without_bra/bound2_rounds6"]["two_term_rounds_equal_closed_form"] is None
    assert runs["free/without_bra/bound2_rounds6"]["two_term_sequences_equal_binomial"] is None
    main = runs["anchored/without_bra/bound3_rounds4"]
    assert main["results"] == 129 and main["rounds_agreeing_with_unbounded_formula"] == [True, True]
    assert main["results_by_destroyed_givens"] == {"0": 99, "1": 25, "2": 5}
    assert main["frontier_entries"] == main["frontier_states"] * 7
    assert summary["given"] == {"listed_builds_that_are_not_builds": 0}
    assert summary["free_cost_closed_form_mismatches"] == []
    counts = summary["independent_counts"]
    assert isinstance(counts, dict) and counts["fourth_counts_are_the_lost_zero_part"] is True
    assert counts["totals"] == {"free": [1, 12, 83], "anchored": [1, 42, 698]}

    names = {p.name for p in tmp_path.iterdir()}
    for tag in ("free_without_bra", "free_with_bra", "anchored_without_bra", "anchored_with_bra"):
        for run_ in ("bound3_rounds4", "bound3_rounds5", "bound2_rounds6"):
            for stem in ("results", "added", "frontier", "rounds", "follows"):
                assert f"{stem}_{run_}_{tag}.csv" in names
        assert f"reach_bound3_rounds4_{tag}.csv" in names
        assert f"attempts_bound2_rounds3_{tag}.jsonl" in names
    assert {"given.json", "counts.csv", "summary.json", "MANIFEST.sha256"} <= names

    with (tmp_path / "results_bound3_rounds4_anchored_without_bra.csv").open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == 129 and rows[0]["state"] == "2:01:0-1*1" and rows[0]["round_first_reached"] == "0"
    assert all(row["fewest_changes_by_formula"] == row["round_first_reached"] for row in rows)
    assert {row["destroyed_givens"] for row in rows} == {"0", "1", "2"}
    assert sum(int(row["names_one_term"]) for row in rows) == 5
    assert all(row["reaches_what_is_given"] == str(1 - int(row["names_one_term"])) for row in rows)
    with (tmp_path / "attempts_bound2_rounds3_anchored_without_bra.jsonl").open(encoding="utf-8") as handle:
        records = [json.loads(line) for line in handle]
    first = records[0]
    assert first["change"] == "identify a and b" and first["obstruction"] == ["arb"] and first["kind"] == "identify two terms"
    assert [a["answer"] for a in first["answers"]] == ["refused", "remove the obstruction", "build structure"]
    assert first["answers"][1]["further"] == ["remove arb"] and first["answers"][1]["changes_performed"] == 2
    assert first["remove_the_obstruction"] is None
    loop = next(r for r in records if r["change"] == "add ara")
    assert loop["remove_the_obstruction"] == REMOVAL_IS_REFUSAL and loop["obstruction"] == ["ara"]
    removal = next(r for r in records if r["change"] == "remove arb")
    assert removal["changes_a_multiplicity_to"] == 0 and removal["outcome"] == "2:01:"
    twice = next(r for r in records if r["change"] == "add arb")
    assert twice["changes_a_multiplicity_to"] == 2
    counted = next(r for r in records if r["obstruction"] and "(" in r["obstruction"][0])
    assert counted["kind"] == "identify two terms"
    with (tmp_path / "reach_bound3_rounds4_anchored_without_bra.csv").open(encoding="utf-8", newline="") as handle:
        reach_rows = list(csv.DictReader(handle))
    assert all(row["criterion_agrees_with_search"] == "1" for row in reach_rows)
    assert any(row["fourth_results_it_reached_under_the_fourth_seed"] == "" for row in reach_rows)
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    block = given_doc["anchored/without_bra"]
    assert block["changes"] == 7 and block["of_which_obstructed"] == 3
    assert block["reaches_the_other_beginning"] and block["the_other_beginning_reaches_it"]
    assert block["reaches_the_one_term_state"] and not block["the_one_term_state_reaches_it"]
    assert block["arb_asserted_twice_reaches_what_is_given"] and block["nothing_asserted_reaches_what_is_given"]
    assert block["cost_of_nothing_asserted"] == 1 and block["cost_of_the_one_term_state"] == 2
    assert given_doc["free/with_bra"]["the_one_term_state_reaches_it"]


def test_destroyed_under_both_readings() -> None:
    assert destroyed(MState.of(2, [], (0, 1)), False) == 1 and destroyed(MState.of(2, []), False) == 1
    assert destroyed(MState.of(1, [], (0, 0)), True) == 3 and destroyed(MState.of(1, []), True) == 3


def test_check_changes_reports_disagreements() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, 4)
    edges = check_changes(expl, False)
    assert edges.checked > 0 and not edges.cost_raised_by_more_than_one and not edges.cost_rule_disagreements
    assert not edges.names_told_apart_again and edges.round_raised > edges.round_lowered > 0 == edges.round_kept
    assert set(edges.lowering) == {"a_multiplicity", "fewest_classes", "size", "terms", "total_multiplicity"}
    free = check_changes(explore(given(False, Sameness.FREE), 3, 4), False)
    assert free.checked > 0 and not free.cost_rule_disagreements
    other = check_changes(expl, True)  # the potential and the rule are about changes, not the beginning
    assert not other.cost_rule_disagreements and not other.cost_raised_by_more_than_one


def test_check_changes_sees_names_told_apart(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(given(False, Sameness.ANCHORED), 2, 3)
    monkeypatch.setattr(evidence, "names_stay_merged", lambda s, o: False)
    assert check_changes(expl, False).names_told_apart_again


def test_check_changes_reports_cost_disagreements(monkeypatch: pytest.MonkeyPatch) -> None:
    # The cost invariant and the per-change rule always hold, so their failure
    # branches never fire on correct code; force each to prove the check bites.
    expl = explore(given(False, Sameness.ANCHORED), 3, 4)
    monkeypatch.setattr(evidence, "cost_rises_by_at_most_one", lambda state, out, bra: False)
    assert check_changes(expl, False).cost_raised_by_more_than_one
    monkeypatch.setattr(evidence, "raises_by_one", lambda state, change, bra: True)
    assert check_changes(expl, False).cost_rule_disagreements


def test_check_changes_counts_a_change_that_keeps_the_round() -> None:
    # A change never keeps the round (the cost moves by exactly one); force one
    # edge to, so the step == 0 branch is exercised.
    expl = explore(given(False, Sameness.ANCHORED), 3, 4)
    state, _change, out = next(iter(performed(expl)))
    expl.depth[out] = expl.depth[state]
    assert check_changes(expl, False).round_kept > 0


def test_compare_with_fourth_notices_a_difference() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, 4)
    fourth = explore_fourth(given(False, Sameness.ANCHORED), 3, 4)
    sequences = count_shortest_sequences(expl)
    good = compare_with_fourth(expl, fourth, sequences, False)
    assert good["same_results_and_rounds_as_fourth_derivation"] and good["same_shortest_sequence_counts_as_fourth_derivation"]
    sequences[expl.start] = 5
    bad = compare_with_fourth(expl, fourth, sequences, False)
    assert bad["same_results_and_rounds_as_fourth_derivation"] and not bad["same_shortest_sequence_counts_as_fourth_derivation"]
    fourth.depth[canonical(MState.of(3, [], (0, 1)))] = 99  # not a result of the fourth seed
    assert not compare_with_fourth(expl, fourth, sequences, False)["same_results_and_rounds_as_fourth_derivation"]


def test_free_cost_check_reports_a_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    checked, mismatches = check_free_cost(2, 1)
    assert checked > 0 and mismatches == []
    monkeypatch.setattr(evidence, "cost_free", lambda state, bra: -1)
    checked, mismatches = check_free_cost(2, 1)
    assert len(mismatches) == checked


def test_two_term_binomial_check_can_fail(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    # Force the shortest-sequence counts to a wrong constant so the binomial
    # identity fails, proving the check is not vacuous.
    monkeypatch.setattr(evidence, "count_shortest_sequences", lambda expl: {state: 1 for state in expl.depth})
    run = write_run(tmp_path, Sameness.ANCHORED, False, 2, 3, SMALL)
    assert run["two_term_sequences_equal_binomial"] is False and not cli.run_ok(run)


def test_reach_reports_a_disagreement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    # Starve the graph search so it finds only the state itself; the names
    # criterion then reaches pairs the search does not, proving the
    # agreement check bites.
    monkeypatch.setattr(evidence, "reachable_in_graph", lambda graph, s: {s})
    got = write_reach(tmp_path, Sameness.FREE, False, SMALL)
    assert not got["criterion_agrees_with_search"] and got["disagreements"]
    assert not cli.reach_ok(got)


def test_write_run_and_census_and_given_and_reach_alone(tmp_path: Path) -> None:
    run = write_run(tmp_path, Sameness.FREE, True, 3, 3, SMALL)
    assert cli.run_ok(run) and run["results"] == 33
    census = write_census(Sameness.ANCHORED, True, 3, 3)
    assert cli.census_ok(census) and census["results"] != 0
    assert write_given(tmp_path) == {"listed_builds_that_are_not_builds": 0}
    reach = write_reach(tmp_path, Sameness.ANCHORED, False, Plan(reach_bound=2, reach_rounds=3, reach_extra=2))
    assert cli.reach_ok(reach) and reach["results_with_the_names_one_term"] != 0


def test_the_checks_fail_when_a_number_is_wrong() -> None:
    good: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "rounds_agreeing_with_unbounded_formula": [True],
        "two_term_rounds_equal_closed_form": None,
        "same_results_and_rounds_as_fourth_derivation": True,
        "same_shortest_sequence_counts_as_fourth_derivation": True,
        "attempts_equal_formula": True,
        "obstructed_equal_formula": True,
        "answers_reaching_something_new": [],
        "answers_removing_the_obstruction": 3,
        "cost_raised_by_more_than_one": [],
        "cost_rule_disagreements": [],
        "names_told_apart_again": [],
        "frontier_entries_are_1_plus_2N_per_state_with_N_terms": True,
        "results_with_a_two_change_cycle": 7,
        "results": 7,
        "two_term_sequences_equal_binomial": None,
        "results_that_reach_what_is_given": 5,
    }
    assert cli.run_ok(good)
    for key, wrong in (
        ("explored_equals_independent_count", False),
        ("rounds_agreeing_with_unbounded_formula", [True, False]),
        ("answers_removing_the_obstruction", 0),
        ("results_with_a_two_change_cycle", 6),
        ("results_that_reach_what_is_given", 1),
        ("cost_rule_disagreements", ["x"]),
    ):
        assert not cli.run_ok({**good, key: wrong}), key
    reach: dict[str, object] = {
        "criterion_agrees_with_search": True,
        "ordered_pairs": 4,
        "unordered_pairs_reachable_both_ways": 1,
        "fourth_reachability_implies_fifth": True,
        "ordered_pairs_of_fourth_results": 1,
    }
    assert cli.reach_ok(reach) and not cli.reach_ok({**reach, "unordered_pairs_reachable_both_ways": 0})
    census: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "same_results_and_rounds_as_fourth_derivation": True,
        "same_shortest_sequence_counts_as_fourth_derivation": True,
    }
    assert cli.census_ok(census) and not cli.census_ok({**census, "round_equals_cost_formula_for_every_result": False})
    summary: dict[str, object] = {
        "free_cost_closed_form_mismatches": [],
        "given": {"listed_builds_that_are_not_builds": 0},
        "independent_counts": {"fourth_counts_are_the_lost_zero_part": True},
    }
    assert cli.shared_ok(summary)
    assert not cli.shared_ok({**summary, "independent_counts": {"fourth_counts_are_the_lost_zero_part": False}})


def test_command_line(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    args = [
        "--out", str(tmp_path), "--free-bound", "2", "--anchored-bound", "2", "--rounds", "2",
        "--census-bound", "3", "--deep-bound", "2", "--deep-rounds", "3", "--two-term-rounds", "3",
        "--log-bound", "2", "--log-rounds", "2", "--reach-bound", "2", "--reach-rounds", "2",
        "--reach-extra", "2", "--layers-upto", "3", "--count-upto", "2", "--count-total-upto", "3",
    ]  # fmt: skip
    assert cli.main(args) == 0
    out = capsys.readouterr().out
    assert "checks pass" in out and "FAIL" not in out
    assert cli.main([*args, "--check"]) == 0
    assert "matches a fresh regeneration" in capsys.readouterr().out
    (tmp_path / "counts.csv").write_text("changed\n", encoding="utf-8")
    assert cli.main([*args, "--check"]) == 1
    assert "DIFFERS FROM" in capsys.readouterr().out


def test_a_failing_check_is_reported(tmp_path: Path, capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(cli, "run_ok", lambda run: False)
    args = [
        "--out", str(tmp_path), "--free-bound", "2", "--anchored-bound", "2", "--rounds", "1",
        "--census-bound", "0", "--deep-bound", "2", "--deep-rounds", "1", "--two-term-rounds", "1",
        "--log-bound", "2", "--log-rounds", "1", "--reach-bound", "2", "--reach-rounds", "1",
        "--reach-extra", "1", "--layers-upto", "1", "--count-upto", "1", "--count-total-upto", "1",
    ]  # fmt: skip
    assert cli.main(args) == 1
    assert "FAIL" in capsys.readouterr().out


def test_attempt_record_of_an_unobstructed_change() -> None:
    s = given(False, Sameness.ANCHORED)
    rec = evidence.attempt_record(attempt(s, Change(Kind.ADD_TERM), 3), 1)
    assert rec["adds"] == [1, 0] and rec["changes_a_multiplicity_to"] is None and rec["answers"] == []
    beyond = evidence.attempt_record(attempt(s, Change(Kind.ADD_TERM), 2), 1)
    assert beyond["beyond_bound"] and beyond["outcome"] is None


def test_exploration_awaiting_and_two_term_binomial_without_names() -> None:
    expl = explore(given(False, Sameness.FREE), 2, 3)
    assert evidence._two_term_binomial(expl, count_shortest_sequences(expl), False) is None
    hollow = Exploration(
        start=expl.start, bound=2, rounds=3, depth={expl.start: 0}, new_per_round=[1],
        attempts_per_round=[0], obstructed_per_round=[0], frontier=[],
    )  # fmt: skip
    assert hollow.awaiting == []
