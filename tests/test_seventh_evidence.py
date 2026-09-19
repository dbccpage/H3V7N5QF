from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from seventh import __main__ as cli
from seventh import evidence
from seventh.changes import Change, Kind
from seventh.evidence import (
    Plan,
    check_changes,
    compare_with_sixth,
    one_term_sequences,
    run_tag,
    sixth_ok,
    write_all,
    write_census,
    write_counts,
    write_given,
    write_reach,
    write_run,
)
from seventh.explore import attempt, count_shortest_sequences, explore, performed
from seventh.state import MState, canonical, empty

SMALL = Plan(
    bound=3,
    rounds=5,
    census_bound=4,
    census_rounds=5,
    deep_bound=3,
    deep_rounds=6,
    two_term_rounds=7,
    log_bound=2,
    log_rounds=3,
    reach_bound=3,
    reach_rounds=5,
    reach_extra=2,
    layers_upto=4,
    count_upto=3,
    count_total_upto=5,
)


def test_plan() -> None:
    assert Plan().bound == 5 and Plan().rounds == 11 and Plan().census_bound == 6 and Plan().two_term_rounds == 40
    assert Plan().runs() == ((5, 11), (3, 14), (2, 40)) and SMALL.runs() == ((3, 5), (3, 6), (2, 7))
    assert run_tag(3, 4) == "bound3_rounds4" and evidence.SIXTH_ROUNDS_FEWER == 4


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    reach = summary["reachability"]
    census = summary["census"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(census, dict)
    assert list(runs) == ["bound3_rounds5", "bound3_rounds6", "bound2_rounds7"] and list(census) == ["bound4_rounds5"]
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["attempts_obstructed"] == 0 and run["changes_making_some_xrx_asserted"] > 0
        assert run["results_with_a_term"] == run["results"] - 1 == run["results_with_a_two_change_cycle"]
        assert run["changes_lowering_the_round"] > 0 and run["changes_keeping_the_round"] == 0
        assert set(run["changes_lowering"]) == {"a_multiplicity", "fewest_classes", "size", "terms", "total_multiplicity", "no_xrx"}
        assert run["results_that_reach_what_is_given"] == 1 and run["results_reached_from_what_is_given"] == run["results"]
        assert run["statements_holding_in_every_result"] == []
        for name in ("no_xrx", "some_xrx", "something_asserted", "nothing_asserted", "at_least_one_term", "nothing_at_all"):
            assert name in run["statements_that_do_not_follow"], (tag, name)
        assert run["frontier_entries"] == run["frontier_states"] > 0
        assert run["results_with_exact_sequence_count"] == run["results"] and run["one_term_results_have_one_shortest_sequence"]
        sixth = run["sixth_derivation"]
        assert isinstance(sixth, dict) and set(sixth) == {"without_bra", "with_bra"}
        for block in sixth.values():
            assert sixth_ok(block) and block["sixth_results_any_rewriting"] > 0 and block["sixth_results_names_forgotten"] > 0
    two = runs["bound2_rounds7"]
    assert two["results"] == 74 and two["two_term_rounds_equal_closed_form"] is True
    assert two["results_by_terms"] == {"0": 1, "1": 7, "2": 66}
    assert runs["bound3_rounds5"]["two_term_rounds_equal_closed_form"] is None
    main = runs["bound3_rounds5"]
    assert main["results"] == 38 and main["rounds_agreeing_with_unbounded_formula"] == [True, True, True, True]
    assert main["the_first_round_is_the_one_term_state_alone"] is True
    deep = runs["bound3_rounds6"]
    assert deep["results"] == 89 and deep["rounds_agreeing_with_unbounded_formula"] == [True, True, True, True]
    assert cli.reach_ok(reach) and reach["disagreements"] == [] and reach["sixth_criterion_disagreements"] == []
    assert reach["ordered_pairs_unreachable"] == reach["results"] - 1 == reach["results_with_a_term"]
    assert reach["results_that_reach_what_is_given"] == 1
    for count in census.values():
        assert cli.census_ok(count) and count["bound_on_terms"] == 4 and count["rounds"] == 5 and count["results"] == 41
    assert cli.shared_ok(summary)
    assert summary["given"] == {"changes_on_the_empty_state": 1, "of_which_add_a_term": 1, "attempts_not_performed": 0}
    counts = summary["independent_counts"]
    assert isinstance(counts, dict) and counts["two_term_closed_form_mismatches"] == []
    assert counts["sixth_counts_by_destroyed_givens_add_up_to_these"] is True and counts["totals_by_terms"] == [1, 6, 66, 356]
    assert summary["attempts_in_full_log"] == 1 + 2 + (6 + 3)

    names = {p.name for p in tmp_path.iterdir()}
    for run_ in ("bound3_rounds5", "bound3_rounds6", "bound2_rounds7"):
        for stem in ("results", "added", "frontier", "rounds", "follows"):
            assert f"{stem}_{run_}.csv" in names
    assert {"reach_bound3_rounds5.csv", "attempts_bound2_rounds3.jsonl", "given.json", "counts.csv", "summary.json", "MANIFEST.sha256"} <= names

    with (tmp_path / "results_bound3_rounds5.csv").open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == 38 and rows[0]["state"] == "0::" and rows[0]["written"] == "no terms; asserted nothing"
    assert rows[0]["round_first_reached"] == "0" and rows[0]["is_a_result_of_the_sixth_seed"] == "0"
    assert rows[0]["sixth_seed_cost_without_bra"] == "" and rows[0]["reaches_what_is_given"] == "1"
    assert rows[1]["written"] == "terms a; asserted nothing" and rows[1]["round_first_reached"] == "1"
    assert rows[1]["sixth_seed_cost_without_bra"] == "2" and rows[1]["sixth_seed_cost_with_bra"] == "3"
    assert all(row["fewest_changes_by_formula"] == row["round_first_reached"] for row in rows)
    assert all(row["reaches_what_is_given"] == str(1 - int(row["has_a_term"])) for row in rows)
    assert all(row["reached_from_what_is_given"] == "1" for row in rows)
    assert all((row["fewest_classes"] == "") == (row["asserts_no_xrx"] == "0") for row in rows)
    assert all(row["shortest_sequences_exact_within_bound"] == "1" for row in rows)
    with (tmp_path / "attempts_bound2_rounds3.jsonl").open(encoding="utf-8") as handle:
        records = [json.loads(line) for line in handle]
    first = records[0]
    assert first["state"] == "0::" and first["change"] == "add a term" and first["kind"] == "add a term" and first["performed"]
    assert first["outcome"] == "1::" and first["adds"] == [1, 0] and first["changes_a_multiplicity_to"] is None
    loop = next(r for r in records if r["change"] == "add ara")
    assert loop["makes_some_xrx_asserted"] and loop["changes_a_multiplicity_to"] == 1
    removal = next(r for r in records if r["change"].startswith("remove"))
    assert removal["changes_a_multiplicity_to"] == 0
    assert any(r["beyond_bound"] and r["outcome"] is None for r in records)
    assert all("obstruction" not in r and "answers" not in r for r in records)
    with (tmp_path / "reach_bound3_rounds5.csv").open(encoding="utf-8", newline="") as handle:
        reach_rows = list(csv.DictReader(handle))
    assert all(row["criterion_agrees_with_search"] == "1" for row in reach_rows)
    assert reach_rows[0]["has_a_term"] == "0" and reach_rows[0]["results_reaching_it"] == "1"
    with (tmp_path / "rounds_bound2_rounds7.csv").open(encoding="utf-8", newline="") as handle:
        round_rows = list(csv.DictReader(handle))
    assert [r["new_results_with_two_terms_by_closed_form"] for r in round_rows] == ["1", "1", "2", "3", "7", "11", "20", "29"]
    assert [r["new_results_without_bound_by_formula"] for r in round_rows][:5] == ["1", "1", "2", "4", "10"]
    assert round_rows[5]["new_results_without_bound_by_formula"] == ""  # beyond layers_upto
    with (tmp_path / "counts.csv").open(encoding="utf-8", newline="") as handle:
        count_rows = list(csv.DictReader(handle))
    assert count_rows[0] == {"terms": "0", "total_multiplicity": "0", "results": "1", "results asserting no xrx": "1", "results by the two-term closed form": ""}
    assert any(r["terms"] == "2" and r["results by the two-term closed form"] == r["results"] != "" for r in count_rows)
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given_doc["changes"] == ["add a term"] and given_doc["the_first_change_can_only_add_a_term"]
    assert given_doc["results_after_one_change"] == ["terms a; asserted nothing"]
    assert given_doc["reaches_the_one_term_state"] and not given_doc["the_one_term_state_reaches_it"]
    assert not given_doc["reaches_itself_in_two_changes"] and given_doc["cost_of_the_one_term_state"] == 1
    assert given_doc["the_sixth_seeds_beginnings_seen_from_here"]["without_bra"] == {"state": "terms a b; asserted arb", "cost_here": 3, "cost_under_the_sixth_seed": 0}
    assert given_doc["the_one_term_state_under_the_sixth_seed"] == {"without_bra": 2, "with_bra": 3}
    assert given_doc["the_empty_state_under_the_sixth_seed"] is None


def test_write_run_with_zero_rounds_and_census_off(tmp_path: Path) -> None:
    run = write_run(tmp_path, 2, 0, SMALL)
    assert run["results"] == 1 and run["the_first_round_is_the_one_term_state_alone"] is None
    assert run["rounds_agreeing_with_unbounded_formula"] == [True] and run["changes_checked"] == 0
    assert not cli.run_ok(run)  # no result with a term, nothing checked: the checks do not pass vacuously
    summary = write_all(tmp_path, Plan(bound=2, rounds=2, census_bound=0, deep_bound=2, deep_rounds=2, two_term_rounds=2, log_bound=2, log_rounds=1, reach_bound=2, reach_rounds=2, reach_extra=1, layers_upto=2, count_upto=2, count_total_upto=2))
    assert summary["census"] == {}


def test_check_changes_reports_every_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 3, 4)
    edges = check_changes(expl)
    assert edges.checked > 0 and not edges.cost_raised_by_more_than_one and not edges.size_not_moved_by_one
    assert not edges.cost_rule_disagreements and not edges.term_lost
    assert edges.round_raised > edges.round_lowered > 0 == edges.round_kept and edges.xrx_made > 0
    # The cost invariant, the size step and the per-change rule always hold, so
    # their failure branches never fire on correct code; force each to prove the check bites.
    big = MState.of(1, [(0, 0)] * 5)
    monkeypatch.setattr(evidence, "perform", lambda state, change: big)
    forced = check_changes(expl)
    assert forced.cost_raised_by_more_than_one and forced.size_not_moved_by_one and forced.cost_rule_disagreements
    monkeypatch.setattr(evidence, "term_stays", lambda s, o: False)
    assert check_changes(expl).term_lost


def test_check_changes_counts_a_change_that_keeps_the_round() -> None:
    # A change never keeps the round (the size moves by one); force one edge to,
    # so the step == 0 branch is exercised.
    expl = explore(empty(), 3, 4)
    state, _change, out = next(iter(performed(expl)))
    expl.depth[out] = expl.depth[state]
    assert check_changes(expl).round_kept > 0


def test_one_term_sequences_can_fail() -> None:
    expl = explore(empty(), 2, 4)
    sequences = count_shortest_sequences(expl)
    assert one_term_sequences(expl, sequences)
    sequences[MState.of(1, [])] = 2
    assert not one_term_sequences(expl, sequences)


def test_compare_with_sixth_notices_every_difference(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 3, 6)
    good = compare_with_sixth(expl, False)
    assert sixth_ok(good) and good["sixth_rounds"] == 2 and good["results_with_a_term_of_small_size"] == 1
    assert good["results_where_the_sixth_cost_equals_the_cost"] == 0
    with_bra = compare_with_sixth(expl, True)
    assert sixth_ok(with_bra) and with_bra["results_with_a_term_of_small_size"] == 0
    with pytest.raises(ValueError):
        compare_with_sixth(explore(empty(), 1, 3), False)
    shallow = explore(empty(), 2, 3)
    assert compare_with_sixth(shallow, True)["sixth_rounds"] == 0
    # Drop a result the sixth has: the sets differ and the forgotten results are no longer all results.
    del expl.depth[MState.of(1, [])]
    bad = compare_with_sixth(expl, False)
    assert not bad["same_results_as_sixth_derivation_any_rewriting"] and not bad["sixth_results_names_forgotten_are_results"]
    assert not sixth_ok(bad)
    # Make every result cheap under the sixth's formula: the rounds no longer agree.
    monkeypatch.setattr(evidence, "cost_sixth", lambda s, b: 0)
    worse = compare_with_sixth(explore(empty(), 3, 6), False)
    assert not worse["sixth_round_is_its_cost_formula_on_every_shared_result"] and not sixth_ok(worse)
    # Forget the names into a state the seventh never explores: the small results are not among them.
    monkeypatch.setattr(evidence, "forget_names", lambda s: MState.of(1, [(0, 0)] * 9))
    off = compare_with_sixth(explore(empty(), 3, 6), False)
    assert not off["results_with_a_term_of_small_size_are_sixth_results_names_forgotten"] and not sixth_ok(off)


def test_reach_reports_a_disagreement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    # Starve the graph search so it finds only the state itself; the criterion
    # then reaches pairs the search does not, proving the agreement check bites.
    monkeypatch.setattr(evidence, "reachable_in_graph", lambda graph, s: {s})
    got = write_reach(tmp_path, SMALL)
    assert not got["criterion_agrees_with_search"] and got["disagreements"] and not cli.reach_ok(got)


def test_reach_reports_a_disagreement_with_the_sixth(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable_sixth", lambda s, t: False)
    got = write_reach(tmp_path, Plan(reach_bound=2, reach_rounds=3, reach_extra=1))
    assert not got["sixth_criterion_agrees_on_results_with_a_term"] and got["sixth_criterion_disagreements"]
    assert not cli.reach_ok(got)


def test_counts_notice_a_wrong_closed_form_or_a_difference_with_the_sixth(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "two_term_count", lambda t: 0)
    counts = write_counts(tmp_path, SMALL)
    assert counts["two_term_closed_form_mismatches"] == [f"2/{t}" for t in range(6)]
    monkeypatch.setattr(evidence, "counts_upto_sixth", lambda s, b, n, d: [])
    assert write_counts(tmp_path, SMALL)["sixth_counts_by_destroyed_givens_add_up_to_these"] is False


def test_given_notices_an_attempt_not_performed_or_another_first_change(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "first_changes", lambda: (Change(Kind.ADD_TERM), Change(Kind.ADD_TERM)))
    given = write_given(tmp_path)
    assert given["changes_on_the_empty_state"] == 2 and given["of_which_add_a_term"] == 2
    assert not json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))["the_first_change_can_only_add_a_term"]


def test_write_census_alone() -> None:
    census = write_census(3, 4)
    assert cli.census_ok(census) and census["results"] == 17 and census["results_asserting_some_xrx"] == 9
    assert census["frontier_entries"] == census["frontier_states"] and census["results_of_the_last_round_whose_changes_await"] == 9


def test_the_checks_fail_when_a_number_is_wrong() -> None:
    block: dict[str, object] = {
        "same_results_as_sixth_derivation_any_rewriting": True,
        "sixth_round_is_its_cost_formula_on_every_shared_result": True,
        "sixth_results_names_forgotten_are_results": True,
        "results_with_a_term_of_small_size_are_sixth_results_names_forgotten": True,
    }
    good: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "rounds_agreeing_with_unbounded_formula": [True],
        "two_term_rounds_equal_closed_form": None,
        "the_first_round_is_the_one_term_state_alone": True,
        "attempts_equal_formula": True,
        "xrx_making_equal_sixth_formula": True,
        "cost_raised_by_more_than_one": [],
        "size_not_moved_by_one": [],
        "cost_rule_disagreements": [],
        "term_lost": [],
        "changes_keeping_the_round": 0,
        "frontier_entries_are_1_per_state_with_N_terms": True,
        "results_with_a_two_change_cycle": 6,
        "results_with_a_term": 6,
        "results": 7,
        "results_with_exact_sequence_count": 7,
        "one_term_results_have_one_shortest_sequence": True,
        "results_that_reach_what_is_given": 1,
        "results_reached_from_what_is_given": 7,
        "statements_holding_in_every_result": [],
        "sixth_derivation": {"without_bra": block, "with_bra": block},
    }
    assert cli.run_ok(good)
    for key, wrong in (
        ("explored_equals_independent_count", False),
        ("rounds_agreeing_with_unbounded_formula", [True, False]),
        ("the_first_round_is_the_one_term_state_alone", False),
        ("changes_keeping_the_round", 1),
        ("results_with_a_two_change_cycle", 5),
        ("results_that_reach_what_is_given", 2),
        ("statements_holding_in_every_result", ["at_least_one_term"]),
        ("size_not_moved_by_one", ["x"]),
        ("sixth_derivation", {"without_bra": {**block, "sixth_results_names_forgotten_are_results": False}}),
    ):
        assert not cli.run_ok({**good, key: wrong}), key
    reach: dict[str, object] = {
        "criterion_agrees_with_search": True,
        "ordered_pairs": 4,
        "unordered_pairs_reachable_both_ways": 1,
        "results_that_reach_what_is_given": 1,
        "sixth_criterion_agrees_on_results_with_a_term": True,
        "ordered_pairs_of_results_with_a_term": 1,
    }
    assert cli.reach_ok(reach) and not cli.reach_ok({**reach, "results_that_reach_what_is_given": 2})
    census: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "sixth_derivation": {"without_bra": block},
    }
    assert cli.census_ok(census) and not cli.census_ok({**census, "round_equals_cost_formula_for_every_result": False})
    summary: dict[str, object] = {
        "given": {"changes_on_the_empty_state": 1, "of_which_add_a_term": 1, "attempts_not_performed": 0},
        "independent_counts": {"two_term_closed_form_mismatches": [], "sixth_counts_by_destroyed_givens_add_up_to_these": True},
    }
    assert cli.shared_ok(summary)
    assert not cli.shared_ok({**summary, "given": {"changes_on_the_empty_state": 2, "of_which_add_a_term": 1, "attempts_not_performed": 0}})
    assert not cli.shared_ok({**summary, "independent_counts": {"two_term_closed_form_mismatches": ["2/3"], "sixth_counts_by_destroyed_givens_add_up_to_these": True}})


def test_command_line(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    args = [
        "--out", str(tmp_path), "--bound", "2", "--rounds", "5", "--census-bound", "3", "--census-rounds", "4",
        "--deep-bound", "2", "--deep-rounds", "5", "--two-term-rounds", "5", "--log-bound", "2", "--log-rounds", "2",
        "--reach-bound", "2", "--reach-rounds", "3", "--reach-extra", "2", "--layers-upto", "3",
        "--count-upto", "2", "--count-total-upto", "3",
    ]  # fmt: skip
    assert cli.main(args) == 0
    out = capsys.readouterr().out
    assert "checks pass" in out and "FAIL" not in out and "census bound3_rounds4" in out
    assert cli.main([*args, "--check"]) == 0
    assert "matches a fresh regeneration" in capsys.readouterr().out
    (tmp_path / "counts.csv").write_text("changed\n", encoding="utf-8")
    assert cli.main([*args, "--check"]) == 1
    assert "DIFFERS FROM" in capsys.readouterr().out


def test_a_failing_check_is_reported(tmp_path: Path, capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(cli, "run_ok", lambda run: False)
    args = [
        "--out", str(tmp_path), "--bound", "2", "--rounds", "2", "--census-bound", "0", "--deep-bound", "2",
        "--deep-rounds", "2", "--two-term-rounds", "2", "--log-bound", "2", "--log-rounds", "1", "--reach-bound", "2",
        "--reach-rounds", "2", "--reach-extra", "1", "--layers-upto", "2", "--count-upto", "1", "--count-total-upto", "1",
    ]  # fmt: skip
    assert cli.main(args) == 1
    assert "FAIL" in capsys.readouterr().out


def test_attempt_record_of_each_kind() -> None:
    s = MState.of(2, [(0, 1)])
    rec = evidence.attempt_record(attempt(s, Change(Kind.ADD_TERM), 3), 1)
    assert rec["adds"] == [1, 0] and rec["changes_a_multiplicity_to"] is None and rec["performed"] and rec["kind"] == "add a term"
    beyond = evidence.attempt_record(attempt(s, Change(Kind.ADD_TERM), 2), 1)
    assert beyond["beyond_bound"] and beyond["outcome"] is None
    removal = evidence.attempt_record(attempt(s, Change(Kind.REMOVE, 0, 1), 2), 1)
    assert removal["changes_a_multiplicity_to"] == 0 and removal["outcome"] == canonical(MState.of(2, [])).key()
    merge = evidence.attempt_record(attempt(s, Change(Kind.IDENTIFY, 0, 1), 2), 1)
    assert merge["makes_some_xrx_asserted"] and merge["changes_a_multiplicity_to"] is None
    start = evidence.attempt_record(attempt(empty(), Change(Kind.ADD_TERM), 2), 1)
    assert start["written"] == "no terms; asserted nothing" and start["outcome"] == "1::"
