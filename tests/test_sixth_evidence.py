from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from fifth.explore import count_shortest_sequences as count_shortest_sequences_fifth
from fifth.explore import explore as explore_fifth
from sixth import __main__ as cli
from sixth import evidence
from sixth.changes import Change, Kind, attempt_counts
from sixth.evidence import (
    Plan,
    check_changes,
    check_free_cost,
    compare_with_fifth,
    destroyed,
    destroyed_fifth,
    run_tag,
    two_term_round_count,
    write_all,
    write_census,
    write_counts,
    write_given,
    write_reach,
    write_run,
)
from sixth.explore import Exploration, attempt, count_shortest_sequences, explore, performed
from sixth.state import MState, canonical, given
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
    assert Plan().rounds == 8 and Plan().two_term_rounds == 20 and Plan().census_bound == 5
    assert Plan().runs(Sameness.FREE) == ((5, 8), (3, 9), (2, 20))
    assert SMALL.runs(Sameness.ANCHORED) == ((3, 4), (3, 5), (2, 6))
    assert run_tag(Sameness.FREE, True, 3, 4) == "bound3_rounds4_free_with_bra"
    assert [two_term_round_count(False, r) for r in range(8)] == [1, 6, 16, 32, 59, 98, 151, 220]
    assert [two_term_round_count(True, r) for r in range(8)] == [1, 7, 20, 41, 73, 120, 183, 264]


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    reach = summary["reachability"]
    census = summary["anchored_census"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(census, dict)
    assert len(runs) == 12 and len(reach) == 4 and len(census) == 2
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["attempts_obstructed"] == 0 and run["changes_making_some_xrx_asserted"] > 0
        assert run["results_asserting_some_xrx"] > run["results_asserting_no_xrx"]
        assert run["changes_checked"] > 0
        assert run["changes_lowering_the_round"] > 0 and run["changes_keeping_the_round"] == 0
        assert run["changes_lowering"]["terms"] > 0 and run["changes_lowering"]["no_xrx"] > 0
        assert run["results_with_fewer_terms_or_assertions_than_given"] > 0
        assert run["results_with_a_two_change_cycle"] == run["results"]
        assert run["results_that_reach_what_is_given"] > 1
        assert run["results_with_exact_sequence_count"] <= run["results"]
        assert run["results_asserting_no_xrx"] == run["fifth_derivation_results"] < run["results"]
        assert run["fifth_results_with_more_shortest_sequences"] == run["fifth_results_with_the_names_one_term"] > 0
        assert run["fifth_destroyed_givens_differ_on"] > 0
        assert run["statements_holding_in_every_result"] == ["at_least_one_term"]
        for name in ("no_xrx", "some_xrx", "something_asserted", "nothing_twice", "nothing_asserted", "at_least_two_terms"):
            assert name in run["statements_that_do_not_follow"], (tag, name)
        if "anchored" in tag:
            assert "arb_asserted" in run["statements_that_do_not_follow"]
            assert run["results_with_the_names_one_term"] > 0
            assert run["fifth_destroyed_givens_differ_exactly_on_those"] is True
            assert run["fifth_destroyed_givens_differ_on"] == run["results_with_the_names_one_term_and_crc_asserted"]
            assert run["results_that_reach_what_is_given"] == run["results"] - run["results_with_the_names_one_term"]
        else:
            assert run["fifth_destroyed_givens_differ_exactly_on_those"] is None
            assert run["results_that_reach_what_is_given"] == run["results"]
    for tag, pairs in reach.items():
        assert cli.reach_ok(pairs), tag
        assert pairs["disagreements"] == [] and pairs["fifth_criterion_disagreements"] == []
        assert pairs["ordered_pairs_with_some_xrx"] > 0 and pairs["of_which_reachable"] > 0
        if "anchored" in tag:
            assert pairs["ordered_pairs_unreachable"] > 0
        else:
            assert pairs["ordered_pairs_unreachable"] == 0
    for count in census.values():
        assert cli.census_ok(count) and count["bound_on_terms"] == 4 and count["rounds"] == 4
    two = runs["anchored/without_bra/bound2_rounds6"]
    assert two["results"] == sum(two_term_round_count(False, r) for r in range(7)) == 363
    assert two["two_term_rounds_equal_closed_form"] is True and two["two_term_sequences_equal_multinomial"] is True
    assert runs["free/without_bra/bound2_rounds6"]["two_term_rounds_equal_closed_form"] is None
    assert runs["free/without_bra/bound2_rounds6"]["two_term_sequences_equal_multinomial"] is None
    main = runs["anchored/without_bra/bound3_rounds4"]
    assert main["results"] == 386 and main["rounds_agreeing_with_unbounded_formula"] == [True, True]
    assert main["results_by_destroyed_givens"] == {"0": 290, "1": 90, "2": 6}
    assert main["frontier_entries"] == main["frontier_states"]
    assert summary["given"] == {"attempts_not_performed": 0, "beginnings_whose_xrx_count_differs_from_formula": 0}
    assert summary["free_cost_closed_form_mismatches"] == []
    counts = summary["independent_counts"]
    assert isinstance(counts, dict) and counts["fifth_counts_are_the_xrx_free_part"] is True
    assert counts["totals"] == {"free": [6, 66, 356], "anchored": [6, 252, 3024]}

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
    assert len(rows) == 386 and rows[0]["state"] == "2:01:0-1*1" and rows[0]["round_first_reached"] == "0"
    assert all(row["fewest_changes_by_formula"] == row["round_first_reached"] for row in rows)
    assert {row["destroyed_givens"] for row in rows} == {"0", "1", "2"}
    assert all(row["reaches_what_is_given"] == str(1 - int(row["names_one_term"])) for row in rows)
    assert all((row["fewest_classes"] == "") == (row["asserts_no_xrx"] == "0") for row in rows)
    assert all((row["shortest_sequences_fifth_seed"] == "") == (row["asserts_no_xrx"] == "0") for row in rows)
    merged = next(row for row in rows if row["written"].startswith("terms a (a and b are one term); asserted ara"))
    assert merged["round_first_reached"] == "1" and merged["destroyed_givens"] == "1" and merged["destroyed_givens_fifth_formula"] == "2"
    with (tmp_path / "attempts_bound2_rounds3_anchored_without_bra.jsonl").open(encoding="utf-8") as handle:
        records = [json.loads(line) for line in handle]
    first = records[0]
    assert first["change"] == "identify a and b" and first["kind"] == "identify two terms" and first["performed"]
    assert first["makes_some_xrx_asserted"] and first["outcome"] == "1:00:0-0*1"
    loop = next(r for r in records if r["change"] == "add ara")
    assert loop["makes_some_xrx_asserted"] and loop["changes_a_multiplicity_to"] == 1 and loop["outcome"] is not None
    removal = next(r for r in records if r["change"] == "remove arb")
    assert removal["changes_a_multiplicity_to"] == 0 and removal["outcome"] == "2:01:"
    assert all("obstruction" not in r and "answers" not in r for r in records)
    with (tmp_path / "reach_bound3_rounds4_anchored_without_bra.csv").open(encoding="utf-8", newline="") as handle:
        reach_rows = list(csv.DictReader(handle))
    assert all(row["criterion_agrees_with_search"] == "1" for row in reach_rows)
    assert any(row["is_a_result_of_the_fifth_seed"] == "0" and row["asserts_no_xrx"] == "0" for row in reach_rows)
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    block = given_doc["anchored/without_bra"]
    assert block["changes"] == 7 and block["of_which_make_some_xrx_asserted"] == 3 and block["of_which_obstructed"] == 0
    assert block["reaches_the_other_beginning"] and block["the_other_beginning_reaches_it"]
    assert block["reaches_the_one_term_state"] and not block["the_one_term_state_reaches_it"]
    assert block["identifying_a_and_b_gives"] == "terms a (a and b are one term); asserted ara"
    assert block["cost_of_identifying_a_and_b"] == 1 and block["fifth_formula_for_the_same_state"] == 3
    assert not block["identifying_a_and_b_reaches_what_is_given_back"]
    assert block["cost_of_adding_ara"] == 1 and block["cost_of_nothing_asserted"] == 1 and block["cost_of_the_one_term_state"] == 2
    assert given_doc["free/with_bra"]["the_one_term_state_reaches_it"]


def test_destroyed_under_both_readings() -> None:
    assert destroyed(MState.of(2, [], (0, 1)), False) == 1 and destroyed(MState.of(2, []), False) == 1
    assert destroyed(MState.of(1, [(0, 0)], (0, 0)), True) == 2 and destroyed(MState.of(1, [(0, 0)]), True) == 2
    assert destroyed_fifth(MState.of(1, [(0, 0)], (0, 0)), True) == 3 and destroyed_fifth(MState.of(1, []), True) == 3


def test_check_changes_reports_disagreements() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, 4)
    edges = check_changes(expl, False)
    assert edges.checked > 0 and not edges.cost_raised_by_more_than_one and not edges.cost_rule_disagreements
    assert not edges.names_told_apart_again and edges.round_raised > edges.round_lowered > 0 == edges.round_kept
    assert edges.xrx_made > 0
    assert set(edges.lowering) == {"a_multiplicity", "fewest_classes", "size", "terms", "total_multiplicity", "no_xrx"}
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
    # A change never keeps the round (the cost moves by an odd amount); force
    # one edge to, so the step == 0 branch is exercised.
    expl = explore(given(False, Sameness.ANCHORED), 3, 4)
    state, _change, out = next(iter(performed(expl)))
    expl.depth[out] = expl.depth[state]
    assert check_changes(expl, False).round_kept > 0


def test_compare_with_fifth_notices_a_difference() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, 4)
    fifth = explore_fifth(given(False, Sameness.ANCHORED), 3, 4)
    sequences = count_shortest_sequences(expl)
    fifth_sequences = count_shortest_sequences_fifth(fifth)
    good = compare_with_fifth(expl, fifth, sequences, fifth_sequences)
    assert good["same_results_and_rounds_as_fifth_derivation"] and good["same_shortest_sequence_counts_on_fifth_results_with_names_apart"]
    assert good["fifth_results_with_fewer_shortest_sequences"] == 0
    assert good["fifth_results_with_more_shortest_sequences"] == good["fifth_results_with_the_names_one_term"] == 5
    sequences[expl.start] = 5
    bad = compare_with_fifth(expl, fifth, sequences, fifth_sequences)
    assert bad["same_results_and_rounds_as_fifth_derivation"] and not bad["same_shortest_sequence_counts_on_fifth_results_with_names_apart"]
    sequences[expl.start] = 0
    assert compare_with_fifth(expl, fifth, sequences, fifth_sequences)["fifth_results_with_fewer_shortest_sequences"] == 1
    fifth.depth[canonical(MState.of(3, [], (0, 1)))] = 99  # not a result at that round
    assert not compare_with_fifth(expl, fifth, sequences, fifth_sequences)["same_results_and_rounds_as_fifth_derivation"]


def test_free_cost_check_reports_a_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    checked, mismatches = check_free_cost(2, 1)
    assert checked > 0 and mismatches == []
    monkeypatch.setattr(evidence, "cost_free", lambda state, bra: -1)
    checked, mismatches = check_free_cost(2, 1)
    assert len(mismatches) == checked


def test_two_term_multinomial_check_can_fail(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    # Force the shortest-sequence counts to a wrong constant so the multinomial
    # identity fails, proving the check is not vacuous.
    monkeypatch.setattr(evidence, "count_shortest_sequences", lambda expl: {state: 1 for state in expl.depth})
    run = write_run(tmp_path, Sameness.ANCHORED, False, 2, 3, SMALL)
    assert run["two_term_sequences_equal_multinomial"] is False and not cli.run_ok(run)


def test_run_sees_the_fifths_destroyed_givens_differ_elsewhere(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    # Make the fifth's formula agree everywhere: the "differ exactly on those"
    # check must then fail, and so must the "same on every result asserting no xrx" one when it disagrees.
    monkeypatch.setattr(evidence, "destroyed_fifth", evidence.destroyed)
    run = write_run(tmp_path, Sameness.ANCHORED, False, 2, 3, SMALL)
    assert run["fifth_destroyed_givens_differ_exactly_on_those"] is False and not cli.run_ok(run)
    monkeypatch.setattr(evidence, "destroyed_fifth", lambda state, bra: -1)
    run = write_run(tmp_path, Sameness.ANCHORED, False, 2, 3, SMALL)
    assert run["fifth_destroyed_givens_agree_on_every_result_asserting_no_xrx"] is False


def test_reach_reports_a_disagreement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    # Starve the graph search so it finds only the state itself; the names
    # criterion then reaches pairs the search does not, proving the
    # agreement check bites.
    monkeypatch.setattr(evidence, "reachable_in_graph", lambda graph, s: {s})
    got = write_reach(tmp_path, Sameness.FREE, False, SMALL)
    assert not got["criterion_agrees_with_search"] and got["disagreements"]
    assert not cli.reach_ok(got)


def test_reach_reports_a_disagreement_with_the_fifth(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable_fifth", lambda s, t: False)
    got = write_reach(tmp_path, Sameness.ANCHORED, False, Plan(reach_bound=2, reach_rounds=2, reach_extra=2))
    assert not got["fifth_criterion_agrees_on_fifth_results"] and got["fifth_criterion_disagreements"]
    assert not cli.reach_ok(got)


def test_counts_notice_a_difference_with_the_fifth(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "counts_by_lost_fifth", lambda s, b, n, d: {})
    assert write_counts(tmp_path, SMALL)["fifth_counts_are_the_xrx_free_part"] is False


def test_given_notices_an_attempt_not_performed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    real = attempt_counts
    monkeypatch.setattr(evidence, "attempt_counts", lambda state: (real(state)[0], real(state)[1] + 1))
    assert write_given(tmp_path)["beginnings_whose_xrx_count_differs_from_formula"] == 4


def test_write_run_and_census_and_given_and_reach_alone(tmp_path: Path) -> None:
    run = write_run(tmp_path, Sameness.FREE, True, 3, 3, SMALL)
    assert cli.run_ok(run) and run["results"] == 80
    census = write_census(Sameness.ANCHORED, True, 3, 3)
    assert cli.census_ok(census) and census["results"] != 0 and census["results_asserting_some_xrx"] != 0
    assert write_given(tmp_path) == {"attempts_not_performed": 0, "beginnings_whose_xrx_count_differs_from_formula": 0}
    reach = write_reach(tmp_path, Sameness.ANCHORED, False, Plan(reach_bound=2, reach_rounds=3, reach_extra=2))
    assert cli.reach_ok(reach) and reach["results_with_the_names_one_term"] != 0


def test_the_checks_fail_when_a_number_is_wrong() -> None:
    good: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "rounds_agreeing_with_unbounded_formula": [True],
        "two_term_rounds_equal_closed_form": None,
        "same_results_and_rounds_as_fifth_derivation": True,
        "same_shortest_sequence_counts_on_fifth_results_with_names_apart": True,
        "fifth_results_with_fewer_shortest_sequences": 0,
        "fifth_results_with_more_shortest_sequences": 2,
        "fifth_results_with_the_names_one_term": 2,
        "fifth_destroyed_givens_differ_exactly_on_those": True,
        "fifth_destroyed_givens_agree_on_every_result_asserting_no_xrx": True,
        "attempts_equal_formula": True,
        "xrx_making_equal_formula": True,
        "cost_raised_by_more_than_one": [],
        "cost_rule_disagreements": [],
        "names_told_apart_again": [],
        "changes_keeping_the_round": 0,
        "frontier_entries_are_1_per_state_with_N_terms": True,
        "results_with_a_two_change_cycle": 7,
        "results": 7,
        "two_term_sequences_equal_multinomial": None,
        "results_that_reach_what_is_given": 5,
        "results_asserting_some_xrx": 3,
    }
    assert cli.run_ok(good)
    for key, wrong in (
        ("explored_equals_independent_count", False),
        ("rounds_agreeing_with_unbounded_formula", [True, False]),
        ("fifth_results_with_more_shortest_sequences", 1),
        ("fifth_results_with_fewer_shortest_sequences", 1),
        ("changes_keeping_the_round", 1),
        ("results_with_a_two_change_cycle", 6),
        ("results_that_reach_what_is_given", 1),
        ("results_asserting_some_xrx", 0),
        ("cost_rule_disagreements", ["x"]),
    ):
        assert not cli.run_ok({**good, key: wrong}), key
    reach: dict[str, object] = {
        "criterion_agrees_with_search": True,
        "ordered_pairs": 4,
        "unordered_pairs_reachable_both_ways": 1,
        "fifth_criterion_agrees_on_fifth_results": True,
        "ordered_pairs_of_fifth_results": 1,
    }
    assert cli.reach_ok(reach) and not cli.reach_ok({**reach, "unordered_pairs_reachable_both_ways": 0})
    census: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "same_results_and_rounds_as_fifth_derivation": True,
        "same_shortest_sequence_counts_on_fifth_results_with_names_apart": True,
        "fifth_results_with_fewer_shortest_sequences": 0,
    }
    assert cli.census_ok(census) and not cli.census_ok({**census, "round_equals_cost_formula_for_every_result": False})
    summary: dict[str, object] = {
        "free_cost_closed_form_mismatches": [],
        "given": {"attempts_not_performed": 0, "beginnings_whose_xrx_count_differs_from_formula": 0},
        "independent_counts": {"fifth_counts_are_the_xrx_free_part": True},
    }
    assert cli.shared_ok(summary)
    assert not cli.shared_ok({**summary, "independent_counts": {"fifth_counts_are_the_xrx_free_part": False}})
    assert not cli.shared_ok({**summary, "given": {"attempts_not_performed": 1, "beginnings_whose_xrx_count_differs_from_formula": 0}})


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


def test_attempt_record_of_each_kind() -> None:
    s = given(False, Sameness.ANCHORED)
    rec = evidence.attempt_record(attempt(s, Change(Kind.ADD_TERM), 3), 1)
    assert rec["adds"] == [1, 0] and rec["changes_a_multiplicity_to"] is None and rec["performed"]
    beyond = evidence.attempt_record(attempt(s, Change(Kind.ADD_TERM), 2), 1)
    assert beyond["beyond_bound"] and beyond["outcome"] is None
    loop = evidence.attempt_record(attempt(s, Change(Kind.ADD_ASSERTION, 0, 0), 2), 1)
    assert loop["makes_some_xrx_asserted"] and loop["changes_a_multiplicity_to"] == 1


def test_exploration_awaiting_and_two_term_multinomial_without_names() -> None:
    expl = explore(given(False, Sameness.FREE), 2, 3)
    assert evidence._two_term_multinomial(expl, count_shortest_sequences(expl), False) is None
    hollow = Exploration(
        start=expl.start, bound=2, rounds=3, depth={expl.start: 0}, new_per_round=[1],
        attempts_per_round=[0], xrx_per_round=[0],
    )  # fmt: skip
    assert hollow.awaiting == []
