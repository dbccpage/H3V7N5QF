from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from eighth.orbits import count_free
from ninth import __main__ as cli
from ninth import evidence
from ninth.changes import Change, Kind
from ninth.evidence import (
    Plan,
    check_changes,
    compare_with_eighth,
    compare_with_seventh,
    eighth_ok,
    one_term_binomial,
    run_tag,
    seventh_ok,
    write_all,
    write_census,
    write_counts,
    write_given,
    write_reach,
    write_run,
)
from ninth.explore import Attempt, Exploration, attempt, count_shortest_sequences, explore, performed
from ninth.state import DState, canonical, empty

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
    assert Plan().bound == 5 and Plan().rounds == 8 and Plan().census_bound == 6 and Plan().two_term_rounds == 12
    assert Plan().runs() == ((5, 8), (3, 9), (2, 12)) and SMALL.runs() == ((3, 5), (3, 6), (2, 7))
    assert run_tag(3, 4) == "bound3_rounds4" and evidence.EIGHTH_ROUNDS_FEWER == 4


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    reach = summary["reachability"]
    census = summary["census"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(census, dict)
    assert list(runs) == ["bound3_rounds5", "bound3_rounds6", "bound2_rounds7"] and list(census) == ["bound4_rounds5"]
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["attempts_obstructed"] == 0 and run["changes_making_some_xsx_asserted"] > 0
        assert run["results_with_a_term"] == run["results"] - 1 == run["results_with_a_two_change_cycle"]
        assert run["changes_lowering_the_round"] > 0 and run["changes_keeping_the_round"] == 0
        assert set(run["changes_lowering"]) == {
            "a_multiplicity",
            "fewest_classes_r",
            "fewest_classes_s",
            "no_xrx",
            "no_xsx",
            "size",
            "terms",
            "total_r",
            "total_s",
        }
        assert run["results_that_reach_what_is_given"] == 1 and run["results_reached_from_what_is_given"] == run["results"]
        assert run["statements_holding_in_every_result"] == []
        for name in (
            "no_xrx_r",
            "no_xrx_s",
            "some_xrx_r",
            "something_asserted_s",
            "at_least_one_term_r",
            "nothing_at_all",
            "nothing_in_s",
            "unchanged_by_exchange",
        ):
            assert name in run["statements_that_do_not_follow"], (tag, name)
        assert run["frontier_entries"] == run["frontier_states"] > 0
        assert run["results_with_exact_sequence_count"] == run["results"] and run["one_term_results_follow_the_binomial"]
        assert run["one_term_results_with_more_than_one_shortest_sequence"] > 0
        seventh = run["seventh_derivation"]
        assert isinstance(seventh, dict) and seventh_ok(seventh)
        eighth = run["eighth_derivation"]
        assert isinstance(eighth, dict) and set(eighth) == {"without_bra", "with_bra"}
        for block in eighth.values():
            assert eighth_ok(block) and block["eighth_results_any_rewriting"] > 0 and block["eighth_results_names_forgotten"] > 0
    two = runs["bound2_rounds7"]
    assert two["results"] == 680 and two["two_term_rounds_equal_closed_form"] is True
    assert two["results_by_terms"] == {"0": 1, "1": 28, "2": 651}
    assert runs["bound3_rounds5"]["two_term_rounds_equal_closed_form"] is None
    main = runs["bound3_rounds5"]
    assert main["results"] == 140 and main["rounds_agreeing_with_unbounded_formula"] == [True, True, True, True]
    assert main["the_first_round_is_the_one_term_state_alone"] is True
    deep = runs["bound3_rounds6"]
    assert deep["results"] == 518 and deep["rounds_agreeing_with_unbounded_formula"] == [True, True, True, True]
    assert cli.reach_ok(reach) and reach["disagreements"] == [] and reach["seventh_criterion_disagreements"] == []
    assert reach["eighth_criterion_disagreements"] == []
    assert reach["ordered_pairs_unreachable"] == reach["results"] - 1 == reach["results_with_a_term"]
    assert reach["results_that_reach_what_is_given"] == 1
    for count in census.values():
        assert cli.census_ok(count) and count["bound_on_terms"] == 4 and count["rounds"] == 5 and count["results"] == 145
    assert cli.shared_ok(summary)
    assert summary["given"] == {"changes_on_the_empty_state": 1, "of_which_add_a_term": 1, "attempts_not_performed": 0}
    counts = summary["independent_counts"]
    assert isinstance(counts, dict) and counts["two_term_closed_form_mismatches"] == []
    assert counts["eighth_counts_by_destroyed_givens_add_up_to_these"] is True
    assert counts["product_equals_count_for_at_most_one_term"] and counts["count_exceeds_product_for_two_or_more_terms"]
    assert counts["totals_by_terms"] == [1, 21, 651, 5715]
    assert summary["attempts_in_full_log"] == 22

    names = {p.name for p in tmp_path.iterdir()}
    for run_ in ("bound3_rounds5", "bound3_rounds6", "bound2_rounds7"):
        for stem in ("results", "added", "frontier", "rounds", "follows"):
            assert f"{stem}_{run_}.csv" in names
    assert {"reach_bound3_rounds5.csv", "attempts_bound2_rounds3.jsonl", "given.json", "counts.csv", "summary.json", "MANIFEST.sha256"} <= names

    with (tmp_path / "results_bound3_rounds5.csv").open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == 140 and rows[0]["state"] == "0::|" and rows[0]["written"] == "no terms; asserted nothing"
    assert rows[0]["round_first_reached"] == "0" and rows[0]["is_a_result_of_the_eighth_seed"] == "0"
    assert rows[0]["eighth_seed_cost_without_bra"] == "" and rows[0]["reaches_what_is_given"] == "1"
    assert rows[1]["written"] == "terms a; asserted nothing" and rows[1]["round_first_reached"] == "1"
    assert rows[1]["eighth_seed_cost_without_bra"] == "2" and rows[1]["eighth_seed_cost_with_bra"] == "3"
    assert all(row["fewest_changes_by_formula"] == row["round_first_reached"] for row in rows)
    assert all(row["reaches_what_is_given"] == str(1 - int(row["has_a_term"])) for row in rows)
    assert all(row["reached_from_what_is_given"] == "1" for row in rows)
    assert all((row["fewest_classes_r"] == "") == (row["asserts_no_xrx"] == "0") for row in rows)
    assert all((row["fewest_classes_s"] == "") == (row["asserts_no_xsx"] == "0") for row in rows)
    assert all(row["shortest_sequences_exact_within_bound"] == "1" for row in rows)
    assert all(int(row["seventh_seed_cost_of_the_r_part"]) + int(row["assertions_in_s"]) == int(row["fewest_changes_by_formula"]) for row in rows)
    with (tmp_path / "attempts_bound2_rounds3.jsonl").open(encoding="utf-8") as handle:
        records = [json.loads(line) for line in handle]
    first = records[0]
    assert first["state"] == "0::|" and first["change"] == "add a term" and first["kind"] == "add a term" and first["performed"]
    assert first["outcome"] == "1::|" and first["adds"] == [1, 0] and first["changes_a_multiplicity_to"] is None
    loop = next(r for r in records if r["change"] == "add ara")
    assert loop["makes_some_xrx_asserted"] and loop["changes_a_multiplicity_to"] == 1 and loop["relation"] == "r"
    loop_s = next(r for r in records if r["change"] == "add asa")
    assert loop_s["makes_some_xsx_asserted"] and not loop_s["makes_some_xrx_asserted"] and loop_s["relation"] == "s"
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
    assert [r["new_results_with_two_terms_by_closed_form"] for r in round_rows] == ["1", "1", "3", "7", "24", "65", "176", "403"]
    assert [r["new_results_without_bound_by_formula"] for r in round_rows][:5] == ["1", "1", "3", "8", "29"]
    assert round_rows[5]["new_results_without_bound_by_formula"] == ""
    with (tmp_path / "counts.csv").open(encoding="utf-8", newline="") as handle:
        count_rows = list(csv.DictReader(handle))
    assert count_rows[0] == {
        "terms": "0",
        "total_multiplicity": "0",
        "results": "1",
        "seventh seed results (one relation; the results asserting nothing with s)": "1",
        "product of the seventh seed counts": "1",
        "results whose relations agree everywhere": "1",
        "results by the two-term closed form": "",
    }
    two_one = next(r for r in count_rows if r["terms"] == "2" and r["total_multiplicity"] == "1")
    assert two_one["results"] == two_one["product of the seventh seed counts"] == two_one["results by the two-term closed form"] == "4"
    two_two = next(r for r in count_rows if r["terms"] == "2" and r["total_multiplicity"] == "2")
    assert two_two["results"] == "20" and two_two["product of the seventh seed counts"] == "16"
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given_doc["changes"] == ["add a term"] and given_doc["the_first_change_can_only_add_a_term"]
    assert given_doc["results_after_one_change"] == ["terms a; asserted nothing"]
    assert given_doc["reaches_the_one_term_state"] and not given_doc["the_one_term_state_reaches_it"]
    assert not given_doc["reaches_itself_in_two_changes"] and given_doc["cost_of_the_one_term_state"] == 1
    assert given_doc["the_eighth_seeds_beginnings_seen_from_here"]["without_bra"] == {
        "state": "terms a b; asserted arb",
        "cost_here": 3,
        "cost_under_the_eighth_seed": 0,
    }
    assert given_doc["the_one_term_state_under_the_eighth_seed"] == {"without_bra": 2, "with_bra": 3}
    assert given_doc["ara_once_under_the_eighth_seed"] == 1 and given_doc["asa_once_under_the_eighth_seed"] == 3
    assert given_doc["the_exchange_keeps_the_cost_here_and_not_under_the_eighth_seed"]
    assert given_doc["asa_is_the_exchange_of_ara"]


def test_write_run_with_zero_rounds_and_census_off(tmp_path: Path) -> None:
    run = write_run(tmp_path, 2, 0, SMALL)
    assert run["results"] == 1 and run["the_first_round_is_the_one_term_state_alone"] is None
    assert run["rounds_agreeing_with_unbounded_formula"] == [True] and run["changes_checked"] == 0
    assert not cli.run_ok(run)
    summary = write_all(
        tmp_path,
        Plan(
            bound=2,
            rounds=2,
            census_bound=0,
            deep_bound=2,
            deep_rounds=2,
            two_term_rounds=2,
            log_bound=2,
            log_rounds=1,
            reach_bound=2,
            reach_rounds=2,
            reach_extra=1,
            layers_upto=2,
            count_upto=2,
            count_total_upto=2,
        ),
    )
    assert summary["census"] == {}


def test_check_changes_reports_every_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 3, 4)
    edges = check_changes(expl)
    assert edges.checked > 0 and not edges.cost_raised_by_more_than_one and not edges.size_not_moved_by_one
    assert not edges.cost_rule_disagreements and not edges.term_lost
    assert edges.round_raised > edges.round_lowered > 0 == edges.round_kept and edges.xrx_made > 0 and edges.xsx_made > 0
    big = DState.of(1, [(0, 0)] * 5, [(0, 0)] * 5)
    monkeypatch.setattr(evidence, "perform", lambda state, change: big)
    forced = check_changes(expl)
    assert forced.cost_raised_by_more_than_one and forced.size_not_moved_by_one and forced.cost_rule_disagreements
    monkeypatch.setattr(evidence, "term_stays", lambda s, o: False)
    assert check_changes(expl).term_lost


def test_check_changes_counts_a_change_that_keeps_the_round() -> None:
    expl = explore(empty(), 3, 4)
    state, _change, out = next(iter(performed(expl)))
    expl.depth[out] = expl.depth[state]
    assert check_changes(expl).round_kept > 0


def test_one_term_binomial_can_fail() -> None:
    expl = explore(empty(), 2, 4)
    sequences = count_shortest_sequences(expl)
    assert one_term_binomial(expl, sequences)
    sequences[DState.of(1, [], [])] = 2
    assert not one_term_binomial(expl, sequences)


def test_compare_with_seventh_notices_every_difference() -> None:
    expl = explore(empty(), 3, 5)
    sequences = count_shortest_sequences(expl)
    good = compare_with_seventh(expl, sequences)
    assert seventh_ok(good) and good["results_asserting_nothing_with_s"] == good["seventh_results"]
    ara = DState.of(1, [(0, 0)], [])
    sequences[ara] += 1
    seq_off = compare_with_seventh(expl, sequences)
    assert seq_off["results_asserting_nothing_with_s_are_the_seventh_results_at_the_same_rounds"]
    assert not seq_off["same_shortest_sequence_counts_as_seventh_on_nothing_in_s"]
    assert not seventh_ok(seq_off)
    sequences[ara] -= 1
    asa = DState.of(1, [], [(0, 0)])
    sequences[asa] += 1
    s_off = compare_with_seventh(expl, sequences)
    assert not s_off["same_shortest_sequence_counts_as_seventh_on_nothing_in_r"]
    sequences[asa] -= 1
    del expl.depth[ara]
    missing = compare_with_seventh(expl, sequences)
    assert not missing["results_asserting_nothing_with_s_are_the_seventh_results_at_the_same_rounds"]
    expl = explore(empty(), 3, 5)
    sequences = count_shortest_sequences(expl)
    del expl.depth[asa]
    no_exchange = compare_with_seventh(expl, sequences)
    assert not no_exchange["every_exchange_is_a_result"] and not seventh_ok(no_exchange)
    expl = explore(empty(), 3, 5)
    sequences = count_shortest_sequences(expl)
    expl.depth[asa] = 99
    round_off = compare_with_seventh(expl, sequences)
    assert round_off["every_exchange_is_a_result"]
    assert not round_off["every_exchange_has_the_same_round_and_sequence_count"]


def test_compare_with_eighth_notices_every_difference(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 3, 6)
    good = compare_with_eighth(expl, False)
    assert eighth_ok(good) and good["eighth_rounds"] == 2 and good["results_with_a_term_of_small_size"] == 1
    with_bra = compare_with_eighth(expl, True)
    assert eighth_ok(with_bra) and with_bra["results_with_a_term_of_small_size"] == 0
    with pytest.raises(ValueError):
        compare_with_eighth(explore(empty(), 1, 3), False)
    shallow = explore(empty(), 2, 3)
    assert compare_with_eighth(shallow, True)["eighth_rounds"] == 0
    del expl.depth[canonical(DState.of(2, [(0, 1)], []))]
    bad = compare_with_eighth(expl, False)
    assert not bad["same_results_as_eighth_derivation_any_rewriting"] and not eighth_ok(bad)
    monkeypatch.setattr(evidence, "cost_eighth", lambda s, b: 0)
    worse = compare_with_eighth(explore(empty(), 3, 6), False)
    assert not worse["eighth_round_is_its_cost_formula_on_every_shared_result"] and not eighth_ok(worse)
    monkeypatch.setattr(evidence, "forget_names", lambda s: DState.of(1, [(0, 0)] * 9, []))
    off = compare_with_eighth(explore(empty(), 3, 6), False)
    assert not off["eighth_results_names_forgotten_are_results"]
    assert not off["results_with_a_term_of_small_size_are_eighth_results_names_forgotten"]
    assert not eighth_ok(off)


def test_reach_reports_a_disagreement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable_in_graph", lambda graph, s: {s})
    got = write_reach(tmp_path, SMALL)
    assert not got["criterion_agrees_with_search"] and got["disagreements"] and not cli.reach_ok(got)


def test_reach_reports_a_disagreement_with_the_seventh(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable_on_part", lambda s, t, rel: False)
    got = write_reach(tmp_path, Plan(reach_bound=2, reach_rounds=3, reach_extra=1))
    assert not got["seventh_criterion_on_either_part_agrees_on_every_pair"] and got["seventh_criterion_disagreements"]
    assert not cli.reach_ok(got)


def test_reach_reports_a_disagreement_with_the_eighth(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable_eighth", lambda s, t: False)
    got = write_reach(tmp_path, Plan(reach_bound=2, reach_rounds=3, reach_extra=1))
    assert not got["eighth_criterion_agrees_on_results_with_a_term"] and got["eighth_criterion_disagreements"]
    assert not cli.reach_ok(got)


def test_counts_notice_a_wrong_closed_form_or_a_product_that_matches(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "two_term_count", lambda t: 0)
    counts = write_counts(tmp_path, SMALL)
    assert counts["two_term_closed_form_mismatches"] == [f"2/{t}" for t in range(6)]
    monkeypatch.setattr(evidence, "counts_upto_eighth", lambda s, b, n, d: [])
    assert write_counts(tmp_path, SMALL)["eighth_counts_by_destroyed_givens_add_up_to_these"] is False
    monkeypatch.setattr(evidence, "product_count", lambda n, d: count_free(n, d))
    matched = write_counts(tmp_path, SMALL)
    assert matched["product_equals_count_for_at_most_one_term"] is True
    assert matched["count_exceeds_product_for_two_or_more_terms"] is False
    monkeypatch.setattr(evidence, "product_count", lambda n, d: [0] * (d + 1))
    assert write_counts(tmp_path, SMALL)["product_equals_count_for_at_most_one_term"] is False


def test_given_notices_an_attempt_not_performed_or_another_first_change(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(evidence, "first_changes", lambda: (Change(Kind.ADD_TERM), Change(Kind.ADD_TERM)))
    given = write_given(tmp_path)
    assert given["changes_on_the_empty_state"] == 2 and given["of_which_add_a_term"] == 2
    assert not json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))["the_first_change_can_only_add_a_term"]
    def with_unperformed(start: DState, bound: int, rounds: int = 100, keep_log: bool = False) -> Exploration:
        expl = explore(start, bound, rounds, keep_log)
        expl.log.append(Attempt(empty(), Change(Kind.ADD_TERM), None, False, False, False))
        return expl

    monkeypatch.setattr(evidence, "explore", with_unperformed)
    monkeypatch.setattr(evidence, "first_changes", lambda: (Change(Kind.ADD_TERM),))
    assert write_given(tmp_path)["attempts_not_performed"] == 1


def test_write_run_records_disagreements(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "cost", lambda s: -1)
    run = write_run(tmp_path, 2, 2, SMALL)
    assert run["cost_formula_mismatches"] and not run["round_equals_cost_formula_for_every_result"]
    monkeypatch.setattr(evidence, "part_costs", lambda s: (0, 0))
    parts = write_run(tmp_path, 2, 2, SMALL)
    assert parts["cost_part_mismatches"] and parts["part_sum_mismatches"]
    monkeypatch.setattr(evidence, "two_term_round_count", lambda r: 0)
    closed = write_run(tmp_path, 2, 2, SMALL)
    assert closed["two_term_rounds_equal_closed_form"] is False and not cli.run_ok(closed)
    monkeypatch.setattr(evidence, "agreeing_within", lambda b, r: -1)
    agree = write_run(tmp_path, 2, 2, SMALL)
    assert agree["relations_agreeing_equal_closed_form"] is False
    monkeypatch.setattr(evidence, "one_term_binomial", lambda e, s: False)
    assert write_run(tmp_path, 2, 2, SMALL)["one_term_results_follow_the_binomial"] is False


def test_write_run_notices_a_doubled_frontier(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    def doubled_frontier(start: DState, bound: int, rounds: int = 100, keep_log: bool = False) -> Exploration:
        expl = explore(start, bound, rounds, keep_log)
        if expl.frontier:
            expl.frontier.append(expl.frontier[0])
        return expl

    monkeypatch.setattr(evidence, "explore", doubled_frontier)
    run = write_run(tmp_path, 2, 3, SMALL)
    assert run["frontier_entries_are_1_per_state_with_N_terms"] is False


def test_write_census_alone() -> None:
    census = write_census(3, 4)
    assert cli.census_ok(census) and census["results"] == 41 and int(str(census["results_asserting_some_xrx"])) > 0
    assert census["frontier_entries"] == census["frontier_states"] and int(str(census["results_of_the_last_round_whose_changes_await"])) > 0


def test_the_checks_fail_when_a_number_is_wrong() -> None:
    seventh: dict[str, object] = {
        "results_asserting_nothing_with_s_are_the_seventh_results_at_the_same_rounds": True,
        "results_asserting_nothing_with_r_are_the_seventh_results_at_the_same_rounds": True,
        "same_shortest_sequence_counts_as_seventh_on_nothing_in_s": True,
        "same_shortest_sequence_counts_as_seventh_on_nothing_in_r": True,
        "every_exchange_is_a_result": True,
        "every_exchange_has_the_same_round_and_sequence_count": True,
    }
    eighth: dict[str, object] = {
        "same_results_as_eighth_derivation_any_rewriting": True,
        "eighth_round_is_its_cost_formula_on_every_shared_result": True,
        "eighth_results_names_forgotten_are_results": True,
        "results_with_a_term_of_small_size_are_eighth_results_names_forgotten": True,
    }
    good: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "cost_is_the_seventh_cost_of_either_part_plus_the_other_total": True,
        "sum_of_the_part_costs_exceeds_the_cost_by_the_terms": True,
        "relations_agreeing_equal_closed_form": True,
        "rounds_agreeing_with_unbounded_formula": [True],
        "two_term_rounds_equal_closed_form": None,
        "the_first_round_is_the_one_term_state_alone": True,
        "attempts_equal_formula": True,
        "xrx_making_equal_eighth_formula": True,
        "xsx_making_equal_eighth_formula": True,
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
        "one_term_results_follow_the_binomial": True,
        "results_that_reach_what_is_given": 1,
        "results_reached_from_what_is_given": 7,
        "statements_holding_in_every_result": [],
        "seventh_derivation": seventh,
        "eighth_derivation": {"without_bra": eighth, "with_bra": eighth},
    }
    assert cli.run_ok(good)
    for key, wrong in (
        ("explored_equals_independent_count", False),
        ("rounds_agreeing_with_unbounded_formula", [True, False]),
        ("the_first_round_is_the_one_term_state_alone", False),
        ("changes_keeping_the_round", 1),
        ("results_with_a_two_change_cycle", 5),
        ("results_that_reach_what_is_given", 2),
        ("statements_holding_in_every_result", ["at_least_one_term_r"]),
        ("size_not_moved_by_one", ["x"]),
        ("cost_is_the_seventh_cost_of_either_part_plus_the_other_total", False),
        ("sum_of_the_part_costs_exceeds_the_cost_by_the_terms", False),
        ("seventh_derivation", {**seventh, "every_exchange_is_a_result": False}),
        ("eighth_derivation", {"without_bra": {**eighth, "eighth_results_names_forgotten_are_results": False}, "with_bra": eighth}),
    ):
        assert not cli.run_ok({**good, key: wrong}), key
    reach: dict[str, object] = {
        "criterion_agrees_with_search": True,
        "ordered_pairs": 4,
        "unordered_pairs_reachable_both_ways": 1,
        "results_that_reach_what_is_given": 1,
        "seventh_criterion_on_either_part_agrees_on_every_pair": True,
        "eighth_criterion_agrees_on_results_with_a_term": True,
        "ordered_pairs_of_results_with_a_term": 1,
    }
    assert cli.reach_ok(reach) and not cli.reach_ok({**reach, "results_that_reach_what_is_given": 2})
    assert not cli.reach_ok({**reach, "eighth_criterion_agrees_on_results_with_a_term": False})
    census: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "one_term_results_follow_the_binomial": True,
        "seventh_derivation": seventh,
        "eighth_derivation": {"without_bra": eighth},
    }
    assert cli.census_ok(census) and not cli.census_ok({**census, "round_equals_cost_formula_for_every_result": False})
    summary: dict[str, object] = {
        "given": {"changes_on_the_empty_state": 1, "of_which_add_a_term": 1, "attempts_not_performed": 0},
        "independent_counts": {
            "two_term_closed_form_mismatches": [],
            "eighth_counts_by_destroyed_givens_add_up_to_these": True,
            "product_equals_count_for_at_most_one_term": True,
            "count_exceeds_product_for_two_or_more_terms": True,
        },
    }
    assert cli.shared_ok(summary)
    assert not cli.shared_ok(
        {**summary, "given": {"changes_on_the_empty_state": 2, "of_which_add_a_term": 1, "attempts_not_performed": 0}}
    )
    assert not cli.shared_ok(
        {
            **summary,
            "independent_counts": {
                "two_term_closed_form_mismatches": ["2/3"],
                "eighth_counts_by_destroyed_givens_add_up_to_these": True,
                "product_equals_count_for_at_most_one_term": True,
                "count_exceeds_product_for_two_or_more_terms": True,
            },
        }
    )
    assert not cli.shared_ok(
        {
            **summary,
            "independent_counts": {
                "two_term_closed_form_mismatches": [],
                "eighth_counts_by_destroyed_givens_add_up_to_these": True,
                "product_equals_count_for_at_most_one_term": True,
                "count_exceeds_product_for_two_or_more_terms": False,
            },
        }
    )


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
    s = DState.of(2, [(0, 1)], [])
    rec = evidence.attempt_record(attempt(s, Change(Kind.ADD_TERM), 3), 1)
    assert rec["adds"] == [1, 0] and rec["changes_a_multiplicity_to"] is None and rec["performed"] and rec["kind"] == "add a term"
    beyond = evidence.attempt_record(attempt(s, Change(Kind.ADD_TERM), 2), 1)
    assert beyond["beyond_bound"] and beyond["outcome"] is None
    removal = evidence.attempt_record(attempt(s, Change(Kind.REMOVE, "r", 0, 1), 2), 1)
    assert removal["changes_a_multiplicity_to"] == 0 and removal["outcome"] == canonical(DState.of(2, [], [])).key()
    added = evidence.attempt_record(attempt(s, Change(Kind.ADD_ASSERTION, "s", 0, 1), 2), 1)
    assert added["changes_a_multiplicity_to"] == 1 and added["relation"] == "s"
    merge = evidence.attempt_record(attempt(s, Change(Kind.IDENTIFY, "", 0, 1), 2), 1)
    assert merge["makes_some_xrx_asserted"] and merge["changes_a_multiplicity_to"] is None
    start = evidence.attempt_record(attempt(empty(), Change(Kind.ADD_TERM), 2), 1)
    assert start["written"] == "no terms; asserted nothing" and start["outcome"] == "1::|"
