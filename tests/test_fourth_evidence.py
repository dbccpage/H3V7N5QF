from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from fourth import __main__ as cli
from fourth import evidence
from fourth.changes import REMOVAL_IMPOSSIBLE
from fourth.evidence import (
    Plan,
    check_changes,
    check_free_cost,
    compare_with_third,
    run_tag,
    write_all,
    write_census,
    write_given,
    write_reach,
    write_run,
)
from fourth.explore import Exploration, count_sequences, explore
from fourth.orbits import counts_upto
from fourth.state import MState, canonical, given
from third.explore import explore as explore_third
from xry.state import Sameness
from xry.state import given as given_third

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


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    reach = summary["reachability"]
    census = summary["anchored_census"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(census, dict)
    assert len(runs) == 12 and len(reach) == 4 and len(census) == 2
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["answers_removing_the_obstruction"] == 0
        assert run["changes_checked"] > 0
        assert run["results_that_reach_what_is_given"] == 1
        assert run["results_reached_by_one_sequence"] >= 1
        assert run["sequences_of_changes_total"] > run["results"]
        assert run["results_of_the_last_round_whose_changes_await"] > 0
        for name in ("no_xrx", "at_least_two_terms", "something_asserted"):
            assert name in run["statements_holding_in_every_result"]
        for name in ("nothing_twice", "something_twice", "same_multiplicity"):
            assert name in run["statements_that_do_not_follow"]
        assert run["results_asserting_nothing_twice"] == run["third_derivation_results"]
    for tag, pairs in reach.items():
        assert cli.reach_ok(pairs), tag
        assert pairs["unordered_pairs_reachable_both_ways"] == 0
        assert pairs["pairs_reachable_with_a_multiplicity_above_one"] > 0
        assert pairs["third_derivation_disagreements"] == []
        assert pairs["rows_written"] == pairs["ordered_pairs_reachable"] + pairs["ordered_pairs_asserting_nothing_twice"] - pairs["of_which_reachable"]
        assert pairs["rows_written"] < pairs["ordered_pairs"]
    for count in census.values():
        assert cli.census_ok(count) and count["bound_on_terms"] == 4 and count["rounds"] == 4
    two = runs["anchored/without_bra/bound2_rounds6"]
    assert two["results"] == 28 and two["frontier_entries"] == 5 * 21 and two["changes_awaiting"] == 5 * 7
    assert two["sequences_of_changes_total"] == 2**7 - 1 and two["two_term_sequences_equal_binomial"] is True
    assert runs["free/without_bra/bound2_rounds6"]["two_term_sequences_equal_binomial"] is None
    main = runs["anchored/without_bra/bound3_rounds4"]
    assert main["results"] == 15 + 84 and main["results_by_terms"] == {"2": 15, "3": 84}
    assert main["rounds_agreeing_with_unbounded_formula"] == [True, True]
    assert main["frontier_states"] == 84 - 56 and main["frontier_entries"] == (84 - 56) * 7
    assert main["results_of_the_last_round_whose_changes_await"] == 5 + 56
    assert "arb_asserted" in main["statements_holding_in_every_result"]
    assert "bra_asserted" in main["statements_that_do_not_follow"]
    assert "arb_once" in main["statements_that_do_not_follow"]
    assert "bra_asserted" in runs["anchored/with_bra/bound3_rounds4"]["statements_holding_in_every_result"]
    assert runs["free/without_bra/bound3_rounds4"]["sequences_of_changes_total"] == main["sequences_of_changes_total"]
    assert summary["given"] == {
        "states_on_given_terms_asserting_nothing_twice": 2,
        "states_on_given_terms_with_no_multiplicity_above_3": 12,
        "listed_builds_that_are_not_builds": 0,
    }
    assert summary["free_cost_closed_form_mismatches"] == []
    assert summary["independent_counts"] == {
        "free/without_bra": [0, 11, 82],
        "free/with_bra": [0, 6, 41],
        "anchored/without_bra": [0, 15, 210],
        "anchored/with_bra": [0, 10, 84],
    }

    names = {p.name for p in tmp_path.iterdir()}
    for tag in ("free_without_bra", "free_with_bra", "anchored_without_bra", "anchored_with_bra"):
        for run_ in ("bound3_rounds4", "bound3_rounds5", "bound2_rounds6"):
            for stem in ("results", "added", "frontier", "rounds", "follows"):
                assert f"{stem}_{run_}_{tag}.csv" in names
        assert f"reach_bound3_rounds4_{tag}.csv" in names
        assert f"attempts_bound2_rounds3_{tag}.jsonl" in names
    assert {"given.json", "counts.csv", "summary.json", "MANIFEST.sha256"} <= names

    with (tmp_path / "rounds_bound3_rounds4_free_without_bra.csv").open(encoding="utf-8", newline="") as handle:
        rounds = list(csv.DictReader(handle))
    assert len(rounds) == 5
    assert [row["new_results_within_bound"] for row in rounds[:3]] == ["1", "3", "7"]  # one result of round 2 has 4 terms
    assert [row["new_results_asserting_nothing_twice"] for row in rounds[:3]] == ["1", "2", "4"]
    assert [row["new_results_third_derivation"] for row in rounds[:3]] == ["1", "2", "4"]
    assert rounds[2]["new_results_without_bound_by_formula"] == "8"
    assert rounds[4]["new_results_without_bound_by_formula"] == "54"
    assert rounds[1]["changes_attempted_so_far"] == "5" and rounds[1]["of_which_obstructed"] == "2"

    with (tmp_path / "frontier_bound3_rounds4_anchored_with_bra.csv").open(encoding="utf-8", newline="") as handle:
        frontier = list(csv.DictReader(handle))
    assert len(frontier) == 84 - 56
    assert {(r["leaves_by_the_change"], r["leaves_by_a_build"]) for r in frontier} == {("1", "6")}

    with (tmp_path / "results_bound3_rounds4_anchored_without_bra.csv").open(encoding="utf-8", newline="") as handle:
        results = list(csv.DictReader(handle))
    assert len(results) == 99
    assert all(r["round_first_reached"] == r["fewest_changes_by_formula"] for r in results)
    assert [r["reaches_what_is_given"] for r in results] == ["1"] + ["0"] * 98
    assert results[0]["sequences_of_changes"] == "1" and results[0]["changes"] == "5"
    assert results[0]["obstructed_additions"] == "2" and results[0]["fewest_classes"] == "2"
    assert results[0]["changes_attempted"] == "1" and results[-1]["changes_attempted"] == "0"
    assert min(int(r["terms_added_to_given"]) for r in results) == 0
    assert all(int(r["changes"]) == 1 + int(r["terms"]) ** 2 for r in results)
    assert all(int(r["assertions_asserted"]) <= int(r["assertions_counted"]) for r in results)
    simple = len(explore_third(given_third(False, Sameness.ANCHORED), 3, 4).depth)
    assert sum(int(r["asserts_nothing_twice"]) for r in results) == simple == 28
    twice = next(r for r in results if r["written"] == "terms a b; asserted arb(2)")
    assert twice["largest_multiplicity"] == "2" and twice["asserts_nothing_twice"] == "0"
    assert twice["round_first_reached"] == "1" and twice["assertions_added_to_given"] == "1"

    with (tmp_path / "counts.csv").open(encoding="utf-8", newline="") as handle:
        counts = list(csv.DictReader(handle))
    assert len(counts) == 3 * 6
    row = next(r for r in counts if r["terms"] == "2" and r["total_multiplicity"] == "3")
    assert row["results anchored/without_bra"] == "3" and row["asserting nothing twice anchored/without_bra"] == "0"
    row = next(r for r in counts if r["terms"] == "2" and r["total_multiplicity"] == "2")
    assert row["results anchored/without_bra"] == "2" and row["asserting nothing twice anchored/without_bra"] == "1"

    doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert doc["count_asserting_nothing_twice"] == 2 and doc["count_with_no_multiplicity_above_3"] == 12
    assert doc["count_without_a_bound_on_multiplicity"] == "infinite"
    root = doc["anchored/without_bra"]
    assert root["state"] == "terms a b; asserted arb"
    assert root["changes"] == 5 and root["of_which_obstructed"] == 2
    assert [a["change"] for a in root["attempts"]] == ["add a term", "add ara", "add arb", "add bra", "add brb"]
    add_ara = root["attempts"][1]
    assert add_ara["obstruction"] == ["ara"] and add_ara["remove_the_obstruction"] == REMOVAL_IMPOSSIBLE
    assert [a["answer"] for a in add_ara["answers"]] == ["refused", "build structure", "build structure"]
    assert add_ara["answers"][1]["further"] == ["add a term", "add arc"]
    assert add_ara["raises_a_multiplicity_to"] == 1
    add_arb = root["attempts"][2]
    assert add_arb["raises_a_multiplicity_to"] == 2 and add_arb["outcome"] == "2:01:0-1*2"
    assert root["attempts"][0]["remove_the_obstruction"] is None
    assert root["attempts"][0]["raises_a_multiplicity_to"] is None
    assert root["builds_with_one_added_term"]["add ara"]["one_term_builds"] == 2
    assert root["reaches_the_other_beginning"] and not root["reaches_the_one_term_state"]
    assert root["reaches_arb_asserted_twice"] and not root["arb_asserted_twice_reaches_what_is_given"]
    assert not doc["anchored/with_bra"]["reaches_the_other_beginning"]
    assert doc["free/without_bra"]["reaches_the_other_beginning"]
    assert not doc["free/with_bra"]["reaches_the_other_beginning"]
    assert doc["free/with_bra"]["reaches_arb_asserted_twice"]


def test_evidence_is_regenerable(tmp_path: Path) -> None:
    write_all(tmp_path / "one", SMALL)
    write_all(tmp_path / "two", SMALL)
    one = (tmp_path / "one" / "MANIFEST.sha256").read_text(encoding="utf-8")
    assert one == (tmp_path / "two" / "MANIFEST.sha256").read_text(encoding="utf-8")
    assert b"\r" not in (tmp_path / "one" / "summary.json").read_bytes()


def test_free_cost_check() -> None:
    checked, mismatches = check_free_cost(2, 2)
    assert mismatches == [] and checked == 2 * (1 + 6)
    assert check_free_cost(1, 3)[0] == 2


def test_free_cost_check_reports_a_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    # The closed form and the best-placement form always agree, so the mismatch
    # branch never fires on correct code; force a disagreement to prove the
    # check is not vacuous (as the first and second derivations do).
    monkeypatch.setattr(evidence, "cost_free", lambda state, bra: -1)
    checked, mismatches = check_free_cost(2, 2)
    assert checked == 2 * (1 + 6) and len(mismatches) == checked
    assert mismatches[0].startswith("without_bra/")


def test_independent_count_skips_terms_beyond_the_size_bound() -> None:
    # `_counted` skips a term count whose least size already exceeds the rounds
    # bound (degree < 0); with no rounds, four terms is beyond size(given) = 3.
    assert 4 not in evidence._counted(Sameness.FREE, False, 4, 0)


def test_free_count_of_no_terms_is_empty() -> None:
    # `_free` returns all zeros for zero terms (no state on no terms).
    assert counts_upto(Sameness.FREE, False, 0, 3) == [0, 0, 0, 0]


def test_a_listed_build_that_is_not_a_build_is_counted(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(evidence, "is_build_of", lambda build, state, change: False)
    assert write_given(tmp_path)["listed_builds_that_are_not_builds"] == 4 * 2 * 2


def test_check_changes_reports_every_kind_of_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(given(False, Sameness.FREE), 3, rounds=4)
    check = check_changes(expl)
    assert check.checked > 0
    assert check.round_not_raised_by_one == () and check.counts_lowered_by == ()
    assert check.fewest_classes_lowered_by == ()
    monkeypatch.setattr(evidence, "fewest_classes", lambda state: -state.m)
    assert check_changes(expl).fewest_classes_lowered_by
    monkeypatch.setattr(evidence, "never_decreases", lambda state, out: False)
    lowered = check_changes(expl).counts_lowered_by
    assert lowered and " / add " in lowered[0]
    expl.depth[canonical(MState.of(3, [(0, 1)]))] = 3
    assert check_changes(expl).round_not_raised_by_one


def test_compare_with_third_notices_a_difference() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, rounds=4)
    third = explore_third(given_third(False, Sameness.ANCHORED), 3, rounds=4)
    sequences = count_sequences(expl)
    got = compare_with_third(expl, third, sequences)
    assert got[cli.SAME_RESULTS] and got[cli.SAME_SEQUENCES]
    assert got["results_asserting_nothing_twice"] == got["third_derivation_results"] == len(third.depth)
    twisted = dict(sequences)
    twisted[expl.start] = 2
    got = compare_with_third(expl, third, twisted)
    assert got[cli.SAME_RESULTS] and not got[cli.SAME_SEQUENCES]
    shorter = explore_third(given_third(False, Sameness.ANCHORED), 3, rounds=3)
    got = compare_with_third(expl, shorter, sequences)
    assert not got[cli.SAME_RESULTS] and not got[cli.SAME_SEQUENCES]


def test_two_term_binomial_check_can_fail(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    def broken(expl: object) -> dict[MState, int]:
        assert isinstance(expl, Exploration)
        return {state: 1 for state in expl.depth}

    monkeypatch.setattr(evidence, "count_sequences", broken)
    run = write_run(tmp_path, Sameness.ANCHORED, False, 2, 3, SMALL)
    assert run["two_term_sequences_equal_binomial"] is False and not cli.run_ok(run)


def test_reach_reports_a_disagreement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable_by_search", lambda s, bound, rounds: set())
    got = write_reach(tmp_path, Sameness.FREE, False, SMALL)
    assert not got["embedding_agrees_with_search"] and got["disagreements"]
    stray = MState.of(1, [])
    monkeypatch.setattr(evidence, "reachable_by_search", lambda s, bound, rounds: {stray})
    got = write_reach(tmp_path, Sameness.FREE, False, SMALL)
    assert "not a result" in str(got["disagreements"])


def test_reach_compares_with_the_third_derivation(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable_third", lambda s, t: False)
    got = write_reach(tmp_path, Sameness.FREE, True, SMALL)
    assert not got["third_derivation_agrees_on_every_pair_asserting_nothing_twice"]
    disagreements = got["third_derivation_disagreements"]
    assert isinstance(disagreements, list) and len(disagreements) == got["of_which_reachable"]
    assert not cli.reach_ok(got)


def test_mutual_reachability_would_be_counted(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable", lambda s, t: True)
    got = write_reach(tmp_path, Sameness.ANCHORED, False, SMALL)
    both = got["unordered_pairs_reachable_both_ways"]
    assert isinstance(both, int) and both > 0
    assert not cli.reach_ok(got)


def test_fewer_rounds_than_the_bound_needs(tmp_path: Path) -> None:
    run = write_run(tmp_path, Sameness.FREE, False, 4, 1, SMALL)
    assert run["rounds_agreeing_with_unbounded_formula"] == [True, True]
    assert run["attempts_equal_formula_1_plus_n_squared"]
    assert run["obstructed_equal_formula_n"]
    assert run["changes_checked"] == 3 and run["sequences_of_changes_total"] == 1 + 3
    assert run["frontier_states"] == 0 and run["results_of_the_last_round_whose_changes_await"] == 3
    assert cli.run_ok(run)


def test_census_can_be_turned_off(tmp_path: Path) -> None:
    plan = Plan(
        free_bound=2, anchored_bound=2, rounds=3, census_bound=0, deep_bound=2, deep_rounds=2,
        two_term_rounds=3, log_bound=2, log_rounds=2, reach_bound=2, reach_rounds=2,
        layers_upto=2, count_upto=2, count_total_upto=3,
    )  # fmt: skip
    assert write_all(tmp_path, plan)["anchored_census"] == {}
    count = write_census(Sameness.ANCHORED, True, 3, 3)
    assert count["results"] == 10 + 28 and count["frontier_states"] == 1 + 6
    assert count["results_of_the_last_round_whose_changes_await"] == 4 + 21
    assert count[cli.SAME_RESULTS] and count[cli.SAME_SEQUENCES] and count["third_derivation_results"] == 1 + 1 + 4 + 6


def test_command_line(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    args = [
        "--out", str(tmp_path), "--free-bound", "3", "--anchored-bound", "3", "--rounds", "4",
        "--census-bound", "4", "--deep-bound", "3", "--deep-rounds", "5", "--two-term-rounds", "6",
        "--log-bound", "2", "--log-rounds", "3", "--reach-bound", "3", "--reach-rounds", "4",
        "--layers-upto", "4", "--count-upto", "3", "--count-total-upto", "5",
    ]  # fmt: skip
    assert cli.main(args) == 0
    out = capsys.readouterr().out
    assert out.count("checks pass") == 12 + 4 + 2 + 1 and "FAIL" not in out
    assert "census at bound 4: 150 results" in out
    assert cli.main([*args, "--check"]) == 0
    assert "matches a fresh regeneration" in capsys.readouterr().out
    (tmp_path / "counts.csv").write_text("edited\n", encoding="utf-8")
    assert cli.main([*args, "--check"]) == 1
    out = capsys.readouterr().out
    assert "differs: counts.csv" in out and "DIFFERS FROM a fresh regeneration" in out


GOOD_RUN: dict[str, object] = {
    "results": 1,
    "explored_equals_independent_count": True,
    "round_equals_cost_formula_for_every_result": True,
    "rounds_agreeing_with_unbounded_formula": [True],
    cli.SAME_RESULTS: True,
    cli.SAME_SEQUENCES: True,
    "additions_never_negative": True,
    "attempts_equal_formula_1_plus_n_squared": True,
    "obstructed_equal_formula_n": True,
    "answers_reaching_something_new": [],
    "answers_removing_the_obstruction": 0,
    "round_not_raised_by_one": [],
    "counts_lowered_by": [],
    "fewest_classes_lowered_by": [],
    "frontier_entries_are_1_plus_2N_per_state_with_N_terms": True,
    "two_term_sequences_equal_binomial": None,
    "results_that_reach_what_is_given": 1,
}

GOOD_REACH: dict[str, object] = {
    "embedding_agrees_with_search": True,
    "ordered_pairs": 1,
    "unordered_pairs_reachable_both_ways": 0,
    "third_derivation_agrees_on_every_pair_asserting_nothing_twice": True,
    "ordered_pairs_asserting_nothing_twice": 1,
}


def test_every_check_is_needed() -> None:
    assert cli.run_ok(GOOD_RUN)
    for key, bad in [
        ("rounds_agreeing_with_unbounded_formula", []),
        ("rounds_agreeing_with_unbounded_formula", [True, False]),
        (cli.SAME_RESULTS, False),
        (cli.SAME_SEQUENCES, False),
        ("round_not_raised_by_one", ["x"]),
        ("counts_lowered_by", ["x"]),
        ("results_that_reach_what_is_given", 2),
        ("attempts_equal_formula_1_plus_n_squared", False),
        ("two_term_sequences_equal_binomial", False),
    ]:
        assert not cli.run_ok({**GOOD_RUN, key: bad}), key
    assert cli.reach_ok(GOOD_REACH)
    for key, bad in [
        ("ordered_pairs", 0),
        ("unordered_pairs_reachable_both_ways", 1),
        ("third_derivation_agrees_on_every_pair_asserting_nothing_twice", False),
        ("ordered_pairs_asserting_nothing_twice", 0),
        ("embedding_agrees_with_search", False),
    ]:
        assert not cli.reach_ok({**GOOD_REACH, key: bad}), key
    census: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        cli.SAME_RESULTS: True,
        cli.SAME_SEQUENCES: True,
    }
    assert cli.census_ok(census)
    assert not cli.census_ok({**census, cli.SAME_SEQUENCES: False})


def test_command_line_fails_when_a_check_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    bad = {**GOOD_RUN, "explored_equals_independent_count": False}
    reach = {"free/without_bra": dict(GOOD_REACH)}
    census: dict[str, object] = {
        "anchored/without_bra": {
            "bound_on_terms": 4,
            "results": 1,
            "explored_equals_independent_count": False,
            "round_equals_cost_formula_for_every_result": True,
            cli.SAME_RESULTS: True,
            cli.SAME_SEQUENCES: True,
        }
    }
    shared: dict[str, object] = {
        "given": {"listed_builds_that_are_not_builds": 0},
        "free_cost_closed_form_mismatches": [],
    }
    monkeypatch.setattr(
        cli,
        "write_all",
        lambda out, plan: {
            "runs": {"free/without_bra/bound3_rounds4": bad},
            "reachability": reach,
            "anchored_census": census,
            **shared,
        },
    )
    assert cli.main(["--out", str(tmp_path)]) == 1
    out = capsys.readouterr().out
    assert "free/without_bra/bound3_rounds4: 1 results, checks FAIL" in out
    assert "census at bound 4: 1 results, checks FAIL" in out
    bad["explored_equals_independent_count"] = True
    census.clear()
    reach["free/without_bra"]["ordered_pairs"] = 0
    assert cli.main(["--out", str(tmp_path)]) == 1
    assert "reachability: 0 pairs, checks FAIL" in capsys.readouterr().out
    reach["free/without_bra"]["ordered_pairs"] = 1
    shared["free_cost_closed_form_mismatches"] = ["x"]
    assert cli.main(["--out", str(tmp_path)]) == 1
    assert "given and free cost: checks FAIL" in capsys.readouterr().out
