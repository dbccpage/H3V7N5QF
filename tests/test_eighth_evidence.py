from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from eighth import __main__ as cli
from eighth import evidence
from eighth.changes import Change, Kind, attempt_counts, changes
from eighth.evidence import (
    Plan,
    check_changes,
    check_free_cost,
    compare_with_sixth,
    run_tag,
    two_term_multinomial,
    write_all,
    write_census,
    write_counts,
    write_given,
    write_reach,
    write_run,
)
from eighth.explore import attempt, count_shortest_sequences, explore, performed
from eighth.orbits import count_free
from eighth.state import DState, canonical, given
from sixth.explore import count_shortest_sequences as count_shortest_sequences_sixth
from sixth.explore import explore as explore_sixth
from sixth.state import MState
from sixth.state import canonical as canonical_sixth
from sixth.state import given as given_sixth
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
    log_rounds=2,
    reach_bound=2,
    reach_rounds=3,
    reach_extra=3,
    layers_upto=4,
    count_upto=2,
    count_total_upto=4,
)


def test_plan() -> None:
    assert Plan().bound(Sameness.FREE) == 4 and Plan().bound(Sameness.ANCHORED) == 3 and Plan().rounds == 5
    assert Plan().runs(Sameness.FREE) == ((4, 5), (3, 6), (2, 8)) and SMALL.runs(Sameness.ANCHORED) == ((3, 4), (3, 5), (2, 6))
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
        assert run["attempts_obstructed"] == 0 and run["changes_making_some_xsx_asserted"] > 0
        assert int(str(run["results_asserting_nothing_with_s"])) < int(str(run["results"])) and int(str(run["results_asserting_nothing_with_r"])) > 0
        assert run["changes_lowering"]["total_s"] > 0 and run["changes_lowering"]["no_xsx"] > 0
        assert run["results_with_a_two_change_cycle"] == run["results"] and run["changes_keeping_the_round"] == 0
        assert run["results_asserting_nothing_with_s"] == run["sixth_derivation_results"]
        assert run["statements_holding_in_every_result"] == ["at_least_one_term_r", "at_least_one_term_s"]
        for name in ("nothing_in_s", "nothing_in_r", "some_pair_in_both", "relations_agree", "no_xrx_r", "no_xrx_s", "something_asserted_s"):
            assert name in run["statements_that_do_not_follow"], (tag, name)
        if "anchored" in tag:
            assert run["results_with_the_names_one_term"] > 0
            assert run["results_that_reach_what_is_given"] == run["results"] - run["results_with_the_names_one_term"]
        else:
            assert run["results_that_reach_what_is_given"] == run["results"]
    for tag, pairs in reach.items():
        assert cli.reach_ok(pairs), tag
        assert pairs["ordered_pairs_with_the_same_r_part"] == pairs["of_which_reachable_both_ways"] > 0
        if "anchored" in tag:
            assert pairs["ordered_pairs_unreachable"] > 0
        else:
            assert pairs["ordered_pairs_unreachable"] == 0
    for count in census.values():
        assert cli.census_ok(count) and count["bound_on_terms"] == 4 and count["rounds"] == 4
    two = runs["anchored/without_bra/bound2_rounds6"]
    assert two["results"] == 4436 and two["two_term_rounds_equal_closed_form"] is True
    assert two["two_term_sequences_equal_multinomial"] is True
    assert runs["anchored/with_bra/bound2_rounds6"]["results"] == 5478
    assert runs["free/without_bra/bound2_rounds6"]["two_term_rounds_equal_closed_form"] is None
    main = runs["anchored/without_bra/bound3_rounds4"]
    assert main["results"] == 2194 and main["rounds_agreeing_with_unbounded_formula"] == [True, True]
    assert runs["free/without_bra/bound3_rounds4"]["results"] == 1429 and runs["free/with_bra/bound3_rounds4"]["results"] == 1259
    assert runs["anchored/with_bra/bound3_rounds4"]["results"] == 2533
    assert cli.shared_ok(summary) and summary["free_cost_closed_form_mismatches"] == []
    assert summary["given"] == {"attempts_not_performed": 0, "beginnings_whose_loop_counts_differ_from_formula": 0}
    counts = summary["independent_counts"]
    assert isinstance(counts, dict) and counts["product_equals_count_for_one_term"] and counts["count_exceeds_product_for_two_or_more_terms"]
    assert counts["totals"]["free"] == [15, 255] and counts["totals"]["product"] == [15, 179]

    names = {p.name for p in tmp_path.iterdir()}
    for tag in ("free_without_bra", "free_with_bra", "anchored_without_bra", "anchored_with_bra"):
        for run_ in ("bound3_rounds4", "bound3_rounds5", "bound2_rounds6"):
            for stem in ("results", "added", "frontier", "rounds", "follows"):
                assert f"{stem}_{run_}_{tag}.csv" in names
        assert f"reach_bound2_rounds3_{tag}.csv" in names and f"attempts_bound2_rounds2_{tag}.jsonl" in names
    assert {"given.json", "counts.csv", "summary.json", "MANIFEST.sha256"} <= names

    with (tmp_path / "results_bound3_rounds4_anchored_without_bra.csv").open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == 2194 and rows[0]["state"] == "2:01:0-1*1|" and rows[0]["round_first_reached"] == "0"
    assert all(row["fewest_changes_by_formula"] == row["round_first_reached"] for row in rows)
    assert all(int(row["fewest_changes_by_formula"]) == int(row["fewest_changes_of_the_r_part_sixth_seed"]) + int(row["assertions_in_s"]) for row in rows)
    assert all((row["shortest_sequences_sixth_seed"] == "") == (row["nothing_in_s"] == "0") for row in rows)
    assert all((row["fewest_classes_s"] == "") == (row["asserts_no_xsx"] == "0") for row in rows)
    with (tmp_path / "attempts_bound2_rounds2_anchored_without_bra.jsonl").open(encoding="utf-8") as handle:
        records = [json.loads(line) for line in handle]
    assert records[0]["change"] == "identify a and b" and records[0]["relation"] is None and records[0]["makes_some_xrx_asserted"]
    asb = next(r for r in records if r["change"] == "add asb")
    assert asb["relation"] == "s" and asb["changes_a_multiplicity_to"] == 1 and not asb["makes_some_xsx_asserted"]
    asa = next(r for r in records if r["change"] == "add asa")
    assert asa["makes_some_xsx_asserted"] and not asa["makes_some_xrx_asserted"]
    with (tmp_path / "counts.csv").open(encoding="utf-8", newline="") as handle:
        count_rows = list(csv.DictReader(handle))
    assert count_rows[6]["terms"] == "2" and count_rows[6]["total_multiplicity"] == "1"
    assert count_rows[6]["results free"] == "4" and count_rows[6]["product of the single-relation counts"] == "4"
    assert count_rows[7]["results free"] == "20" and count_rows[7]["product of the single-relation counts"] == "16"
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    block = given_doc["anchored/without_bra"]
    assert block["changes"] == 11 and block["of_which_in_s"] == 4 and block["of_which_make_some_xsx_asserted"] == 2
    assert block["adding_asb_gives"] == "terms a b; asserted arb asb" and block["cost_of_adding_asb"] == 1
    assert block["cost_of_adding_asa"] == 1 and block["cost_of_identifying_a_and_b"] == 1
    assert block["asb_given_instead_reaches_it"] and block["it_reaches_asb_given_instead"]
    assert block["reaches_the_one_term_state"] and not block["the_one_term_state_reaches_it"]


def test_check_changes_reports_disagreements(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, 3)
    edges = check_changes(expl, False)
    assert edges.checked > 0 and not edges.cost_raised_by_more_than_one and not edges.cost_rule_disagreements
    assert not edges.names_told_apart_again and edges.round_raised > edges.round_lowered > 0 == edges.round_kept
    assert edges.xrx_made > 0 and edges.xsx_made > 0
    free = check_changes(explore(given(False, Sameness.FREE), 3, 3), False)
    assert free.checked > 0 and not free.cost_rule_disagreements
    monkeypatch.setattr(evidence, "names_stay_merged", lambda s, o: False)
    assert check_changes(expl, False).names_told_apart_again
    monkeypatch.setattr(evidence, "cost_rises_by_at_most_one", lambda state, out, bra: False)
    assert check_changes(expl, False).cost_raised_by_more_than_one
    monkeypatch.setattr(evidence, "raises_by_one", lambda state, change, bra: True)
    assert check_changes(expl, False).cost_rule_disagreements


def test_check_changes_counts_a_change_that_keeps_the_round() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, 3)
    state, _change, out = next(iter(performed(expl)))
    expl.depth[out] = expl.depth[state]
    assert check_changes(expl, False).round_kept > 0


def test_compare_with_sixth_notices_a_difference() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, 3)
    sixth = explore_sixth(given_sixth(False, Sameness.ANCHORED), 3, 3)
    sequences = count_shortest_sequences(expl)
    sixth_sequences = count_shortest_sequences_sixth(sixth)
    good = compare_with_sixth(expl, sixth, sequences, sixth_sequences)
    assert good["same_results_and_rounds_as_sixth_derivation"] and good["same_shortest_sequence_counts_as_sixth_derivation"]
    assert int(str(good["results_whose_r_part_is_what_is_given"])) > 1
    sequences[expl.start] = 5
    bad = compare_with_sixth(expl, sixth, sequences, sixth_sequences)
    assert bad["same_results_and_rounds_as_sixth_derivation"] and not bad["same_shortest_sequence_counts_as_sixth_derivation"]
    sixth.depth[canonical_sixth(MState.of(3, [], (0, 1)))] = 99
    assert not compare_with_sixth(expl, sixth, sequences, sixth_sequences)["same_results_and_rounds_as_sixth_derivation"]


def test_free_cost_check_reports_a_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    checked, mismatches = check_free_cost(2, 1)
    assert checked > 0 and mismatches == []
    monkeypatch.setattr(evidence, "cost", lambda state, bra: -1)
    checked, mismatches = check_free_cost(1, 1)
    assert len(mismatches) == checked


def test_two_term_multinomial_check_can_fail(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    expl = explore(given(False, Sameness.FREE), 2, 3)
    assert two_term_multinomial(expl, count_shortest_sequences(expl), False) is None
    monkeypatch.setattr(evidence, "count_shortest_sequences", lambda expl: {state: 1 for state in expl.depth})
    run = write_run(tmp_path, Sameness.ANCHORED, False, 2, 3, SMALL)
    assert run["two_term_sequences_equal_multinomial"] is False and not cli.run_ok(run)


def test_reach_reports_a_disagreement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable_in_graph", lambda graph, s: {s})
    got = write_reach(tmp_path, Sameness.FREE, False, SMALL)
    assert not got["criterion_agrees_with_search"] and got["disagreements"] and not cli.reach_ok(got)


def test_counts_notice_a_product_that_matches(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "product_count", lambda n, d: count_free(n, d))
    counts = write_counts(tmp_path, SMALL)
    assert counts["count_exceeds_product_for_two_or_more_terms"] is False and counts["product_equals_count_for_one_term"] is True
    monkeypatch.setattr(evidence, "product_count", lambda n, d: [0] * (d + 1))
    counts = write_counts(tmp_path, SMALL)
    assert counts["product_equals_count_for_one_term"] is False


def test_given_notices_a_loop_count_off_the_formula(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    real = attempt_counts
    monkeypatch.setattr(evidence, "attempt_counts", lambda state: (real(state)[0], real(state)[1] + 1, real(state)[2]))
    assert write_given(tmp_path)["beginnings_whose_loop_counts_differ_from_formula"] == 4


def test_given_relation_counts_follow_the_change_list(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    write_given(tmp_path)
    original = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    for bra in (False, True):
        row = original[f"anchored/{'with_bra' if bra else 'without_bra'}"]
        assert row["of_which_in_r"] == 1 + int(bra) + 4
        assert row["of_which_in_s"] == 4

    real_changes = changes
    monkeypatch.setattr(
        evidence,
        "changes",
        lambda state: tuple(
            c for c in real_changes(state)
            if not (c.kind is Kind.ADD_ASSERTION and c.rel == "r" and c.x == 0 and c.y == 0)
        ),
    )
    write_given(tmp_path)
    altered = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    for bra in (False, True):
        label = f"anchored/{'with_bra' if bra else 'without_bra'}"
        assert altered[label]["of_which_in_r"] == original[label]["of_which_in_r"] - 1
        assert altered[label]["of_which_in_s"] == original[label]["of_which_in_s"]


def test_write_run_and_census_alone(tmp_path: Path) -> None:
    run = write_run(tmp_path, Sameness.FREE, True, 3, 3, SMALL)
    assert cli.run_ok(run) and run["results"] == 262
    census = write_census(Sameness.ANCHORED, True, 3, 3)
    assert cli.census_ok(census) and census["results"] == 491 and census["results_asserting_nothing_with_s"] == 144


def test_the_checks_fail_when_a_number_is_wrong() -> None:
    good: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "rounds_agreeing_with_unbounded_formula": [True],
        "two_term_rounds_equal_closed_form": None,
        "same_results_and_rounds_as_sixth_derivation": True,
        "same_shortest_sequence_counts_as_sixth_derivation": True,
        "results_asserting_nothing_with_s": 3,
        "results": 7,
        "attempts_equal_formula": True,
        "xrx_making_equal_sixth_formula": True,
        "xsx_making_equal_sixth_formula": True,
        "cost_raised_by_more_than_one": [],
        "cost_rule_disagreements": [],
        "names_told_apart_again": [],
        "changes_keeping_the_round": 0,
        "frontier_entries_are_1_per_state_with_N_terms": True,
        "results_with_a_two_change_cycle": 7,
        "two_term_sequences_equal_multinomial": None,
        "results_that_reach_what_is_given": 5,
        "statements_holding_in_every_result": ["at_least_one_term_r", "at_least_one_term_s"],
    }
    assert cli.run_ok(good)
    for key, wrong in (
        ("explored_equals_independent_count", False),
        ("rounds_agreeing_with_unbounded_formula", [True, False]),
        ("results_asserting_nothing_with_s", 7),
        ("xsx_making_equal_sixth_formula", False),
        ("changes_keeping_the_round", 1),
        ("results_with_a_two_change_cycle", 6),
        ("results_that_reach_what_is_given", 1),
        ("statements_holding_in_every_result", []),
        ("cost_rule_disagreements", ["x"]),
    ):
        assert not cli.run_ok({**good, key: wrong}), key
    reach: dict[str, object] = {
        "criterion_agrees_with_search": True,
        "ordered_pairs": 4,
        "unordered_pairs_reachable_both_ways": 1,
        "ordered_pairs_with_the_same_r_part": 2,
        "of_which_reachable_both_ways": 2,
    }
    assert cli.reach_ok(reach) and not cli.reach_ok({**reach, "of_which_reachable_both_ways": 1})
    census: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "same_results_and_rounds_as_sixth_derivation": True,
        "same_shortest_sequence_counts_as_sixth_derivation": True,
    }
    assert cli.census_ok(census) and not cli.census_ok({**census, "same_shortest_sequence_counts_as_sixth_derivation": False})
    summary: dict[str, object] = {
        "free_cost_closed_form_mismatches": [],
        "given": {"attempts_not_performed": 0, "beginnings_whose_loop_counts_differ_from_formula": 0},
        "independent_counts": {"product_equals_count_for_one_term": True, "count_exceeds_product_for_two_or_more_terms": True},
    }
    assert cli.shared_ok(summary)
    assert not cli.shared_ok({**summary, "independent_counts": {"product_equals_count_for_one_term": False, "count_exceeds_product_for_two_or_more_terms": True}})
    assert not cli.shared_ok({**summary, "given": {"attempts_not_performed": 1, "beginnings_whose_loop_counts_differ_from_formula": 0}})


def test_command_line(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    args = [
        "--out", str(tmp_path), "--free-bound", "2", "--anchored-bound", "2", "--rounds", "3",
        "--census-bound", "3", "--deep-bound", "2", "--deep-rounds", "3", "--two-term-rounds", "3",
        "--log-bound", "2", "--log-rounds", "1", "--reach-bound", "2", "--reach-rounds", "2",
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
    assert rec["adds"] == [1, 0] and rec["changes_a_multiplicity_to"] is None and rec["relation"] is None
    beyond = evidence.attempt_record(attempt(s, Change(Kind.ADD_TERM), 2), 1)
    assert beyond["beyond_bound"] and beyond["outcome"] is None
    removal = evidence.attempt_record(attempt(s, Change(Kind.REMOVE, "r", 0, 1), 2), 1)
    assert removal["changes_a_multiplicity_to"] == 0 and removal["relation"] == "r"
    with_s = DState.of(2, [(0, 1)], [(0, 0)], (0, 1))
    loop = evidence.attempt_record(attempt(with_s, Change(Kind.ADD_ASSERTION, "s", 0, 0), 2), 1)
    assert loop["changes_a_multiplicity_to"] == 2 and not loop["makes_some_xsx_asserted"]
