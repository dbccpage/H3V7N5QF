from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from sixteenth import __main__ as cli
from sixteenth import evidence
from sixteenth.changes import Change16, Kind
from sixteenth.evidence import (
    Plan,
    attempt_record,
    compare_with_ninth,
    ninth_ok,
    record_summary,
    records_ok,
    run_tag,
    write_all,
    write_alternatives,
    write_counts,
    write_given,
    write_log,
    write_reach,
    write_run,
)
from sixteenth.explore import attempt16, count_shortest_sequences16, explore16
from sixteenth.invariants import check_records
from sixteenth.reach import mass_ok, reachable16, reachable_ninth
from sixteenth.state import RState, add_assertion16, canonical16, empty16


def _block(doc: dict[str, object], key: str) -> dict[str, object]:
    """A nested block of a summary, typed."""
    inner = doc[key]
    assert isinstance(inner, dict)
    return inner

SMALL = Plan(
    bound=2,
    rounds=5,
    wide_bound=3,
    wide_rounds=5,
    two_term_rounds=5,
    log_bound=2,
    log_rounds=3,
    reach_bound=2,
    reach_rounds=3,
    reach_extra=2,
    alt_bound=2,
    alt_rounds=5,
    alt_reach_rounds=4,
    alt_reach_extra=2,
    layers_upto=4,
    count_upto=2,
    count_weight_upto=4,
)


def test_plan() -> None:
    assert Plan().bound == 3 and Plan().rounds == 8 and Plan().wide_bound == 4 and Plan().two_term_rounds == 10
    assert Plan().runs() == ((3, 8), (4, 7), (2, 10)) and SMALL.runs() == ((2, 5), (3, 5), (2, 5))
    assert run_tag(3, 4) == "bound3_rounds4"


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    reach = summary["reachability"]
    counts = summary["independent_counts"]
    given = summary["given"]
    alternatives = summary["alternatives"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(counts, dict)
    assert isinstance(given, dict) and isinstance(alternatives, dict)
    assert list(runs) == ["bound2_rounds5", "bound3_rounds5"]
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["admissions_attempted"] > 0 and run["results_with_a_record"] > 0
        assert run["frontier_entries"] == run["frontier_states"] > 0
        assert run["change_statements_holding_of_every_change"] == []
        assert "is_admission" in run["change_statements_that_do_not_follow"]
        assert "nothing_recorded" in run["statements_that_do_not_follow"]
    two = runs["bound2_rounds5"]
    assert two["results"] == 126 and two["two_term_rounds_equal_the_series"] is True
    assert two["results_by_terms"] == {"0": 1, "1": 22, "2": 103}
    assert two["rounds_agreeing_with_unbounded_series"] == [True, True, True]
    assert runs["bound3_rounds5"]["two_term_rounds_equal_the_series"] is None
    assert runs["bound3_rounds5"]["results"] == 167
    assert cli.reach_ok(reach) and reach["disagreements"] == []
    assert reach["ordered_pairs_this_seed_admits_and_the_ninth_refuses"] == []
    assert int(str(reach["ordered_pairs_the_ninth_admits_and_this_seed_refuses"])) > 0
    assert reach["results_that_reach_what_is_given"] == 1
    assert cli.counts_ok(counts) and counts["totals_by_terms"] == [1, 22, 351]
    assert counts["layers_without_bound"] == [1, 1, 3, 9, 33] and counts["ninth_layers_without_bound"] == [1, 1, 3, 8, 29]
    assert cli.given_ok(given)
    assert cli.alternatives_ok(alternatives)
    assert summary["attempts_in_full_log"] == 22

    names = {p.name for p in tmp_path.iterdir()}
    for run_ in ("bound2_rounds5", "bound3_rounds5"):
        for stem in ("results", "frontier", "rounds", "follows"):
            assert f"{stem}_{run_}.csv" in names
    assert {"reach_bound2_rounds3.csv", "attempts_bound2_rounds3.jsonl", "given.json", "counts.csv", "alternatives.json", "summary.json", "MANIFEST.sha256"} <= names

    with (tmp_path / "results_bound2_rounds5.csv").open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == 126 and rows[0]["state"] == "0::|#" and rows[0]["written"] == "no terms; asserted nothing; recorded nothing"
    assert rows[1]["written"] == "terms a; asserted nothing; recorded nothing" and rows[1]["round_first_reached"] == "1"
    assert all(row["fewest_changes_by_formula"] == row["round_first_reached"] for row in rows)
    assert all(row["reached_from_what_is_given"] == "1" for row in rows)
    assert all(row["shortest_sequences_exact_within_bound"] == "1" for row in rows)
    assert all((row["ninth_seed_cost_of_the_state"] == row["fewest_changes_by_formula"]) == (row["nothing_recorded"] == "1") for row in rows)
    recorded = next(row for row in rows if row["nothing_recorded"] == "0")
    assert recorded["round_first_reached"] == "3" and recorded["leftovers_recorded"] == "1"
    with (tmp_path / "attempts_bound2_rounds3.jsonl").open(encoding="utf-8") as handle:
        records = [json.loads(line) for line in handle]
    first = records[0]
    assert first["state"] == "0::|#" and first["change"] == "add a term" and first["leftover"] == "nothing" and first["performed"]
    assert first["outcome"] == "1::|#" and first["adds"] == [1, 0] and not first["admits_a_leftover"]
    assert first["leftover_admissible_on_the_outcome"] is False
    assert any(r["beyond_bound"] and r["outcome"] is None and r["leftover_admissible_on_the_outcome"] is None for r in records)
    with (tmp_path / "reach_bound2_rounds3.csv").open(encoding="utf-8", newline="") as handle:
        reach_rows = list(csv.DictReader(handle))
    assert all(row["criterion_agrees_with_search"] == "1" for row in reach_rows)
    assert reach_rows[0]["has_a_term"] == "0" and reach_rows[0]["results_reaching_it"] == "1"
    with (tmp_path / "rounds_bound2_rounds5.csv").open(encoding="utf-8", newline="") as handle:
        round_rows = list(csv.DictReader(handle))
    assert [r["new_results_with_at_most_two_terms_by_the_series"] for r in round_rows] == ["1", "1", "3", "8", "28", "85"]
    assert [r["new_results_with_one_term_by_closed_form"] for r in round_rows] == ["0", "1", "2", "4", "6", "9"]
    assert [r["new_results_of_the_ninth_seed_within_bound"] for r in round_rows] == ["1", "1", "3", "7", "24", "65"]
    assert round_rows[5]["new_results_without_bound_by_the_series"] == ""
    with (tmp_path / "counts.csv").open(encoding="utf-8", newline="") as handle:
        count_rows = list(csv.DictReader(handle))
    one_two = next(r for r in count_rows if r["terms"] == "1" and r["weight (both totals plus twice the record)"] == "2")
    assert one_two["results"] == "4" and one_two["results by the one-term closed form"] == "4"
    assert one_two["results with an empty record"] == one_two["ninth seed results (the same weight, no record)"] == "3"
    two_three = next(r for r in count_rows if r["terms"] == "2" and r["weight (both totals plus twice the record)"] == "3")
    assert two_three["results"] == "76" and two_three["product of the ninth count and the record count"] == "68"
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given_doc["changes"] == ["add a term"] and given_doc["the_first_change_can_only_add_a_term"]
    assert given_doc["same_relation"]["is_the_identity"] and given_doc["same_relation"]["after_removing_ara"] == "terms a; asserted nothing; recorded aℓa"
    assert given_doc["other_relation"]["after_admitting_into_s"] == "terms a; asserted asa; recorded nothing"
    assert given_doc["other_relation"]["after_adding_asa_directly"] == "terms a; asserted asa; recorded aℓa"
    assert given_doc["mass"]["ara_reaches_the_one_term_state_under_the_ninth_criterion"] and not given_doc["mass"]["ara_reaches_the_one_term_state_here"]
    assert given_doc["admission_costs_three"]["route_by_admission_add_term_add_remove_admit"] == [0, 1, 2, 3, 2]
    assert given_doc["cycles"]["the_ninth_add_then_remove_is_a_cycle_here"] is False
    assert given_doc["set_reading"]["is_the_identity_under_the_set_reading"] is False
    assert given_doc["set_reading"]["is_the_identity_under_the_count_reading"] is True
    assert given_doc["the_fourteenth_witness"]["leftover_of_removing_arb_admitted_into_s"] == "terms a b; asserted asb(2); recorded nothing"
    assert given_doc["exchange_keeps_the_record"] and given_doc["direct_additions_that_change_the_record"] == []
    alt_doc = json.loads((tmp_path / "alternatives.json").read_text(encoding="utf-8"))
    assert alt_doc["set"]["same_relation_identity_failures"] > 0 and alt_doc["drop"]["same_relation_identity_failures"] == 0
    assert alt_doc["set"]["first_identity_failure"] and alt_doc["drop"]["first_identity_failure"] is None
    assert alt_doc["drop"]["reachability"]["ninth_criterion_disagreements_with_search"] == 0
    assert alt_doc["count"]["results"] == alt_doc["drop"]["results"] > alt_doc["set"]["results"]


def test_write_run_with_zero_rounds(tmp_path: Path) -> None:
    run = write_run(tmp_path, 2, 0, SMALL)
    assert run["results"] == 1 and run["the_first_round_is_the_one_term_state_alone"] is None
    assert run["rounds_agreeing_with_unbounded_series"] == [True] and _block(run, "records")["checked"] == 0
    assert not cli.run_ok(run)


def test_write_run_beyond_the_layer_bound(tmp_path: Path) -> None:
    run = write_run(tmp_path, 2, 3, Plan(layers_upto=2))
    assert run["rounds_agreeing_with_unbounded_series"] == [True, True, True]


def test_compare_with_ninth_notices_every_difference() -> None:
    expl = explore16(empty16(), 2, 4)
    sequences = count_shortest_sequences16(expl)
    good = compare_with_ninth(expl, sequences)
    assert ninth_ok(good) and int(str(good["results_with_a_record"])) > 0
    ara = canonical16(RState.of(1, [(0, 0)]))
    sequences[ara] += 1
    seq_off = compare_with_ninth(expl, sequences)
    assert seq_off["empty_record_results_are_the_ninth_results"] and seq_off["sequence_disagreements"] and not ninth_ok(seq_off)
    sequences[ara] -= 1
    expl.depth[ara] = 9
    round_off = compare_with_ninth(expl, sequences)
    assert round_off["round_disagreements"] and not ninth_ok(round_off)
    del expl.depth[ara]
    del sequences[ara]
    missing = compare_with_ninth(expl, sequences)
    assert missing["missing_results"] and not ninth_ok(missing)
    stray = canonical16(RState.of(1, [(0, 0)] * 9))
    expl.depth[stray] = 4
    sequences[stray] = 1
    extra = compare_with_ninth(expl, sequences)
    assert extra["extra_results"] and not ninth_ok(extra)


def test_records_ok_and_summary() -> None:
    expl = explore16(empty16(), 2, 3)
    block = record_summary(check_records(expl))
    assert records_ok(block) and int(str(block["checked"])) > 0
    assert not records_ok({**block, "mass_fell": ["x"]})
    assert not records_ok({"checked": 0})


def test_write_run_records_disagreements(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "one_term_round_count", lambda k: -1)
    run = write_run(tmp_path, 2, 3, SMALL)
    assert run["one_term_closed_form_mismatches"] and not run["one_term_rounds_equal_closed_form"] and not cli.run_ok(run)
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "two_term_round_count16", lambda k: -1)
    run = write_run(tmp_path, 2, 3, SMALL)
    assert run["two_term_rounds_equal_the_series"] is False and not cli.run_ok(run)


def test_reach_reports_disagreements(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    plan = Plan(reach_bound=2, reach_rounds=4, reach_extra=2)
    honest = write_reach(tmp_path, plan)
    assert cli.reach_ok(honest)
    assert int(str(honest["ordered_pairs_the_two_mass_invariants_admit_and_the_criterion_refuses"])) > 0
    monkeypatch.setattr(evidence, "reachable_in_graph16", lambda graph, s: {s})
    got = write_reach(tmp_path, plan)
    assert not got["criterion_agrees_with_search"] and got["disagreements"] and not cli.reach_ok(got)
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "reachable_ninth", lambda s, t: False)
    got = write_reach(tmp_path, plan)
    assert got["ordered_pairs_this_seed_admits_and_the_ninth_refuses"] and not cli.reach_ok(got)
    assert got["ordered_pairs_the_ninth_admits_and_this_seed_refuses"] == 0


def test_mass_invariant_count_includes_pairs_the_ninth_refuses(tmp_path: Path) -> None:
    """The two mass invariants are mass and diagonal mass, not the ninth's criterion.

    A term with nothing asserted and nothing recorded has mass 0, so the
    invariants admit the empty state, and the carrying criterion refuses it
    because no map sends a term into no terms. The ninth's criterion refuses
    that pair too. The published count must still include it.
    """
    plan = Plan(reach_bound=2, reach_rounds=3, reach_extra=1)
    got = write_reach(tmp_path, plan)
    states = list(explore16(empty16(), plan.reach_bound, plan.reach_rounds).depth)
    expected = sum(1 for s in states for t in states if mass_ok(s, t) and not reachable16(s, t))
    ninth_filtered = sum(
        1
        for s in states
        for t in states
        if mass_ok(s, t) and reachable_ninth(s, t) and not reachable16(s, t)
    )
    assert expected > ninth_filtered
    assert got["ordered_pairs_the_two_mass_invariants_admit_and_the_criterion_refuses"] == expected


def test_counts_notice_a_wrong_closed_form_or_part(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "one_term_round_count", lambda k: 0)
    counts = write_counts(tmp_path, SMALL)
    assert counts["one_term_closed_form_mismatches"] and not cli.counts_ok(counts)
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "ninth_part", lambda n, d: ([0] * (d + 1), [1] * (d + 1)))
    counts = write_counts(tmp_path, SMALL)
    assert counts["empty_record_count_mismatches"] == ["0", "1", "2"] and not cli.counts_ok(counts)
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "product_count16", lambda n, d: [0] * (d + 1))
    counts = write_counts(tmp_path, SMALL)
    assert not counts["product_equals_count_for_at_most_one_term"] and not cli.counts_ok(counts)


def test_given_notices_a_broken_witness(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    good = write_given(tmp_path)
    assert cli.given_ok(good)
    monkeypatch.setattr(evidence, "first_changes16", lambda: (Change16(Kind.ADD_TERM), Change16(Kind.ADD_TERM)))
    assert not cli.given_ok(write_given(tmp_path))
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "admit16", add_assertion16)
    broken = write_given(tmp_path)
    assert not broken["same_relation_is_the_identity"] and not cli.given_ok(broken)
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "reachable16", lambda s, t: True)
    assert not cli.given_ok(write_given(tmp_path))


def test_alternatives_notice_a_wrong_reading(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    plan = Plan(alt_bound=2, alt_rounds=5, alt_reach_rounds=4, alt_reach_extra=2)
    good = write_alternatives(tmp_path, plan)
    assert cli.alternatives_ok(good)
    monkeypatch.setattr(evidence, "cost16", lambda rs: -1)
    got = write_alternatives(tmp_path, plan)
    assert not _block(got, "set")["round_equals_potential_for_every_result"] and _block(got, "set")["round_potential_mismatches"]
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "admit16", add_assertion16)
    got = write_alternatives(tmp_path, plan)
    assert int(str(_block(got, "drop")["same_relation_identity_failures"])) > 0 and not cli.alternatives_ok(got)


def test_write_log_and_attempt_record(tmp_path: Path) -> None:
    assert write_log(tmp_path, SMALL) == 22
    s = RState.of(2, [(0, 1)], [], [(1, 0)])
    rec = attempt_record(attempt16(s, Change16(Kind.ADD_ASSERTION, "s", 1, 0, True), 3), 1)
    assert rec["admits_a_leftover"] and rec["leftover"] == "nothing" and rec["relation"] == "s" and rec["adds"] == [0, 1]
    assert rec["leftover_admissible_on_the_outcome"] is False
    removal = attempt_record(attempt16(s, Change16(Kind.REMOVE, "r", 0, 1), 3), 1)
    assert removal["leftover"] == "0ℓ1" and removal["leftover_admissible_on_the_outcome"] is True


def test_the_checks_fail_when_a_number_is_wrong() -> None:
    ninth: dict[str, object] = {
        "empty_record_results_are_the_ninth_results": True,
        "extra_results": [],
        "missing_results": [],
        "round_disagreements": [],
        "sequence_disagreements": [],
    }
    records: dict[str, object] = {"checked": 5, **{name: [] for name in (
        "potential_not_moved_by_one", "direction_mismatch", "mass_fell", "diagonal_mass_fell",
        "same_relation_not_identity", "other_relation_same_as_start", "other_relation_same_as_direct",
        "admission_left_something", "writing_not_the_fourteenth", "unadmitted_asserted",
        "admissions_not_recorded", "round_not_potential",
    )}}  # fmt: skip
    good: dict[str, object] = {
        "explored_equals_independent_count": True,
        "rounds_agreeing_with_unbounded_series": [True, True],
        "one_term_rounds_equal_closed_form": True,
        "two_term_rounds_equal_the_series": None,
        "the_first_round_is_the_one_term_state_alone": True,
        "attempts_equal_formula": True,
        "admissions_equal_formula": True,
        "frontier_entries_are_1_per_state_with_N_terms": True,
        "records": records,
        "results_with_a_two_change_cycle": 6,
        "results_with_a_term": 6,
        "results": 7,
        "results_with_exact_sequence_count": 7,
        "results_that_reach_what_is_given": 1,
        "results_reached_from_what_is_given": 7,
        "ninth_derivation": ninth,
        "statements_holding_in_every_result": [],
    }
    assert cli.run_ok(good)
    for key, wrong in (
        ("explored_equals_independent_count", False),
        ("rounds_agreeing_with_unbounded_series", [True, False]),
        ("the_first_round_is_the_one_term_state_alone", False),
        ("results_with_a_two_change_cycle", 5),
        ("results_that_reach_what_is_given", 2),
        ("statements_holding_in_every_result", ["nothing_recorded"]),
        ("records", {**records, "mass_fell": ["x"]}),
        ("ninth_derivation", {**ninth, "missing_results": ["x"]}),
    ):
        assert not cli.run_ok({**good, key: wrong}), key
    reach: dict[str, object] = {
        "criterion_agrees_with_search": True,
        "ordered_pairs_this_seed_admits_and_the_ninth_refuses": [],
        "ordered_pairs_the_ninth_admits_and_this_seed_refuses": 3,
        "results_that_reach_what_is_given": 1,
    }
    assert cli.reach_ok(reach) and not cli.reach_ok({**reach, "ordered_pairs_the_ninth_admits_and_this_seed_refuses": 0})
    counts: dict[str, object] = {
        "empty_record_counts_are_the_ninth_counts": True,
        "one_term_closed_form_mismatches": [],
        "product_equals_count_for_at_most_one_term": True,
        "count_exceeds_product_for_two_or_more_terms": True,
    }
    assert cli.counts_ok(counts) and not cli.counts_ok({**counts, "count_exceeds_product_for_two_or_more_terms": False})
    given: dict[str, object] = {
        "changes_on_the_empty_state": 1,
        "of_which_add_a_term": 1,
        "same_relation_is_the_identity": True,
        "other_relation_is_new": True,
        "leftover_of_r_admitted_into_s": True,
        "ninth_criterion_fails_on_ara": True,
        "set_reading_breaks_the_identity": True,
        "direct_additions_that_change_the_record": 0,
    }
    assert cli.given_ok(given) and not cli.given_ok({**given, "other_relation_is_new": False})
    alt_reach = {"ninth_criterion_disagreements_with_search": 0, "carrying_criterion_disagreements_with_search": 4}
    alternatives: dict[str, object] = {
        "set": {"explored_equals_independent_count": True, "same_relation_identity_failures": 2, "reachability": {**alt_reach, "ninth_criterion_disagreements_with_search": 1, "carrying_criterion_disagreements_with_search": 1}},
        "drop": {"explored_equals_independent_count": True, "same_relation_identity_failures": 0, "reachability": alt_reach},
    }
    assert cli.alternatives_ok(alternatives)
    assert not cli.alternatives_ok({**alternatives, "drop": {**alternatives["drop"], "same_relation_identity_failures": 1}})  # type: ignore[dict-item]
    drop_agrees = {**alternatives["drop"], "reachability": {**alt_reach, "carrying_criterion_disagreements_with_search": 0}}  # type: ignore[dict-item]
    assert not cli.alternatives_ok({**alternatives, "drop": drop_agrees})


def test_command_line(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    args = [
        "--out", str(tmp_path), "--bound", "2", "--rounds", "5", "--wide-bound", "2", "--wide-rounds", "5",
        "--two-term-rounds", "5", "--log-bound", "2", "--log-rounds", "2", "--reach-bound", "2", "--reach-rounds", "3",
        "--reach-extra", "2", "--alt-bound", "2", "--alt-rounds", "5", "--alt-reach-rounds", "4", "--alt-reach-extra", "2",
        "--layers-upto", "3", "--count-upto", "2", "--count-weight-upto", "3",
    ]  # fmt: skip
    assert cli.main(args) == 0
    out = capsys.readouterr().out
    assert "checks pass" in out and "FAIL" not in out and "alternatives: checks pass" in out
    assert cli.main([*args, "--check"]) == 0
    assert "check: identical" in capsys.readouterr().out
    (tmp_path / "counts.csv").write_text("changed\n", encoding="utf-8")
    assert cli.main([*args, "--check"]) == 1
    assert "differs: counts.csv" in capsys.readouterr().out


def test_a_failing_check_is_reported(tmp_path: Path, capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(cli, "run_ok", lambda run: False)
    args = [
        "--out", str(tmp_path), "--bound", "2", "--rounds", "3", "--wide-bound", "2", "--wide-rounds", "3",
        "--two-term-rounds", "3", "--log-bound", "2", "--log-rounds", "1", "--reach-bound", "2", "--reach-rounds", "2",
        "--reach-extra", "1", "--alt-bound", "2", "--alt-rounds", "3", "--alt-reach-rounds", "2", "--alt-reach-extra", "1",
        "--layers-upto", "2", "--count-upto", "1", "--count-weight-upto", "2",
    ]  # fmt: skip
    assert cli.main(args) == 1
    assert "FAIL" in capsys.readouterr().out
