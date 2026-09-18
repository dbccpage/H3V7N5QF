from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from second import __main__ as cli
from second import evidence
from second.changes import REMOVAL_IMPOSSIBLE
from second.evidence import (
    Plan,
    check_classes,
    check_free_cost,
    write_all,
    write_census,
    write_given,
    write_reach,
    write_run,
)
from second.explore import explore
from xry.state import Sameness, State, given

SMALL = Plan(
    free_bound=3,
    anchored_bound=3,
    census_bound=4,
    log_bound=2,
    reach_bound=3,
    rounds=14,
    layers_upto=4,
    count_upto=3,
)


def test_plan() -> None:
    assert Plan().bound(Sameness.FREE) == 5 and Plan().bound(Sameness.ANCHORED) == 4
    assert Plan().census_bound == 5 and Plan().reach_bound == 3


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    reach = summary["reachability"]
    census = summary["anchored_census"]
    assert isinstance(runs, dict) and isinstance(reach, dict) and isinstance(census, dict)
    assert len(runs) == 4 and len(reach) == 4 and len(census) == 2
    for tag, run in runs.items():
        assert cli.run_ok(run)
        assert run["frontier_entries"] == run["frontier_states"] * 7
        assert run["frontier_attempts"] == run["frontier_states"] * 4
        assert run["answers_removing_the_obstruction"] == 0
        assert run["fewest_classes_checked_on"] > 0
        assert run["results_that_reach_what_is_given"] > 1
        for name in ("no_xrx", "at_least_two_terms", "something_asserted"):
            assert name in run["statements_holding_in_every_result"]
        assert cli.reach_ok(reach[tag])
        assert reach[tag]["unordered_pairs_reachable_both_ways"] > 0
    for count in census.values():
        assert cli.census_ok(count) and count["bound_on_terms"] == 4
    assert census["anchored/without_bra"]["results"] == 2 + 32 + 1056
    anchored = runs["anchored/without_bra"]
    assert "arb_asserted" in anchored["statements_holding_in_every_result"]
    assert "bra_asserted" in anchored["statements_that_do_not_follow"]
    assert "bra_asserted" in runs["anchored/with_bra"]["statements_holding_in_every_result"]
    assert summary["given"] == {"states_on_given_terms": 2, "listed_builds_that_are_not_builds": 0}
    assert summary["free_cost_closed_form_mismatches"] == []
    assert summary["independent_counts"] == {
        "free/without_bra": [0, 2, 15],
        "free/with_bra": [0, 1, 9],
        "anchored/without_bra": [0, 2, 32],
        "anchored/with_bra": [0, 1, 16],
    }

    names = {p.name for p in tmp_path.iterdir()}
    for tag in ("free_without_bra", "free_with_bra", "anchored_without_bra", "anchored_with_bra"):
        for stem in ("results", "added", "frontier", "rounds", "follows", "reach_bound3"):
            assert f"{stem}_{tag}.csv" in names
        assert f"attempts_bound2_{tag}.jsonl" in names
    assert {"given.json", "counts.csv", "summary.json", "MANIFEST.sha256"} <= names

    with (tmp_path / "rounds_free_without_bra.csv").open(encoding="utf-8", newline="") as handle:
        rounds = list(csv.DictReader(handle))
    assert len(rounds) == SMALL.rounds + 1
    assert [row["new_results_within_bound"] for row in rounds[:3]] == ["1", "2", "4"]
    assert [row["new_results_by_additions_alone"] for row in rounds[:3]] == ["1", "2", "4"]
    assert rounds[2]["new_results_without_bound_by_formula"] == "5"
    assert rounds[5]["new_results_without_bound_by_formula"] == ""

    with (tmp_path / "frontier_anchored_with_bra.csv").open(encoding="utf-8", newline="") as handle:
        frontier = list(csv.DictReader(handle))
    assert len(frontier) == 16
    assert {(r["leaves_by_the_change"], r["leaves_by_a_build"]) for r in frontier} == {("1", "6")}

    with (tmp_path / "results_anchored_without_bra.csv").open(encoding="utf-8", newline="") as handle:
        results = list(csv.DictReader(handle))
    assert len(results) == 2 + 32
    assert all(r["round_first_reached"] == r["fewest_changes_by_formula"] for r in results)
    assert {r["reaches_what_is_given"] for r in results} == {"0", "1"}
    assert results[0]["fewest_classes"] == "2" and min(int(r["terms_added_to_given"]) for r in results) == 0

    doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    root = doc["anchored/without_bra"]
    assert root["state"] == "terms a b; asserted arb"
    assert [a["change"] for a in root["attempts"]] == [
        "identify a and b", "add a term", "add ara", "add bra", "add brb",
    ]  # fmt: skip
    first = root["attempts"][0]
    assert first["obstruction"] == ["arb"] and first["remove_the_obstruction"] == REMOVAL_IMPOSSIBLE
    assert [a["answer"] for a in first["answers"]] == ["refused", "build structure"]
    assert root["attempts"][1]["remove_the_obstruction"] is None
    add_ara = next(a for a in root["attempts"] if a["change"] == "add ara")
    assert add_ara["answers"][1]["further"] == ["add a term", "add arc"]
    assert root["builds_with_one_added_term"]["add ara"]["one_term_builds"] == 6
    assert root["reaches_the_other_beginning"] and not root["reaches_the_one_term_state"]
    assert not doc["anchored/with_bra"]["reaches_the_other_beginning"]
    assert doc["free/without_bra"]["reaches_the_other_beginning"]
    assert not doc["free/with_bra"]["reaches_the_other_beginning"]

    log = (tmp_path / "attempts_bound2_free_with_bra.jsonl").read_text(encoding="utf-8")
    lines = [json.loads(line) for line in log.splitlines()]
    assert all(line["round"] >= 1 for line in lines)
    assert all(
        (line["remove_the_obstruction"] == REMOVAL_IMPOSSIBLE) == bool(line["obstruction"])
        for line in lines
    )

    with (tmp_path / "reach_bound3_anchored_without_bra.csv").open(encoding="utf-8", newline="") as handle:
        pairs = list(csv.DictReader(handle))
    assert len(pairs) == 34 * 34
    start = next(p for p in pairs if p["from"] == p["to"] == "2:01:0-1")
    assert start["reachable"] == "1" and start["carrying_map"] == "0 1"


def test_evidence_is_regenerable(tmp_path: Path) -> None:
    write_all(tmp_path / "one", SMALL)
    write_all(tmp_path / "two", SMALL)
    one = (tmp_path / "one" / "MANIFEST.sha256").read_text(encoding="utf-8")
    assert one == (tmp_path / "two" / "MANIFEST.sha256").read_text(encoding="utf-8")
    assert b"\r" not in (tmp_path / "one" / "summary.json").read_bytes()


def test_free_cost_check_counts_every_state_once() -> None:
    assert check_free_cost(3) == (2 * (1 + 3 + 16), [])


def test_free_cost_check_reports_a_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "cost_free", lambda state, bra: -1)
    checked, mismatches = check_free_cost(2)
    assert checked == 2 * (1 + 3) and len(mismatches) == checked
    assert mismatches[0].startswith("without_bra/")


def test_a_listed_build_that_is_not_a_build_is_counted(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(evidence, "is_build_of", lambda build, state, change: False)
    assert write_given(tmp_path)["listed_builds_that_are_not_builds"] == 72


def test_check_classes_reports_a_drop(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(given(False, Sameness.FREE), 3, rounds=14)
    checked, lowered = check_classes(expl)
    assert checked > 0 and lowered == []
    monkeypatch.setattr(evidence, "fewest_classes", lambda state: -state.m)
    _, lowered = check_classes(expl)
    assert lowered and " / add " in lowered[0]


def test_reach_reports_a_disagreement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable_by_search", lambda s, bound: set())
    got = write_reach(tmp_path, Sameness.FREE, False, SMALL)
    assert not got["carrying_map_agrees_with_search"] and got["disagreements"]
    stray = State.of(1, [])
    monkeypatch.setattr(evidence, "reachable_by_search", lambda s, bound: {stray})
    got = write_reach(tmp_path, Sameness.FREE, False, SMALL)
    assert "not a result" in str(got["disagreements"])


def test_fewer_rounds_than_the_bound_needs(tmp_path: Path) -> None:
    few = Plan(free_bound=4, anchored_bound=3, census_bound=0, log_bound=2, rounds=1, layers_upto=4, count_upto=2)
    run = write_run(tmp_path, Sameness.FREE, False, few)
    assert run["rounds_agreeing_with_unbounded_formula"] == [True, True]


def test_census_can_be_turned_off(tmp_path: Path) -> None:
    plan = Plan(free_bound=2, anchored_bound=2, census_bound=0, log_bound=2, reach_bound=2, rounds=3, layers_upto=2, count_upto=2)
    assert write_all(tmp_path, plan)["anchored_census"] == {}
    count = write_census(Sameness.ANCHORED, True, 3, 10)
    assert count["results"] == 1 + 16 and count["frontier_states"] == 16 and count["frontier_entries"] == 16 * 7


def test_command_line(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    args = [
        "--out", str(tmp_path), "--free-bound", "3", "--anchored-bound", "3", "--census-bound", "4",
        "--log-bound", "2", "--reach-bound", "3", "--rounds", "14", "--layers-upto", "4", "--count-upto", "3",
    ]  # fmt: skip
    assert cli.main(args) == 0
    out = capsys.readouterr().out
    assert out.count("checks pass") == 4 + 2 + 1 and "FAIL" not in out
    assert "census at bound 4: 1090 results" in out
    assert cli.main([*args, "--check"]) == 0
    assert "matches a fresh regeneration" in capsys.readouterr().out
    (tmp_path / "counts.csv").write_text("edited\n", encoding="utf-8")
    assert cli.main([*args, "--check"]) == 1
    out = capsys.readouterr().out
    assert "differs: counts.csv" in out and "DIFFERS FROM a fresh regeneration" in out


def test_an_empty_comparison_does_not_pass() -> None:
    run: dict[str, object] = {
        "explored_equals_independent_count": True,
        "round_equals_cost_formula_for_every_result": True,
        "rounds_agreeing_with_unbounded_formula": [],
        "additions_alone_reach_the_same_results_in_the_same_rounds": True,
        "additions_never_negative": True,
        "answers_reaching_something_new": [],
        "answers_removing_the_obstruction": 0,
        "fewest_classes_lowered_by": [],
        "frontier_entries_are_1_plus_2N_per_state_with_N_terms": True,
    }
    assert not cli.run_ok(run)
    run["rounds_agreeing_with_unbounded_formula"] = [True]
    assert cli.run_ok(run)
    assert not cli.reach_ok({"carrying_map_agrees_with_search": True, "ordered_pairs": 0})
    assert cli.reach_ok({"carrying_map_agrees_with_search": True, "ordered_pairs": 1})
    assert not cli.census_ok(
        {"explored_equals_independent_count": True, "round_equals_cost_formula_for_every_result": False}
    )


def test_command_line_fails_when_a_check_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    bad: dict[str, object] = {
        "results": 1,
        "explored_equals_independent_count": False,
        "round_equals_cost_formula_for_every_result": True,
        "rounds_agreeing_with_unbounded_formula": [True],
        "additions_alone_reach_the_same_results_in_the_same_rounds": True,
        "additions_never_negative": True,
        "answers_reaching_something_new": [],
        "answers_removing_the_obstruction": 0,
        "fewest_classes_lowered_by": [],
        "frontier_entries_are_1_plus_2N_per_state_with_N_terms": True,
    }
    reach = {"free/without_bra": {"carrying_map_agrees_with_search": True, "ordered_pairs": 1}}
    census: dict[str, object] = {
        "anchored/without_bra": {
            "bound_on_terms": 4,
            "results": 1,
            "explored_equals_independent_count": False,
            "round_equals_cost_formula_for_every_result": True,
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
            "runs": {"free/without_bra": bad},
            "reachability": reach,
            "anchored_census": census,
            **shared,
        },
    )
    assert cli.main(["--out", str(tmp_path)]) == 1
    out = capsys.readouterr().out
    assert "free/without_bra: 1 results, checks FAIL" in out
    assert "census at bound 4: 1 results, checks FAIL" in out
    bad["explored_equals_independent_count"] = True
    census.clear()
    shared["free_cost_closed_form_mismatches"] = ["x"]
    assert cli.main(["--out", str(tmp_path)]) == 1
    assert "given and free cost: checks FAIL" in capsys.readouterr().out
