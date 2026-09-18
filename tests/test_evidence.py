from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

import pytest

from xry import __main__ as cli
from xry import evidence
from xry.evidence import (
    Plan,
    added_rows,
    alternative,
    check_free_cost,
    compare_evidence,
    states_on_given_terms,
    write_all,
    write_manifest,
)
from xry.explore import explore
from xry.state import Sameness, given

SMALL = Plan(free_bound=3, anchored_bound=3, log_bound=2, rounds=14, layers_upto=4, count_upto=3)


def test_exactly_two_states_on_the_given_terms() -> None:
    found = states_on_given_terms()
    assert [s.written() for s in found] == [
        "terms a b; asserted arb",
        "terms a b; asserted arb bra",
    ]


def test_plan_and_names() -> None:
    assert Plan().bound(Sameness.FREE) == 5 and Plan().bound(Sameness.ANCHORED) == 4
    assert alternative(True) == "with_bra" and alternative(False) == "without_bra"


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    assert isinstance(runs, dict) and len(runs) == 4
    for run in runs.values():
        assert run["explored_equals_independent_count"]
        assert run["round_equals_cost_formula_for_every_result"]
        assert all(run["rounds_agreeing_with_unbounded_formula"])
        assert run["answers_reaching_something_new"] == []
        assert run["frontier_entries_are_1_plus_2N_per_state_with_N_terms"]
        assert run["frontier_entries"] == run["frontier_states"] * 7
        assert run["frontier_attempts"] == run["frontier_states"] * 4
        assert "bra_asserted" not in run["statements_holding_in_every_result"]
        assert "no_xrx" in run["statements_holding_in_every_result"]
    assert "bra_asserted" in runs["anchored/without_bra"]["statements_that_do_not_follow"]
    assert summary["given"] == {"states_on_given_terms": 2, "listed_builds_that_are_not_builds": 0}
    assert summary["free_cost_closed_form_mismatches"] == []
    assert summary["independent_counts"] == {
        "free": [1, 3, 16],
        "free_one_way": [1, 2, 7],
        "anchored": [1, 8, 100],
    }

    names = {p.name for p in tmp_path.iterdir()}
    for tag in ("free_without_bra", "free_with_bra", "anchored_without_bra", "anchored_with_bra"):
        for stem in ("results", "added", "frontier", "rounds", "follows"):
            assert f"{stem}_{tag}.csv" in names
        assert f"attempts_bound2_{tag}.jsonl" in names
    assert {"given.json", "counts.csv", "summary.json", "MANIFEST.sha256"} <= names

    with (tmp_path / "rounds_free_without_bra.csv").open(encoding="utf-8", newline="") as handle:
        rounds = list(csv.DictReader(handle))
    assert len(rounds) == SMALL.rounds + 1
    assert [row["new_results_within_bound"] for row in rounds[:3]] == ["1", "3", "6"]
    assert rounds[3]["new_results_without_bound_by_formula"] == "11"
    assert rounds[5]["new_results_without_bound_by_formula"] == ""

    with (tmp_path / "frontier_anchored_with_bra.csv").open(encoding="utf-8", newline="") as handle:
        frontier = list(csv.DictReader(handle))
    assert len(frontier) == 100
    assert {(r["leaves_by_the_change"], r["leaves_by_a_build"]) for r in frontier} == {("1", "6")}

    doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    root = doc["anchored/without_bra"]
    assert root["state"] == "terms a b; asserted arb"
    first = root["attempts"][0]
    assert first["change"] == "identify a and b" and first["obstruction"] == ["arb"]
    assert [a["answer"] for a in first["answers"]] == [
        "refused",
        "remove the obstruction",
        "build structure",
    ]
    assert first["answers"][1]["further"] == ["remove arb"]
    add_ara = next(a for a in root["attempts"] if a["change"] == "add ara")
    assert add_ara["answers"][1]["further"] == ["add a term", "add arc"]
    assert root["builds_with_one_added_term"]["add ara"]["one_term_builds"] == 6
    on_one = doc["builds_answering_xrx_on_one_term"]
    assert on_one["one_term_builds"] == [
        "terms a b; asserted arb",
        "terms a b; asserted bra",
        "terms a b; asserted arb bra",
    ]
    assert on_one["up_to_free_sameness"] == [
        "terms a b; asserted arb",
        "terms a b; asserted arb bra",
    ]
    assert on_one["these_are_the_alternatives_for_what_is_given"] is True

    log = (tmp_path / "attempts_bound2_free_with_bra.jsonl").read_text(encoding="utf-8")
    assert all(json.loads(line)["round"] >= 1 for line in log.splitlines())


def test_evidence_is_regenerable(tmp_path: Path) -> None:
    write_all(tmp_path / "one", SMALL)
    write_all(tmp_path / "two", SMALL)
    one = (tmp_path / "one" / "MANIFEST.sha256").read_text(encoding="utf-8")
    assert one == (tmp_path / "two" / "MANIFEST.sha256").read_text(encoding="utf-8")
    for line in one.splitlines():
        digest, name = line.split("  ")
        assert hashlib.sha256((tmp_path / "one" / name).read_bytes()).hexdigest() == digest
    assert b"\r" not in (tmp_path / "one" / "summary.json").read_bytes()
    assert b"\r" not in (tmp_path / "one" / "counts.csv").read_bytes()


def test_manifest_skips_itself_and_folders(tmp_path: Path) -> None:
    (tmp_path / "x.txt").write_text("x", encoding="utf-8")
    (tmp_path / "sub").mkdir()
    assert write_manifest(tmp_path) == 1
    assert write_manifest(tmp_path) == 1


def test_added_rows_put_fewest_additions_first() -> None:
    rows = added_rows(explore(given(False, Sameness.FREE), 3, rounds=14))
    totals = [max(t, 0) + max(a, 0) for t, a, *_ in rows]
    assert totals == sorted(totals)
    assert [0, 0, 1, 0, 0] in rows
    assert sum(row[2] for row in rows) == 1 + 3 + 16


def test_free_cost_check_counts_both_alternatives() -> None:
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
    assert evidence.write_given(tmp_path)["listed_builds_that_are_not_builds"] == 72


def test_fewer_rounds_than_the_bound_needs(tmp_path: Path) -> None:
    few = Plan(free_bound=4, anchored_bound=3, log_bound=2, rounds=1, layers_upto=4, count_upto=2)
    run = evidence.write_run(tmp_path, Sameness.FREE, False, few)
    assert run["rounds_agreeing_with_unbounded_formula"] == [True, True]


def test_compare_evidence(tmp_path: Path) -> None:
    one, two = tmp_path / "one", tmp_path / "two"
    for folder in (one, two):
        folder.mkdir()
        (folder / "a.csv").write_text("x\n", encoding="utf-8")
        write_manifest(folder)
    assert compare_evidence(one, two) == []
    (one / "lean_axioms.txt").write_text("report\n", encoding="utf-8")
    write_manifest(one)
    assert compare_evidence(one, two) == []
    (one / "a.csv").write_text("y\n", encoding="utf-8")
    (one / "stale.jsonl").write_text("", encoding="utf-8")
    (two / "new.csv").write_text("", encoding="utf-8")
    (two / "MANIFEST.sha256").unlink()
    assert compare_evidence(one, two) == [
        f"only in {one}: stale.jsonl",
        "only in the regeneration: new.csv",
        "differs: a.csv",
        "differs: MANIFEST.sha256 (lean_axioms.txt line left out)",
    ]


def test_command_line(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    args = [
        "--out", str(tmp_path), "--free-bound", "3", "--anchored-bound", "3",
        "--log-bound", "2", "--rounds", "14", "--layers-upto", "4", "--count-upto", "3",
    ]  # fmt: skip
    assert cli.main(args) == 0
    out = capsys.readouterr().out
    assert out.count("checks pass") == 5 and "FAIL" not in out
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
        "answers_reaching_something_new": [],
        "frontier_entries_are_1_plus_2N_per_state_with_N_terms": True,
    }
    assert not cli.run_ok(run)
    run["rounds_agreeing_with_unbounded_formula"] = [True]
    assert cli.run_ok(run)


def test_command_line_fails_when_a_check_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    bad = {
        "results": 1,
        "explored_equals_independent_count": False,
        "round_equals_cost_formula_for_every_result": True,
        "rounds_agreeing_with_unbounded_formula": [True],
        "answers_reaching_something_new": [],
        "frontier_entries_are_1_plus_2N_per_state_with_N_terms": True,
    }
    shared: dict[str, object] = {
        "given": {"listed_builds_that_are_not_builds": 0},
        "free_cost_closed_form_mismatches": [],
    }
    monkeypatch.setattr(
        cli, "write_all", lambda out, plan: {"runs": {"free/without_bra": bad}, **shared}
    )
    assert cli.main(["--out", str(tmp_path)]) == 1
    assert "free/without_bra: 1 results, checks FAIL" in capsys.readouterr().out
    bad["explored_equals_independent_count"] = True
    shared["free_cost_closed_form_mismatches"] = ["x"]
    assert cli.main(["--out", str(tmp_path)]) == 1
    assert "given and free cost: checks FAIL" in capsys.readouterr().out
