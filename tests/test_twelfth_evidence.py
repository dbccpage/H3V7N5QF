from __future__ import annotations

import json
from pathlib import Path

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from twelfth import __main__ as cli
from twelfth import evidence
from twelfth.evidence import (
    Plan,
    compare_with_ninth,
    ninth_ok,
    recorded_ok,
    records_ok,
    run_tag,
    write_all,
    write_given,
    write_recorded,
    write_run,
)
from twelfth.explore import RecordedExploration, explore, explore_recorded
from twelfth.invariants import check_records
from twelfth.record import record_determined_by_rel, restores_listed

SMALL = Plan(
    bound=3,
    rounds=4,
    deep_bound=2,
    deep_rounds=3,
    two_term_rounds=4,
    log_bound=2,
    log_rounds=2,
    recorded_bound=2,
    recorded_rounds=5,
)


def test_plan() -> None:
    assert Plan().bound == 3 and Plan().rounds == 6 and Plan().recorded_bound == 2
    assert Plan().runs() == ((3, 6), (3, 5), (2, 8)) and SMALL.runs() == ((3, 4), (2, 3), (2, 4))
    assert run_tag(3, 4) == "bound3_rounds4"


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    recorded = summary["recorded"]
    given = summary["given"]
    assert isinstance(runs, dict) and isinstance(recorded, dict) and isinstance(given, dict)
    assert given["r_record_not_s"] and given["identify_drops_a_term"]
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["results_that_reach_what_is_given"] == 1
        if run["rounds"] >= 4:
            assert "empty_record" not in run["record_statements_holding_of_every_identification"]
    assert recorded_ok(recorded)
    names = {p.name for p in tmp_path.iterdir()}
    assert "given.json" in names and "recorded.json" in names and "summary.json" in names
    assert "attempts_bound2_rounds2.jsonl" in names
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given_doc["r_record_not_s"]
    assert given_doc["two_term_empty_restored"]
    assert not given_doc["two_term_between_restored"]
    assert given_doc["identify_drops_a_term"]
    two = runs["bound2_rounds4"]
    assert two["two_term_rounds_equal_closed_form"] is True
    assert two["records"]["differs"] >= 1


def test_check_records_reports_disagreements(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 2, 4)
    edges = check_records(expl)
    assert edges.checked > 0 and not edges.not_determined_by_rel
    assert not edges.nonempty_restored and not edges.empty_not_restored_isolated
    assert not edges.swap_mismatch
    assert edges.empty_records and edges.nonempty_records and edges.differs
    monkeypatch.setattr("twelfth.invariants.record_determined_by_rel", lambda *_a: False)
    forced = check_records(expl)
    assert forced.not_determined_by_rel
    monkeypatch.setattr("twelfth.invariants.record_determined_by_rel", record_determined_by_rel)
    monkeypatch.setattr("twelfth.invariants.restores_listed", lambda *_a: True)
    forced_rest = check_records(expl)
    assert forced_rest.nonempty_restored
    monkeypatch.setattr("twelfth.invariants.restores_listed", lambda *_a: False)
    forced_empty = check_records(expl)
    assert forced_empty.empty_not_restored_isolated
    monkeypatch.setattr("twelfth.invariants.restores_listed", restores_listed)
    monkeypatch.setattr("twelfth.invariants.swap", lambda s: s)
    forced_swap = check_records(expl)
    assert forced_swap.swap_mismatch


def test_compare_with_ninth_notices(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 2, 3)
    good = compare_with_ninth(expl)
    assert ninth_ok(good) and good["same_results"]
    real = explore_ninth

    def drop_empty(start: DState, bound: int, rounds: int, keep_log: bool = False) -> object:
        got = real(start, bound, rounds, keep_log=keep_log)
        got.depth = {s: r for s, r in got.depth.items() if s.n != 0}
        return got

    monkeypatch.setattr(evidence, "explore_ninth", drop_empty)
    bad = compare_with_ninth(expl)
    assert not ninth_ok(bad) and bad["missing_results"] == [] and bad["extra_results"]
    real_seq = evidence.count_shortest_sequences

    def bump(expl_):  # type: ignore[no-untyped-def]
        got = real_seq(expl_)
        first = next(iter(got))
        got = dict(got)
        got[first] = got[first] + 1
        return got

    monkeypatch.setattr(evidence, "count_shortest_sequences", bump)
    monkeypatch.setattr(evidence, "explore_ninth", real)
    seq = compare_with_ninth(expl)
    assert seq["sequence_disagreements"]
    monkeypatch.setattr(evidence, "count_shortest_sequences", real_seq)
    shifted = explore(empty(), 2, 3)
    one = next(s for s in shifted.depth if s.n == 1)
    ninth_depth = explore_ninth(empty(), 2, 3).depth
    shifted.depth[one] += 1
    assert shifted.depth[one] != ninth_depth[one]
    expl2 = explore(empty(), 2, 3)
    gone = next(s for s in list(expl2.depth) if s.n == 0)
    expl2.depth.pop(gone)
    assert gone not in expl2.depth and gone in ninth_depth


def test_recorded_and_records_ok_can_fail() -> None:
    assert not recorded_ok(
        {
            "more_results_than_the_ninth": False,
            "plain_and_identified_are_two_results": True,
            "one_term_plain_cost": 1,
            "one_term_size": 1,
            "one_term_identified_cost": 3,
            "recorded_cost_failure_count": 1,
        }
    )
    assert not records_ok(
        {
            "split_agrees": False,
            "checked": 1,
            "not_determined_by_rel": [],
            "nonempty_restored": [],
            "empty_not_restored_isolated": [],
            "swap_mismatch": [],
        }
    )


def test_write_run_two_term_formula_can_fail(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "two_term_round_count", lambda _r: -1)
    run = write_run(tmp_path, 2, 3, SMALL)
    assert run["two_term_rounds_equal_closed_form"] is False
    assert not cli.run_ok(run)
    deep = write_run(tmp_path, 3, 3, SMALL)
    assert deep["two_term_rounds_equal_closed_form"] is None


def test_shallow_count_and_recorded_cost_failure(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    shallow = explore(empty(), 3, 1)
    block = compare_with_ninth(shallow)
    assert block["explored_equals_independent_count"]
    real = explore_recorded

    def bump(bound: int, rounds: int) -> RecordedExploration:
        expl = real(bound, rounds)
        first = next(iter(expl.depth))
        expl.depth[first] = expl.depth[first] + 10
        return expl

    monkeypatch.setattr(evidence, "explore_recorded", bump)
    doc = write_recorded(tmp_path, 2, 2)
    count = doc["recorded_cost_failure_count"]
    assert isinstance(count, int) and count >= 1


def test_write_recorded_and_given(tmp_path: Path) -> None:
    given = write_given(tmp_path)
    recorded = write_recorded(tmp_path, 2, 5)
    assert given["r_record_not_s"]
    assert recorded_ok(recorded)
    assert (tmp_path / "given.json").is_file() and (tmp_path / "recorded.json").is_file()


def test_main_writes_and_checks(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    out = tmp_path / "evidence" / "twelfth"
    argv = [
        "--out",
        str(out),
        "--bound",
        "2",
        "--rounds",
        "3",
        "--deep-bound",
        "2",
        "--deep-rounds",
        "2",
        "--two-term-rounds",
        "3",
        "--log-bound",
        "2",
        "--log-rounds",
        "2",
        "--recorded-bound",
        "2",
        "--recorded-rounds",
        "4",
    ]
    assert cli.main(argv) == 0
    capsys.readouterr()
    assert cli.main(argv + ["--check"]) == 0
    out2 = capsys.readouterr().out
    assert "check: identical" in out2
    (out / "given.json").write_text("{}", encoding="utf-8")
    assert cli.main(argv + ["--check"]) == 1
