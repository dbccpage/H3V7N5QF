from __future__ import annotations

import dataclasses
import json
from pathlib import Path

import pytest

from xry.changes import Answer, AnswerKind, Change
from xry.state import Sameness, State

import run_seventeenth
from seventeenth import __main__ as cli
from seventeenth import evidence
from seventeenth.evidence import (
    RESULT_HEADER,
    LoopCheck,
    Plan,
    check_bounds,
    disagreements,
    passes,
    write_all,
)
from seventeenth.explore import Closure, closure_unobstructed, with_loop
from seventeenth.loop import obstructed_m1


SMALL = Plan(bound=2, rounds=4, log_bound=2, log_rounds=2)


def test_check_bounds_passes_and_records_both_readings() -> None:
    report = check_bounds(2, 4)
    assert passes(report)
    assert report.replace_results > 0
    assert report.perform_results > report.replace_results
    assert not report.replace_has_xrx
    assert len(report.by_run) == 4
    assert len(report.unexpanded_by_run) == 4
    assert report.frontier


def test_passes_rejects_a_disagreement() -> None:
    blank = check_bounds(2, 1)
    # rounds 1 still passes; a hand-filled list does not
    assert passes(blank)
    # One round leaves every round-1 result unexpanded: those are frontier too.
    assert any(item.endswith("|rounds") for item in blank.frontier)
    names = list(disagreements(blank))
    assert len(names) == 12
    for name in names:
        broken = dataclasses.replace(blank)
        setattr(broken, name, ["x"])
        assert not passes(broken), name
    failed = LoopCheck(
        ["x"],
        [],
        [],
        [],
        [],
        [],
        [],
        [],
        [],
        [],
        [],
        [],
        0,
        0,
    )
    assert not passes(failed)


def test_write_all_round_trip(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    assert summary["passes"] is True
    text = (tmp_path / "summary.json").read_text(encoding="utf-8")
    assert json.loads(text)["passes"] is True
    log = (tmp_path / "attempts_bound2_rounds2.jsonl").read_text(encoding="utf-8")
    assert "replace" in log and "perform" in log
    unexpanded = summary["unexpanded_by_run"]
    assert isinstance(unexpanded, list) and len(unexpanded) == 4
    rows = (tmp_path / "results_bound2_rounds4.csv").read_text(encoding="utf-8").splitlines()
    assert rows[0] == ",".join(RESULT_HEADER)
    readings = {row.split(",")[1] for row in rows[1:]}
    assert readings == {"replace", "perform"}
    assert any(row.endswith(",1") for row in rows[1:]) and any(row.endswith(",0") for row in rows[1:])
    again = write_all(tmp_path)
    assert again["bound"] == Plan.bound and again["passes"] is True
    assert run_seventeenth.__name__ == "run_seventeenth"


def test_main_writes_and_checks(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    out = tmp_path / "evidence"
    assert cli.main(["--out", str(out), "--bound", "2", "--rounds", "3"]) == 0
    assert cli.main(["--out", str(out), "--bound", "2", "--rounds", "3", "--check"]) == 0
    (out / "summary.json").write_text("{}\n", encoding="utf-8")
    assert cli.main(["--out", str(out), "--bound", "2", "--rounds", "3", "--check"]) == 1
    monkeypatch.setattr(evidence, "check_bounds", lambda bound, rounds: _bad())
    assert cli.main(["--out", str(out), "--bound", "2", "--rounds", "2"]) == 1


def _bad() -> LoopCheck:
    good = check_bounds(2, 2)
    return LoopCheck(
        ["loop"],
        good.replace_not_base,
        good.replace_cost_mismatch,
        good.replace_not_formula,
        good.perform_misses_witness,
        good.perform_cost_not_above,
        good.m_disagree_loopfree,
        good.m_agree_on_loop,
        good.remove_first_differs,
        good.refusal_changes_something,
        good.loop_beginning_in_replace,
        good.loop_beginning_not_in_perform,
        good.replace_results,
        good.perform_results,
    )


def test_injections_fire_each_disagreement(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "has_xrx", lambda state: True)
    assert check_bounds(2, 2).replace_has_xrx
    monkeypatch.undo()

    monkeypatch.setattr(
        evidence,
        "closure_unobstructed",
        lambda start, bound, rounds, keep_log=False: Closure(depth={}, frontier=()),
    )
    assert check_bounds(2, 2).replace_not_base
    monkeypatch.undo()

    monkeypatch.setattr(evidence, "cost", lambda state, bra: -1)
    assert check_bounds(2, 2).replace_cost_mismatch
    monkeypatch.undo()

    monkeypatch.setattr(evidence, "by_cost", lambda bound, rounds, bra, sameness: set())
    assert check_bounds(2, 2).replace_not_formula
    monkeypatch.undo()

    def only_start(start: State, bound: int, rounds: int, keep_log: bool = False) -> Closure:
        del bound, rounds, keep_log
        return Closure(depth={start: 0}, frontier=())

    monkeypatch.setattr(evidence, "closure_perform", only_start)
    missed = check_bounds(2, 2)
    assert missed.perform_misses_witness
    assert missed.loop_beginning_not_in_perform
    monkeypatch.undo()

    monkeypatch.setattr(evidence, "cost", lambda state, bra: 0)
    assert check_bounds(2, 2).perform_cost_not_above
    monkeypatch.undo()

    monkeypatch.setattr(evidence, "outcome_has_xrx", lambda state, change: True)
    assert check_bounds(2, 2).m_disagree_loopfree
    monkeypatch.undo()

    monkeypatch.setattr(evidence, "outcome_has_xrx", lambda state, change: obstructed_m1(state, change))
    assert check_bounds(2, 2).m_agree_on_loop
    monkeypatch.undo()

    def bad_remove(state: State, change: object) -> tuple[Answer, ...]:
        del change
        return (Answer(AnswerKind.REMOVE_OBSTRUCTION, (), True, state),)

    monkeypatch.setattr(evidence, "answers", bad_remove)
    assert check_bounds(2, 2).remove_first_differs
    monkeypatch.undo()

    def bad_refuse(state: State, change: Change) -> tuple[Answer, ...]:
        del change
        return ()

    monkeypatch.setattr(evidence, "answers", bad_refuse)
    assert check_bounds(2, 2).refusal_changes_something
    monkeypatch.undo()

    real = closure_unobstructed

    def extra(start: State, bound: int, rounds: int, keep_log: bool = False) -> Closure:
        got = real(start, bound, rounds, keep_log)
        got.depth[with_loop(False, Sameness.ANCHORED)] = 1
        return got

    monkeypatch.setattr(evidence, "closure_unobstructed", extra)
    assert check_bounds(2, 2).loop_beginning_in_replace
    monkeypatch.undo()


