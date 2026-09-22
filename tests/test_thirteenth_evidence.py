from __future__ import annotations

import json
from pathlib import Path

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from thirteenth import __main__ as cli
from thirteenth import evidence
from thirteenth.evidence import (
    Plan,
    coarse_ok,
    coarses_ok,
    compare_with_ninth,
    ninth_ok,
    run_tag,
    write_all,
    write_coarse,
    write_given,
    write_run,
)
from thirteenth.explore import CoarseExploration, explore, explore_coarse
from thirteenth.invariants import check_coarses
from thirteenth.coarse import determines, splits, swap_keeps_coarse

SMALL = Plan(
    bound=3,
    rounds=4,
    deep_bound=2,
    deep_rounds=3,
    two_term_rounds=4,
    log_bound=2,
    log_rounds=2,
    coarse_bound=2,
    coarse_rounds=5,
)


def test_plan() -> None:
    assert Plan().bound == 3 and Plan().rounds == 6 and Plan().coarse_bound == 2
    assert Plan().runs() == ((3, 6), (3, 5), (2, 8)) and SMALL.runs() == ((3, 4), (2, 3), (2, 4))
    assert run_tag(3, 4) == "bound3_rounds4"


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    coarse = summary["coarse"]
    given = summary["given"]
    assert isinstance(runs, dict) and isinstance(coarse, dict) and isinstance(given, dict)
    assert given["r_and_s_same_coarser"] and given["r_and_s_differ_finer"]
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["results_that_reach_what_is_given"] == 1
        if run["rounds"] >= 3:
            assert "determines_finer" not in run["coarse_statements_holding_of_every_result"]
    assert coarse_ok(coarse)
    names = {p.name for p in tmp_path.iterdir()}
    assert "given.json" in names and "coarse.json" in names and "summary.json" in names
    assert "attempts_bound2_rounds2.jsonl" in names
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given_doc["r_and_s_same_coarser"]
    assert not given_doc["two_term_between_determines"]
    assert given_doc["empty_determines"]
    two = runs["bound2_rounds4"]
    assert two["two_term_rounds_equal_closed_form"] is True
    assert two["coarses"]["not_determines_count"] >= 1


def test_check_coarses_reports_disagreements(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 2, 4)
    edges = check_coarses(expl)
    assert edges.checked > 0 and not edges.not_sum and not edges.not_size
    assert not edges.not_swap and not edges.determines_when_asserted
    assert edges.determines_count and edges.not_determines_count
    monkeypatch.setattr("thirteenth.invariants.determines", lambda _s: True)
    forced = check_coarses(expl)
    assert forced.determines_when_asserted
    monkeypatch.setattr("thirteenth.invariants.determines", lambda _s: False)
    forced_empty = check_coarses(expl)
    assert forced_empty.not_determines_when_empty
    monkeypatch.setattr("thirteenth.invariants.determines", determines)
    monkeypatch.setattr("thirteenth.invariants.swap_keeps_coarse", lambda _s: False)
    forced_swap = check_coarses(expl)
    assert forced_swap.not_swap
    monkeypatch.setattr("thirteenth.invariants.swap_keeps_coarse", swap_keeps_coarse)
    monkeypatch.setattr("thirteenth.invariants.splits", lambda _s: -1)
    forced_splits = check_coarses(expl)
    assert forced_splits.splits_mismatch
    monkeypatch.setattr("thirteenth.invariants.splits", splits)
    monkeypatch.setattr("thirteenth.invariants.add_r_or_s_same_coarser", lambda *_a: False)
    monkeypatch.setattr("thirteenth.invariants.same_coarser", lambda *_a: False)
    forced_add = check_coarses(expl)
    assert forced_add.add_r_s_fail
    from fourth.state import MState
    from thirteenth.invariants import _splits_of

    monkeypatch.setattr(
        "thirteenth.invariants.coarse",
        lambda s: MState(s.n, (0,) * (s.n * s.n), None),
    )
    forced_sum = check_coarses(expl)
    assert forced_sum.not_sum
    assert _splits_of("no") == -1
    assert coarses_ok({"checked": 0})


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
    expl2 = explore(empty(), 2, 3)
    gone = next(s for s in list(expl2.depth) if s.n == 0)
    expl2.depth.pop(gone)
    ninth_depth = explore_ninth(empty(), 2, 3).depth
    assert gone not in expl2.depth and gone in ninth_depth


def test_coarse_and_coarses_ok_can_fail() -> None:
    assert not coarse_ok(
        {
            "fewer_results_than_the_ninth": False,
            "extra_results": 0,
            "between_and_swap_same_coarse": True,
            "between_and_swap_differ_finer": True,
            "one_term_coarse_cost": 1,
            "one_term_size": 1,
            "coarse_cost_failure_count": 0,
            "coarse_cost_equals_size": True,
            "explored_equals_seventh_count": True,
        }
    )
    assert not coarses_ok(
        {
            "split_agrees": False,
            "checked": 1,
            "not_sum": [],
            "not_size": [],
            "not_swap": [],
            "determines_when_asserted": [],
            "not_determines_when_empty": [],
            "splits_mismatch": [],
            "add_r_s_fail": [],
        }
    )


def test_write_run_two_term_formula_can_fail(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "two_term_round_count", lambda _r: -1)
    run = write_run(tmp_path, 2, 3, SMALL)
    assert run["two_term_rounds_equal_closed_form"] is False
    assert not cli.run_ok(run)
    deep = write_run(tmp_path, 3, 3, SMALL)
    assert deep["two_term_rounds_equal_closed_form"] is None


def test_shallow_count_and_coarse_cost_failure(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    shallow = explore(empty(), 3, 1)
    block = compare_with_ninth(shallow)
    assert block["explored_equals_independent_count"]
    real = explore_coarse

    def bump(bound: int, rounds: int) -> CoarseExploration:
        expl = real(bound, rounds)
        first = next(iter(expl.depth))
        expl.depth[first] = expl.depth[first] + 10
        return expl

    monkeypatch.setattr(evidence, "explore_coarse", bump)
    doc = write_coarse(tmp_path, 2, 2)
    count = doc["coarse_cost_failure_count"]
    assert isinstance(count, int) and count >= 1


def test_write_coarse_and_given(tmp_path: Path) -> None:
    given = write_given(tmp_path)
    coarse = write_coarse(tmp_path, 2, 5)
    assert given["r_and_s_same_coarser"]
    assert coarse_ok(coarse)
    assert (tmp_path / "given.json").is_file() and (tmp_path / "coarse.json").is_file()


def test_main_writes_and_checks(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    out = tmp_path / "evidence" / "thirteenth"
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
        "--coarse-bound",
        "2",
        "--coarse-rounds",
        "4",
    ]
    assert cli.main(argv) == 0
    capsys.readouterr()
    assert cli.main(argv + ["--check"]) == 0
    out2 = capsys.readouterr().out
    assert "check: identical" in out2
    (out / "given.json").write_text("{}", encoding="utf-8")
    assert cli.main(argv + ["--check"]) == 1
