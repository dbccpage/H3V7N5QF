from __future__ import annotations

import json
from pathlib import Path

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from tenth import __main__ as cli
from tenth import evidence
from tenth.evidence import (
    Plan,
    compare_with_ninth,
    leftovers_ok,
    ninth_ok,
    run_tag,
    tagged_ok,
    write_all,
    write_given,
    write_run,
    write_tagged,
)
from tenth.explore import explore, leftover_performed
from tenth.invariants import check_leftovers
from tenth.leftover import LeftOver

SMALL = Plan(
    bound=3,
    rounds=4,
    deep_bound=2,
    deep_rounds=3,
    two_term_rounds=4,
    log_bound=2,
    log_rounds=2,
    tagged_bound=2,
    tagged_rounds=4,
)


def test_plan() -> None:
    assert Plan().bound == 3 and Plan().rounds == 6 and Plan().tagged_bound == 2
    assert Plan().runs() == ((3, 6), (3, 5), (2, 8)) and SMALL.runs() == ((3, 4), (2, 3), (2, 4))
    assert run_tag(3, 4) == "bound3_rounds4"


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    tagged = summary["tagged"]
    given = summary["given"]
    assert isinstance(runs, dict) and isinstance(tagged, dict) and isinstance(given, dict)
    assert given["three_outcomes_inhabited"] and given["leftover_of_the_first_change"] == "nothing left"
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["results_that_reach_what_is_given"] == 1
        if run["rounds"] >= 4:
            assert run["leftover_statements_holding_of_every_change"] == []
    assert tagged_ok(tagged)
    assert tagged["one_term_nothing_left_cost"] == 1 and tagged["one_term_clearable_cost"] == 3
    names = {p.name for p in tmp_path.iterdir()}
    assert "given.json" in names and "tagged.json" in names and "summary.json" in names
    assert "attempts_bound2_rounds2.jsonl" in names
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given_doc["the_first_change_leaves_nothing"]
    assert given_doc["two_term_empty_identify_leftover"] == "a leftover that a later change of the four kinds can clear"
    assert given_doc["two_term_between_identify_leftover"] == "a leftover that none of them can"
    assert not given_doc["other_relation_clears_a_removal"]
    two = runs["bound2_rounds4"]
    assert two["two_term_rounds_equal_closed_form"] is True
    assert two["leftovers"]["three_outcomes_inhabited"] is True


def test_check_leftovers_reports_disagreements(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 2, 4)
    edges = check_leftovers(expl)
    assert edges.checked > 0 and not edges.additions_not_nothing and not edges.removals_not_clearable
    assert not edges.other_relation_cleared and not edges.identify_disagreements and not edges.clearing_failed
    assert edges.nothing_left and edges.clearable and edges.uncleared
    monkeypatch.setattr("tenth.explore.leftover_of", lambda _s, _c: LeftOver.UNCLEARED)
    forced_add = check_leftovers(expl)
    assert forced_add.additions_not_nothing and forced_add.removals_not_clearable
    monkeypatch.setattr("tenth.explore.leftover_of", lambda _s, _c: LeftOver.NOTHING_LEFT)
    forced = check_leftovers(expl)
    assert forced.removals_not_clearable and forced.identify_disagreements
    monkeypatch.setattr("tenth.invariants.other_clears", lambda _s, _c: True)
    monkeypatch.setattr("tenth.explore.leftover_of", lambda s, c: evidence.leftover_of(s, c))
    forced_other = check_leftovers(expl)
    assert forced_other.other_relation_cleared
    monkeypatch.setattr("tenth.invariants.clearing_change", lambda _c: None)
    assert check_leftovers(expl).clearing_failed


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
    shallow = explore(empty(), 3, 1)
    assert compare_with_ninth(shallow)["explored_equals_independent_count"]
    # A shifted round or a lost result is refused by the sequence count itself,
    # so the count is held at the unshifted exploration's to reach the round
    # and result comparisons.
    shifted = explore(empty(), 2, 3)
    fair = real_seq(shifted)
    monkeypatch.setattr(evidence, "count_shortest_sequences", lambda _e: fair)
    one = next(s for s in shifted.depth if s.n == 1)
    shifted.depth[one] += 1
    moved = compare_with_ninth(shifted)
    assert not ninth_ok(moved) and moved["round_disagreements"] == [one.key()]
    expl2 = explore(empty(), 2, 3)
    gone = next(s for s in list(expl2.depth) if s.n == 0)
    expl2.depth.pop(gone)
    lost = compare_with_ninth(expl2)
    assert not ninth_ok(lost) and lost["missing_results"] == [gone.key()]
    assert not lost["explored_equals_independent_count"]


def test_bare_criterion_agrees_with_the_search_and_catches_a_wrong_outcome(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tenth.invariants import bare, bare_criterion
    from tenth.leftover import leftover_of, restores_in_one
    from tenth.changes import Change, Kind, changes

    loop_on_one = DState.of(2, [(1, 1)], [])
    ident = Change(Kind.IDENTIFY, "", 0, 1)
    assert bare(loop_on_one, 0) and not bare(loop_on_one, 1)
    assert bare_criterion(loop_on_one, ident) is LeftOver.CLEARABLE is leftover_of(loop_on_one, ident)
    two_loops = DState.of(2, [(0, 0)], [(1, 1)])
    assert bare_criterion(two_loops, ident) is LeftOver.UNCLEARED is leftover_of(two_loops, ident)
    expl = explore(empty(), 3, 4)
    seen = 0
    for state, change, _out, _left in leftover_performed(expl):
        if change.kind is Kind.IDENTIFY:
            seen += 1
            assert (bare_criterion(state, change) is LeftOver.CLEARABLE) == restores_in_one(state, change)
    assert seen > 0 and all(c.kind is not Kind.IDENTIFY for c in changes(empty()))
    flipped = {LeftOver.CLEARABLE: LeftOver.UNCLEARED, LeftOver.UNCLEARED: LeftOver.CLEARABLE}

    def wrong(state: DState, change: Change) -> LeftOver:
        right = leftover_of(state, change)
        return flipped.get(right, right) if change.kind is Kind.IDENTIFY else right

    monkeypatch.setattr("tenth.explore.leftover_of", wrong)
    assert check_leftovers(expl).identify_disagreements


def test_tagged_and_leftovers_ok_can_fail() -> None:
    assert not tagged_ok(
        {
            "more_results_than_the_ninth": False,
            "tagged_cost_exceeds_size": True,
            "one_term_nothing_left_cost": 1,
            "one_term_size": 1,
            "one_term_clearable_cost": 3,
        }
    )
    assert not leftovers_ok(
        {
            "split_agrees": False,
            "checked": 1,
            "additions_not_nothing": [],
            "removals_not_clearable": [],
            "other_relation_cleared": [],
            "identify_disagreements": [],
            "clearing_failed": [],
        }
    )


def test_write_run_two_term_formula_can_fail(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "two_term_round_count", lambda _r: -1)
    run = write_run(tmp_path, 2, 3, SMALL)
    assert run["two_term_rounds_equal_closed_form"] is False
    assert not cli.run_ok(run)
    deep = write_run(tmp_path, 3, 3, SMALL)
    assert deep["two_term_rounds_equal_closed_form"] is None


def test_write_tagged_and_given(tmp_path: Path) -> None:
    given = write_given(tmp_path)
    tagged = write_tagged(tmp_path, 2, 4)
    assert given["three_outcomes_inhabited"]
    assert tagged_ok(tagged)
    assert (tmp_path / "given.json").is_file() and (tmp_path / "tagged.json").is_file()


def test_main_writes_and_checks(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    out = tmp_path / "evidence" / "tenth"
    argv = [
        "--out",
        str(out),
        "--bound",
        "2",
        "--rounds",
        "4",
        "--deep-bound",
        "2",
        "--deep-rounds",
        "3",
        "--two-term-rounds",
        "4",
        "--log-bound",
        "2",
        "--log-rounds",
        "2",
        "--tagged-bound",
        "2",
        "--tagged-rounds",
        "4",
    ]
    assert cli.main(argv) == 0
    assert "pass" in capsys.readouterr().out
    assert cli.main(argv + ["--check"]) == 0
    assert "identical" in capsys.readouterr().out
    (out / "given.json").write_text("{}\n", encoding="utf-8")
    assert cli.main(argv + ["--check"]) == 1
    assert "check:" in capsys.readouterr().out
