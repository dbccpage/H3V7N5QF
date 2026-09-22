from __future__ import annotations

import json
from pathlib import Path

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from fourteenth import __main__ as cli
from fourteenth import evidence
from fourteenth.evidence import (
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
from fourteenth.explore import explore
from fourteenth.invariants import check_leftovers
from fourteenth.leftover import leftover_merge, leftover_nothing, leftover_pair

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
    assert given["r_and_s_same_leftover"] and given["leftover_not_assertion"] and given["leftover_not_answer"]
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["results_that_reach_what_is_given"] == 1
        if run["rounds"] >= 4:
            assert "leaves_nothing" not in run["leftover_statements_holding_of_every_change"]
    assert tagged_ok(tagged)
    assert tagged["one_term_nothing_cost"] == 1
    pair_cost = tagged["one_term_pair_cost"]
    assert pair_cost is not None and int(str(pair_cost)) > 1
    names = {p.name for p in tmp_path.iterdir()}
    assert "given.json" in names and "tagged.json" in names and "summary.json" in names
    assert "attempts_bound2_rounds2.jsonl" in names
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given_doc["the_first_change_leaves_nothing"]
    assert given_doc["r_and_s_same_leftover"]
    assert given_doc["pair_written_uses_neither_r_nor_s"]
    two = runs["bound2_rounds4"]
    assert two["two_term_rounds_equal_closed_form"] is True
    assert two["leftovers"]["three_kinds_inhabited"] is True


def test_check_leftovers_reports_disagreements(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 2, 4)
    edges = check_leftovers(expl)
    assert edges.checked > 0 and not edges.additions_not_nothing and not edges.removals_not_pair
    assert not edges.identify_not_merge and not edges.assertion_writings
    assert not edges.answer_writings and not edges.clearing_kind and not edges.cross_relation_disagree
    assert edges.nothing and edges.pair and edges.merge
    monkeypatch.setattr("fourteenth.explore.leftover_of", lambda _s, _c: leftover_merge(0, 1))
    forced_add = check_leftovers(expl)
    assert forced_add.additions_not_nothing and forced_add.removals_not_pair
    monkeypatch.setattr("fourteenth.explore.leftover_of", lambda _s, _c: leftover_nothing())
    forced = check_leftovers(expl)
    assert forced.removals_not_pair and forced.identify_not_merge
    monkeypatch.setattr("fourteenth.explore.leftover_of", evidence.leftover_of)
    # Make the leftover relation-dependent, so a removal in `s` disagrees with
    # the removal in `r` of the same pair (the cross-relation check fires only
    # where both removals are legal changes).
    monkeypatch.setattr(
        "fourteenth.invariants.leftover_of",
        lambda s, c: leftover_pair(9, 9) if c.rel == "s" else evidence.leftover_of(s, c),
    )
    forced_cross = check_leftovers(expl)
    assert forced_cross.cross_relation_disagree
    monkeypatch.setattr("fourteenth.invariants.leftover_of", evidence.leftover_of)
    monkeypatch.setattr("fourteenth.leftover.LeftWriting.is_assertion", lambda self: True)
    assert check_leftovers(expl).assertion_writings
    monkeypatch.setattr("fourteenth.leftover.LeftWriting.is_assertion", lambda self: False)
    monkeypatch.setattr("fourteenth.leftover.LeftWriting.is_answer", lambda self: True)
    assert check_leftovers(expl).answer_writings
    monkeypatch.setattr("fourteenth.leftover.LeftWriting.is_answer", lambda self: False)
    monkeypatch.setattr("fourteenth.invariants.clearing_is_a_kind", lambda _w: True)
    assert check_leftovers(expl).clearing_kind


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
    expl2 = explore(empty(), 2, 3)
    gone = next(s for s in list(expl2.depth) if s.n == 0)
    expl2.depth.pop(gone)
    ninth_depth = explore_ninth(empty(), 2, 3).depth
    assert gone not in expl2.depth and gone in ninth_depth
    fake = dict(good)
    fake["round_disagreements"] = ["shifted"]
    assert not ninth_ok(fake)


def test_tagged_and_leftovers_ok_can_fail() -> None:
    assert not tagged_ok(
        {
            "more_results_than_the_ninth": False,
            "tagged_cost_exceeds_size": True,
            "one_term_nothing_cost": 1,
            "one_term_size": 1,
            "one_term_pair_cost": 3,
        }
    )
    assert not leftovers_ok(
        {
            "split_agrees": False,
            "checked": 1,
            "additions_not_nothing": [],
            "removals_not_pair": [],
            "identify_not_merge": [],
            "assertion_writings": [],
            "answer_writings": [],
            "clearing_kind": [],
            "cross_relation_disagree": [],
        }
    )
    assert leftovers_ok({"checked": 0})


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
    assert given["r_and_s_same_leftover"]
    assert tagged_ok(tagged)
    assert (tmp_path / "given.json").is_file() and (tmp_path / "tagged.json").is_file()


def test_main_writes_and_checks(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    out = tmp_path / "evidence" / "fourteenth"
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
    capsys.readouterr()
    assert cli.main(argv + ["--check"]) == 0
    out2 = capsys.readouterr().out
    assert "check: identical" in out2
    (out / "given.json").write_text("{}", encoding="utf-8")
    assert cli.main(argv + ["--check"]) == 1
