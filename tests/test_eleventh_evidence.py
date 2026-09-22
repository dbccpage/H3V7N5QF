from __future__ import annotations

import json
from pathlib import Path

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from eleventh import __main__ as cli
from eleventh import evidence
from eleventh.evidence import (
    Plan,
    compare_with_ninth,
    labeled_ok,
    ninth_ok,
    run_tag,
    write_all,
    write_given,
    write_labeled,
    write_run,
    writings_ok,
)
from eleventh.explore import LabeledExploration, explore, explore_labeled
from eleventh.invariants import check_writings
from eleventh.writing import determines

SMALL = Plan(
    bound=3,
    rounds=4,
    deep_bound=2,
    deep_rounds=3,
    two_term_rounds=4,
    log_bound=2,
    log_rounds=2,
    labeled_bound=2,
    labeled_rounds=4,
)


def test_plan() -> None:
    assert Plan().bound == 3 and Plan().rounds == 6 and Plan().labeled_bound == 2
    assert Plan().runs() == ((3, 6), (3, 5), (2, 8)) and SMALL.runs() == ((3, 4), (2, 3), (2, 4))
    assert run_tag(3, 4) == "bound3_rounds4"


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    labeled = summary["labeled"]
    given = summary["given"]
    assert isinstance(runs, dict) and isinstance(labeled, dict) and isinstance(given, dict)
    assert given["r_collision_not_s"] and given["identify_drops_a_term"]
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["results_that_reach_what_is_given"] == 1
        if run["rounds"] >= 4:
            assert "collides" not in run["writing_statements_holding_of_every_writing"]
    assert labeled_ok(labeled)
    names = {p.name for p in tmp_path.iterdir()}
    assert "given.json" in names and "labeled.json" in names and "summary.json" in names
    assert "attempts_bound2_rounds2.jsonl" in names
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given_doc["two_term_between_collide_determines_s"]
    assert not given_doc["two_term_between_collide_determines_r"]
    assert given_doc["identify_drops_a_term"] and given_doc["collide_keeps_two_terms"]
    assert given_doc["collision_forbids_coarser"]
    two = runs["bound2_rounds4"]
    assert two["two_term_rounds_equal_closed_form"] is True
    assert two["writings"]["colliding"] >= 1


def test_check_writings_reports_disagreements(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 2, 4)
    edges = check_writings(expl)
    assert edges.checked > 0 and not edges.injective_not_determining
    assert not edges.coarser_of_collision_determines
    assert not edges.identify_kept_both_terms and not edges.collide_dropped_a_term
    assert edges.injective_writings and edges.determining and edges.colliding and edges.r_not_s
    monkeypatch.setattr("eleventh.invariants.determines", lambda _s, _w: False)
    forced = check_writings(expl)
    assert forced.injective_not_determining
    monkeypatch.setattr("eleventh.invariants.determines", lambda _s, w: w != (0, 1))
    forced_coarse = check_writings(expl)
    assert forced_coarse.coarser_of_collision_determines
    monkeypatch.setattr("eleventh.invariants.determines", determines)
    monkeypatch.setattr("eleventh.invariants.perform", lambda _s, _c: DState.of(2, [], []))
    forced_id = check_writings(expl)
    assert forced_id.identify_kept_both_terms
    monkeypatch.setattr("eleventh.invariants.terms_after_writing", lambda _s, _w: 0)
    forced_w = check_writings(expl)
    assert forced_w.collide_dropped_a_term


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
    # A shifted round or a lost result is refused by the sequence count itself,
    # so it is held at the unshifted count to reach the round and result checks.
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


def test_labeled_of_merges_automorphic_writings_at_three_terms() -> None:
    from eleventh.changes import labeled_of
    from eleventh.writing import orbit_count_burnside, writings

    bare_three = DState.of(3, [], [])
    labeled = labeled_of(bare_three)
    writings_seen = {lab.writing for lab in labeled}
    # The five writings of three terms are all-same, all-distinct, and three
    # "one pair shares a letter" writings; under the bare state's full symmetry
    # those three are one orbit, so five writings give three labeled results.
    assert len(labeled) == len(writings_seen) == orbit_count_burnside(bare_three) == 3
    assert len(writings(3)) == 5
    assert (0, 0, 1) in writings_seen and (0, 1, 0) not in writings_seen and (0, 1, 1) not in writings_seen
    # At two terms every writing is its own orbit, so nothing merges there.
    for state in (DState.of(2, [], []), DState.of(2, [(0, 1)], []), DState.of(2, [(0, 0)], [(1, 1)])):
        assert len(labeled_of(state)) == orbit_count_burnside(state) == len(writings(2)) == 2


def test_labeled_and_writings_ok_can_fail() -> None:
    assert not labeled_ok(
        {
            "more_results_than_the_ninth": False,
            "labeled_equals_orbit_count": True,
            "labeled_cost_equals_size": True,
            "two_term_empty_apart_cost": 2,
            "two_term_empty_size": 2,
            "two_term_empty_collide_cost": 2,
            "apart_and_collide_are_two_results": True,
        }
    )
    assert not writings_ok(
        {
            "split_agrees": False,
            "checked": 1,
            "injective_not_determining": [],
            "coarser_of_collision_determines": [],
            "identify_kept_both_terms": [],
            "collide_dropped_a_term": [],
        }
    )


def test_write_run_two_term_formula_can_fail(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "two_term_round_count", lambda _r: -1)
    run = write_run(tmp_path, 2, 3, SMALL)
    assert run["two_term_rounds_equal_closed_form"] is False
    assert not cli.run_ok(run)
    deep = write_run(tmp_path, 3, 3, SMALL)
    assert deep["two_term_rounds_equal_closed_form"] is None


def test_shallow_count_and_read_written(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    shallow = explore(empty(), 3, 1)
    block = compare_with_ninth(shallow)
    assert block["explored_equals_independent_count"]
    written = evidence._read_written({"r": {(0, 1): 1}, "s": {}})
    assert written == {"r": {"0,1": 1}, "s": {}}
    assert evidence._read_written(None) is None
    real = explore_labeled

    def bump(bound: int, rounds: int) -> LabeledExploration:
        expl = real(bound, rounds)
        first = next(iter(expl.depth))
        expl.depth[first] = expl.depth[first] + 10
        return expl

    monkeypatch.setattr(evidence, "explore_labeled", bump)
    doc = write_labeled(tmp_path, 2, 2)
    count = doc["labeled_cost_failure_count"]
    assert isinstance(count, int) and count >= 1
    assert not labeled_ok(doc)


def test_write_labeled_and_given(tmp_path: Path) -> None:
    given = write_given(tmp_path)
    labeled = write_labeled(tmp_path, 2, 4)
    assert given["r_collision_not_s"]
    assert labeled_ok(labeled)
    assert (tmp_path / "given.json").is_file() and (tmp_path / "labeled.json").is_file()


def test_main_writes_and_checks(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    out = tmp_path / "evidence" / "eleventh"
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
        "--labeled-bound",
        "2",
        "--labeled-rounds",
        "4",
    ]
    assert cli.main(argv) == 0
    assert "pass" in capsys.readouterr().out
    assert cli.main(argv + ["--check"]) == 0
    assert "identical" in capsys.readouterr().out
    (out / "given.json").write_text("{}\n", encoding="utf-8")
    assert cli.main(argv + ["--check"]) == 1
    assert "check:" in capsys.readouterr().out
