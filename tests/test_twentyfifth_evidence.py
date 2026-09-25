"""The evidence writer, and an injection test for every disagreement branch of every check."""

from __future__ import annotations

import json
from collections.abc import Iterable
from pathlib import Path
from typing import Any

import pytest

from twentythird.explore import explore as real_explore23
from twentythird.state import DState

from twentyfifth import evidence
from twentyfifth.embed import EmbedReport
from twentyfifth.evidence import (
    FillingCheck,
    Plan,
    audit,
    check_changes,
    check_counts,
    check_decide,
    check_embed,
    check_read_back,
    check_reach,
    check_readings,
    check_results,
    check_whether,
    mark_text,
    run_tag,
    write_all,
)
from twentyfifth.explore import Exploration, Grouped, explore
from twentyfifth.explore import explore as real_explore
from twentyfifth.explore import performed as real_performed
from twentyfifth.readings import ReadingRun
from twentyfifth.readings import explore_reading as real_reading
from twentyfifth.state import FState, Mark, result_mark

SMALL = Plan(
    bound=3,
    rounds=5,
    deep_bound=2,
    deep_rounds=4,
    two_term_rounds=5,
    log_bound=3,
    log_rounds=4,
    reach_bound=3,
    reach_rounds=4,
    readings_bound=3,
    readings_rounds=5,
    decide_terms=4,
    search_terms=3,
    unseen_terms=3,
    unseen_full_upto=4,
    keeping_terms=3,
    count_runs=((3, 5),),
)

TINY = Plan(readings_bound=3, readings_rounds=4, decide_terms=3, search_terms=3)


def test_plan_and_tag() -> None:
    assert Plan().runs() == ((5, 8), (3, 10), (2, 24))
    assert run_tag(3, 4) == "bound3_rounds4"
    assert mark_text((3, (0,) * 9, ((0, 1, 2),))) == "3:0,0,0,0,0,0,0,0,0|012"


def test_audit_is_clean() -> None:
    check = audit(3, 5)
    assert check.clean()
    assert set(check.as_dict()) == set(FillingCheck.__dataclass_fields__)
    assert audit(2, 3, SMALL).clean()


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    assert summary["every_check_clean"] is True
    names = {p.name for p in tmp_path.iterdir()}
    assert {"given.json", "summary.json", "counts.csv", "readings.json", "decide.csv", "unseen.csv"} <= names
    assert "results_bound3_rounds5.csv" in names and "reach_bound3_rounds4.csv" in names
    assert "attempts_bound3_rounds4.jsonl" in names and "records_bound3_rounds5.csv" in names
    given = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    witnesses = given["the_twentythird_record_does_not_show_which_terms"]
    assert [w["record"] for w in witnesses] == [[2, 1, 0], [2, 1, 0], [3, 1, 1], [3, 1, 1], [3, 1, 1]]
    assert [len(w["least_sets_keeping_it_from_nothing"][0]) for w in witnesses] == [1, 2, 1, 2, 3]
    assert given["a_loop_is_never_gone_along"] == {"state": given["a_loop_is_never_gone_along"]["state"],
                                                   "told": False, "the_result_asserting_nothing": False}
    assert given["a_two_way_sum_seen_one_way_round"]["balances_a_b_c"] is False
    assert given["a_two_way_sum_seen_one_way_round"]["balances_a_c_b"] is True
    assert given["blind_with_four_terms"]["blind"] is True and given["blind_with_four_terms"]["nothing"] is False
    assert given["identifying_two_terms_of_a_filled_triple"]["cost"] == 4
    assert given["identifying_two_terms_of_a_filled_triple"]["cost_after"] == 2
    assert given["the_map_back"]["on_a_b_c_filled_a_b_c"] is None
    runs = summary["runs"]
    assert isinstance(runs, dict)
    first = runs["bound3_rounds5"]
    assert first["map_back"]["first_result_answered_none"] == "terms a b c; asserted nothing; filled abc"
    assert first["the_twentythird_record"]["first_such_record"] == [2, 0, 1]


# --- helpers ------------------------------------------------------------------------------


def fake_grouped(members: Iterable[FState], r: int) -> Grouped:
    ms = tuple(members)
    mark = result_mark(ms[0])
    depth = {m: r for m in ms}
    return Grouped(Exploration(3, r, depth, [0] * (r + 1)), {mark: r}, {mark: ms})


# --- injections: each forces one disagreement and proves its branch fires ------------------


def test_round_not_cost(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "cost", lambda s: -1)
    check = FillingCheck()
    check_results(explore(3, 4), check, 3)
    assert check.round_not_cost


def test_record_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    arc = DState.of(3, [(0, 1)], [(1, 0)])
    raised = DState.of(3, [(0, 1), (0, 1), (0, 2)], [(1, 0), (1, 0), (2, 0)])
    g = fake_grouped([FState(arc, ((0, 1, 2),)), FState(raised, ((0, 1, 2),))], 6)
    clean = FillingCheck()
    check_results(g, clean, 3)
    assert not clean.record_mismatch
    calls = [0]

    def flaky(fs: FState, t: tuple[int, int, int]) -> bool:
        calls[0] += 1
        return calls[0] % 2 == 0

    monkeypatch.setattr(evidence, "balances", flaky)
    check = FillingCheck()
    check_results(g, check, 3)
    assert check.record_mismatch


def test_told_mismatch_both_ways(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "told", lambda fs: True)
    check = FillingCheck()
    check_results(explore(3, 4), check, 3)
    assert check.told_mismatch
    monkeypatch.setattr(evidence, "record_differs_from_nothing", lambda fs: True)
    check = FillingCheck()
    check_results(explore(3, 4), check, 3)
    assert check.told_mismatch


def test_blind_mismatch_both_ways(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "blind_by_description", lambda s: False)
    check = FillingCheck()
    check_results(explore(3, 4), check, 3)
    assert check.blind_mismatch
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "told", lambda fs: True)
    check = FillingCheck()
    check_results(explore(3, 4), check, 3)
    assert check.blind_mismatch


def test_keeping_mismatch_three_ways(monkeypatch: pytest.MonkeyPatch) -> None:
    g = explore(3, 5)
    with monkeypatch.context() as m:
        m.setattr(evidence, "keeping_sets_by_restriction", lambda s: ((9,),))
        check = FillingCheck()
        check_results(g, check, 3)
        assert any(x.startswith("least sets") for x in check.keeping_mismatch)
        check = FillingCheck()
        check_results(g, check, -1)
        assert not check.keeping_mismatch
    with monkeypatch.context() as m:
        m.setattr(evidence, "nothing_certificate", lambda s: None)
        check = FillingCheck()
        check_results(g, check, 3)
        assert any(x.startswith("none exactly") for x in check.keeping_mismatch)
    with monkeypatch.context() as m:
        m.setattr(evidence, "keeping_sets", lambda s: ())
        check = FillingCheck()
        check_results(g, check, 0)
        assert any(x.startswith("an unbalanced") for x in check.keeping_mismatch)


def test_exchange_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    def looped(fs: FState) -> FState:
        n = fs.n
        r = list(fs.state.r)
        if n:
            r[0] += 1
        return FState(DState(n, tuple(r), fs.state.s), fs.filled)

    monkeypatch.setattr(evidence, "swap25", looped)
    check = FillingCheck()
    check_results(explore(3, 4), check, 3)
    assert check.exchange_mismatch


def test_counts_and_two_terms(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "counts_within", lambda b, r: {})
    monkeypatch.setattr(evidence, "two_term_round_count", lambda r: -1)
    check = FillingCheck()
    check_counts(explore(3, 4), check)
    assert check.count_mismatch and check.two_term_mismatch


def test_plain_and_change_mismatches(monkeypatch: pytest.MonkeyPatch) -> None:
    g = explore(3, 4)
    with monkeypatch.context() as m:
        m.setattr(evidence, "psi", lambda fs: -1)
        check = FillingCheck()
        check_changes(g, check)
        assert check.plain_mismatch
    with monkeypatch.context() as m:
        m.setattr(evidence, "result_mark", lambda fs: result_mark(FState(DState(0, (), ()), ())))
        check = FillingCheck()
        check_changes(g, check)
        assert check.change_mismatch
    far = max(g.states.depth, key=lambda s: g.states.depth[s])

    def to_far(expl: Exploration) -> list[tuple[Any, Any, Any, Any]]:
        return [(fs, c, raw, far) for fs, c, raw, _ in real_performed(expl)]

    with monkeypatch.context() as m:
        m.setattr(evidence, "performed", to_far)
        check = FillingCheck()
        check_changes(g, check)
        assert any(x.startswith("from a state asserting the fewest") for x in check.change_mismatch)


def test_embed_mismatches(monkeypatch: pytest.MonkeyPatch) -> None:
    g = explore(3, 4)
    with monkeypatch.context() as m:
        m.setattr(evidence, "explore23", lambda b, r: real_explore23(b, max(r - 1, 0)))
        check = FillingCheck()
        check_embed(g, check)
        assert check.embed_mismatch
    with monkeypatch.context() as m:
        m.setattr(evidence, "compare_twentythird", lambda a, b: EmbedReport(1, 1, 0, 0, 0, 0))
        check = FillingCheck()
        check_embed(g, check)
        assert check.embed_mismatch == ["the map back does not return a mapped result"]
    with monkeypatch.context() as m:
        m.setattr(evidence, "seventh_pairs_merged", lambda: (False, True))
        check = FillingCheck()
        check_embed(g, check)
        assert check.embed_mismatch == ["an earlier pair kept apart"]


def test_read_back_mismatches(monkeypatch: pytest.MonkeyPatch) -> None:
    with monkeypatch.context() as m:
        m.setattr(evidence, "read_back", lambda fs: None)
        check = FillingCheck()
        check_read_back(explore(3, 4), check)
        assert check.read_back_mismatch
    with monkeypatch.context() as m:
        m.setattr(evidence, "smallest_none", lambda g: None)
        check = FillingCheck()
        block = check_read_back(explore(3, 4), check)
        assert check.read_back_mismatch and block["its_round"] is None
        check = FillingCheck()
        check_read_back(explore(2, 4), check)
        assert not check.read_back_mismatch


def test_reach_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "reachable", lambda s, t: True)
    check = FillingCheck()
    check_reach(explore(2, 3), check)
    assert check.reach_mismatch


def test_whether_mismatch_and_its_shapes(monkeypatch: pytest.MonkeyPatch) -> None:
    check = FillingCheck()
    block, _ = check_whether(explore(2, 2), check)
    assert block["first_such_record"] is None and not check.whether_mismatch
    monkeypatch.setattr(evidence, "record", lambda fs: (fs.n, 0, 0))
    check = FillingCheck()
    check_whether(explore(3, 5), check)
    assert check.whether_mismatch


def test_decide_mismatches(monkeypatch: pytest.MonkeyPatch) -> None:
    with monkeypatch.context() as m:
        m.setattr(evidence, "decides", lambda n, sub: True)
        check = FillingCheck()
        check_decide(TINY, check)
        assert check.decide_mismatch
    with monkeypatch.context() as m:
        m.setattr(evidence, "undecided_witness", lambda n, sub: (0,) * (n * n))
        check = FillingCheck()
        check_decide(TINY, check)
        assert check.decide_mismatch
    with monkeypatch.context() as m:
        m.setattr(evidence, "_balanced_small", lambda n, sub: True)
        check = FillingCheck()
        check_decide(TINY, check)
        assert any(x.startswith("search") for x in check.decide_mismatch)


def test_readings_mismatches(monkeypatch: pytest.MonkeyPatch) -> None:
    with monkeypatch.context() as m:
        m.setattr(evidence, "explore", lambda b, r: real_explore(b, max(r - 1, 0)))
        check = FillingCheck()
        check_readings(SMALL, check)
        assert "the chosen reading, computed twice" in check.readings_mismatch
    with monkeypatch.context() as m:
        m.setattr(evidence, "i3_reach_failures", lambda run: (1, 1))
        check = FillingCheck()
        check_readings(SMALL, check)
        assert any(x.startswith("C-I3") for x in check.readings_mismatch)
    with monkeypatch.context() as m:
        m.setattr(ReadingRun, "cost", lambda self, mark: -1)
        check = FillingCheck()
        check_readings(SMALL, check)
        assert any(x.endswith("round against cost") for x in check.readings_mismatch)

    def short_drop(reading: Any, b: int, r: int) -> ReadingRun:
        return real_reading(reading, b, r - 1 if reading.identify == "drop" else r)

    with monkeypatch.context() as m:
        m.setattr(evidence, "explore_reading", short_drop)
        check = FillingCheck()
        check_readings(SMALL, check)
        assert any(x.endswith("not the chosen results") for x in check.readings_mismatch)
    with monkeypatch.context() as m:
        m.setattr(evidence, "explore23", lambda b, r: real_explore23(b, max(r - 1, 0)))
        check = FillingCheck()
        check_readings(SMALL, check)
        assert any(x.endswith("not the twenty-third's results") for x in check.readings_mismatch)
    check = FillingCheck()
    block = check_readings(TINY, check)
    assert check.readings_mismatch == ["C-I3: identifying keeps the triples left without three different terms"]
    assert "state" not in block["C-I3_witness"]  # type: ignore[operator]


def test_marks_used_by_the_helpers() -> None:
    mark: Mark = result_mark(FState(DState(3, (0,) * 9, (0,) * 9), ((0, 1, 2),)))
    assert mark_text(mark).endswith("|012")
