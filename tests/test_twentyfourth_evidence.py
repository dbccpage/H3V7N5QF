"""The evidence writer, and an injection test for every disagreement branch of every check."""

from __future__ import annotations

import json
from collections.abc import Iterator
from pathlib import Path
from typing import Any

import pytest

from twentyfourth import embed, evidence, readings
from twentyfourth.changes import ID_BOTH, Reading
from twentyfourth.embed import Comparison
from twentyfourth.evidence import (
    FillCheck,
    Plan,
    align,
    audit,
    check_changes,
    check_forget,
    check_reach,
    check_read_back,
    check_readings,
    check_record_question,
    check_respect,
    check_results,
    check_sameness,
    check_sequences,
    class_from_key,
    compare_twentythird,
    key_text,
    run_tag,
    write_all,
    write_counts,
)
from twentyfourth.explore import Grouped, explore
from twentyfourth.state import DState, FState, result_key
from twentythird.state import excess_table

SMALL = Plan(
    bound=2,
    rounds=4,
    deep_bound=3,
    deep_rounds=4,
    two_term_rounds=5,
    log_bound=2,
    log_rounds=2,
    reach_bound=2,
    reach_rounds=3,
    same_small=1,
    same_large=3,
    readings_bound=2,
    readings_rounds=3,
    layers_upto=4,
    closed_form_upto=6,
    points_upto=3,
)


def small() -> Grouped:
    return explore(2, 4)


def test_plan_tag_key_text() -> None:
    assert Plan().runs() == ((5, 7), (3, 9), (2, 16))
    with pytest.raises(ValueError, match="three times"):
        Plan(same_small=2, same_large=5)
    with pytest.raises(ValueError, match="two terms and three rounds"):
        Plan(reach_rounds=2)
    with pytest.raises(ValueError, match="two terms and three rounds"):
        Plan(reach_bound=1)
    assert run_tag(3, 4) == "bound3_rounds4"
    assert key_text((2, (0, 1, -1, 0), (1, 0))) == "2:0,1,-1,0:10"


def test_audit_is_clean() -> None:
    check = audit(2, 4)
    assert check.clean()
    assert set(check.as_dict()) == set(FillCheck.__dataclass_fields__)


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    assert summary["every_check_clean"] is True
    names = {p.name for p in tmp_path.iterdir()}
    assert {"given.json", "summary.json", "counts.csv", "readings.json", "MANIFEST.sha256"} <= names
    assert {"results_bound2_rounds4.csv", "reach_bound2_rounds3.csv", "attempts_bound2_rounds2.jsonl"} <= names
    given = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given["identifying_two_filled_terms"]["cost_from"] == 4
    assert given["identifying_two_filled_terms"]["cost_to"] == 2
    assert given["identifying_turns_a_two_term_witness_into_a_loop"]["class_to"] == "told"
    assert given["smallest_result_answered_none"]["cost"] == 2
    assert set(given["first_result_of_each_class"]) == {"nothing", "told", "one filling away", "two terms", "three terms"}
    kept = [w["kept_by"] for w in given["the_twentythird_record_question"]["witnesses"]]
    assert kept == [[1, 2], [1, 3]]


def test_align() -> None:
    a = FState(DState.of(2, [(0, 1)], [(1, 0)]), (1, 0))
    b = FState(DState.of(2, []), (0, 1))
    assert result_key(align(a, b)) == result_key(b) and align(a, b).fills == b.fills
    with pytest.raises(ValueError):
        align(a, FState(DState.of(2, [(0, 0)]), (0, 1)))


def test_class_from_key() -> None:
    assert class_from_key((1, (1,), (1,))) == "told"
    assert class_from_key((1, (1,), (0,))) == "one filling away"
    assert class_from_key((2, (0, 1, 0, 0), (0, 0))) == "two terms"
    assert class_from_key((3, (0, 1, 0, -1, 0, 0, 0, 0, 0), (0, 0, 0))) == "three terms"
    assert class_from_key((2, (0, 0, 0, 0), (1, 1))) == "nothing"


# --- injections: each forces one disagreement and proves its branch fires ------------------


def test_round_balance_tell_record_exchange(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    monkeypatch.setattr(evidence, "cost", lambda s: -1)
    monkeypatch.setattr(evidence, "potential", lambda s: -1)
    monkeypatch.setattr(evidence, "balance_record", lambda s: (9, 9))
    monkeypatch.setattr(evidence, "tell_class", lambda s: "none of them")
    monkeypatch.setattr(evidence, "record23", lambda s: (7, 7, 7))
    check = FillCheck()
    check_results(g, check)
    assert check.round_not_cost and check.balance_mismatch and check.tell_mismatch and check.record_mismatch
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "swap", lambda s: s)
    check = FillCheck()
    check_results(g, check)
    assert check.exchange_mismatch and not check.round_not_cost


def test_counts_and_two_term(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "counts_within", lambda b, r: {"9/9/9": 1})
    monkeypatch.setattr(evidence, "two_term_round_count", lambda r: -1)
    check = FillCheck()
    check_results(small(), check)
    assert check.count_mismatch and check.two_term_mismatch
    check = FillCheck()
    check_results(explore(1, 3), check)  # one term: no two-term rounds to compare
    assert check.count_mismatch and not check.two_term_mismatch


def test_write_counts_injection(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    check = FillCheck()
    write_counts(tmp_path, SMALL, check)
    assert not check.two_term_mismatch
    monkeypatch.setattr(evidence, "two_term_count", lambda k, t: -1)
    write_counts(tmp_path, SMALL, check)
    assert check.two_term_mismatch


def test_sequences(monkeypatch: pytest.MonkeyPatch) -> None:
    check = FillCheck()
    check_sequences(small(), check)
    assert not check.sequences_mismatch
    monkeypatch.setattr(evidence, "one_term_sequences", lambda k, t: -1)
    check_sequences(small(), check)
    assert check.sequences_mismatch


def test_changes(monkeypatch: pytest.MonkeyPatch) -> None:
    from twentyfourth.explore import performed as real

    g = small()

    def start(expl: Any) -> Iterator[tuple[FState, Any, FState, FState]]:
        for s, c, _, out in real(expl):
            yield s, c, s, out

    monkeypatch.setattr(evidence, "performed", start)
    check = FillCheck()
    check_changes(g, check)
    assert any("returns to its own result" in x for x in check.change_mismatch)
    assert any("parity" in x for x in check.change_mismatch)
    assert any("filling" in x for x in check.change_mismatch)

    def jump(expl: Any) -> Iterator[tuple[FState, Any, FState, FState]]:
        for s, c, raw, out in real(expl):
            big = FState(DState(raw.n, raw.base.r, tuple(k + 3 for k in raw.base.s)), raw.fills)
            yield s, c, big, out

    monkeypatch.setattr(evidence, "performed", jump)
    check = FillCheck()
    check_changes(g, check)
    assert any("from a state asserting the fewest" in x for x in check.change_mismatch)


def test_respect(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    check = FillCheck()
    assert check_respect(g, check)["outcomes_compared"] != 0 and not check.respect_mismatch
    assert check_respect(g, FillCheck(), most_terms=0)["outcomes_compared"] == 0
    monkeypatch.setattr(evidence, "outcome_key", lambda s, c: (s.n, excess_table(s.base), s.fills))
    check_respect(g, check)
    assert check.respect_mismatch


def test_twentythird(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    real = embed.compare_with_twentythird(g)
    k = (9, (), ())
    fake = Comparison(real.twentythird, (k,), (k,), (k,), (k,), 1, 1)
    monkeypatch.setattr(evidence, "compare_with_twentythird", lambda grouped: fake)
    check = FillCheck()
    compare_twentythird(g, check)
    assert len(check.twentythird_mismatch) == 4


def test_read_back(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    check = FillCheck()
    check_read_back(explore(2, 1), check)
    assert not check.read_back_mismatch
    monkeypatch.setattr(evidence, "read_back", lambda k: None)
    check_read_back(g, check)
    assert check.read_back_mismatch
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "read_back", lambda k: (k[0], (5,) * (k[0] * k[0])))
    check = FillCheck()
    check_read_back(g, check)
    assert check.read_back_mismatch


def test_forget(monkeypatch: pytest.MonkeyPatch) -> None:
    from twentyfourth.explore import performed as real

    g = small()
    monkeypatch.setattr(evidence, "forget_key", lambda k: (0, ()))
    check = FillCheck()
    check_forget(g, check)
    assert check.forget_mismatch
    monkeypatch.undo()

    def moved(expl: Any) -> Iterator[tuple[FState, Any, FState, FState]]:
        for s, c, raw, out in real(expl):
            yield s, c, FState(DState(raw.n, tuple(k + 5 for k in raw.base.r), raw.base.s), raw.fills), out

    monkeypatch.setattr(evidence, "performed", moved)
    check = FillCheck()
    check_forget(g, check)
    assert any("fill" in x for x in check.forget_mismatch)
    assert any("add" in x for x in check.forget_mismatch)


def test_reach(monkeypatch: pytest.MonkeyPatch) -> None:
    g = explore(2, 3)
    check = FillCheck()
    summary, rows = check_reach(g, check)
    assert not check.reach_mismatch and rows and summary["ordered_pairs_reachable"] != summary["ordered_pairs"]
    monkeypatch.setattr(evidence, "reachable", lambda s, t, r: True)
    check_reach(g, check)
    assert check.reach_mismatch


def test_sameness(monkeypatch: pytest.MonkeyPatch) -> None:
    check = FillCheck()
    check_sameness(1, 3, check)
    assert not check.sameness_mismatch
    monkeypatch.setattr(readings, "fill_steps", lambda s: iter(()))
    check_sameness(1, 3, check)
    assert any("the same but not joined" in x for x in check.sameness_mismatch)
    monkeypatch.undo()

    def joined(n: int, small_: int, large: int) -> dict[FState, FState]:
        states = readings.box_fstates(n, small_)
        return {s: states[0] for s in states}

    monkeypatch.setattr(evidence, "generated_classes", joined)
    check = FillCheck()
    check_sameness(1, 1, check)
    assert any("joined but not the same" in x for x in check.sameness_mismatch)


def test_readings(monkeypatch: pytest.MonkeyPatch) -> None:
    chosen = explore(2, 3)
    check = FillCheck()
    out = check_readings(2, 3, check, chosen)
    assert not check.readings_mismatch and out["C-F2_results"] != out["C-F1_C-I1_results"]
    monkeypatch.setattr(evidence, "cost_counted", lambda s: -1)
    check_readings(2, 3, check, chosen)
    assert any("C-F2" in x for x in check.readings_mismatch)
    check = FillCheck()
    monkeypatch.undo()
    check_readings(2, 3, check, explore(2, 2))
    assert any("C-F3" in x for x in check.readings_mismatch)


def test_record_question(monkeypatch: pytest.MonkeyPatch) -> None:
    g = explore(2, 3)
    check = FillCheck()
    check_record_question(g, check)
    assert not check.record_question_mismatch
    monkeypatch.setattr(evidence, "keeping_size", lambda b: 0)
    check_record_question(g, check)
    assert len(check.record_question_mismatch) == 2
    monkeypatch.undo()

    class Shown:
        records = 0
        records_with_several_sizes = 0
        records_with_several_term_counts = 0
        first = None
        whether_shown = False

    monkeypatch.setattr(evidence, "record_question", lambda theirs: Shown())
    check = FillCheck()
    out = check_record_question(g, check)
    assert check.record_question_mismatch == ["the record's assertions are zero on a result other than nothing"]
    assert out["first_such_record"] is None


def test_identification_readings_in_changes() -> None:
    g = explore(2, 4, Reading(identify=ID_BOTH))
    check = FillCheck()
    check_changes(g, check)
    # under C-I2 identifying a filled term with an unfilled one also moves the cost by an even number
    assert any("parity" in x for x in check.change_mismatch)
