from __future__ import annotations

import pytest

from fourteenth.leftover import leftover_nothing
from ninth.explore import explore as explore_ninth
from ninth.state import empty
from sixteenth.changes import Change16, Kind
from sixteenth.explore import (
    Exit16,
    attempt16,
    count_shortest_sequences16,
    cycle16,
    explore16,
    order16,
    performed16,
    returns_in_two,
    sequences_exact16,
)
from sixteenth.state import RState, Reading, canonical16, empty16


def test_explore_small() -> None:
    expl = explore16(empty16(), 2, 6)
    assert len(expl.depth) == 386 and expl.new_per_round == [1, 1, 3, 8, 28, 85, 260]
    assert expl.last_new_round == 6 and expl.start == empty16() and expl.reading is Reading.COUNT
    assert expl.attempts_per_round[0] == 0 and expl.attempts_per_round[-1] > 0
    assert expl.admissions_per_round[-1] > 0 and expl.admissions_per_round[3] == 0
    assert expl.awaiting and all(expl.depth[s] == 6 for s in expl.awaiting)
    assert all(isinstance(e, Exit16) and e.change == Change16(Kind.ADD_TERM) for e in expl.frontier)
    assert {s.state for s in expl.depth if s.record_empty} == set(explore_ninth(empty(), 2, 6).depth)
    assert all(r == s.potential for s, r in expl.depth.items())
    with pytest.raises(ValueError, match="below the start"):
        explore16(RState.of(3, []), 2, 1)
    with pytest.raises(ValueError, match="at least one term"):
        explore16(empty16(), 0, 1)
    with pytest.raises(ValueError, match="not negative"):
        explore16(empty16(), 2, -1)


def test_log_and_attempts() -> None:
    expl = explore16(empty16(), 2, 3, keep_log=True)
    assert expl.log and expl.log[0].leftover == leftover_nothing() and expl.log[0].change == Change16(Kind.ADD_TERM)
    kinds = {rec.leftover.kind for rec in expl.log}
    assert kinds == {"nothing", "pair", "merge"}
    beyond = attempt16(RState.of(2, []), Change16(Kind.ADD_TERM), 2)
    assert beyond.beyond and beyond.outcome is None
    inside = attempt16(RState.of(1, [(0, 0)]), Change16(Kind.REMOVE, "r", 0, 0), 2)
    assert inside.outcome == canonical16(RState.of(1, [], [], [(0, 0)])) and inside.leftover.kind == "pair"


def test_performed_and_sequences() -> None:
    expl = explore16(empty16(), 2, 5)
    steps = list(performed16(expl))
    assert steps[0][0] == empty16() and steps[0][1] == Change16(Kind.ADD_TERM)
    assert all(expl.depth[s] < 5 for s, _c, _raw, _out in steps)
    assert all(canonical16(raw) == out for _s, _c, raw, out in steps)
    sequences = count_shortest_sequences16(expl)
    assert sequences[empty16()] == 1 and sequences[RState.of(1, [])] == 1
    assert sequences[canonical16(RState.of(1, [], [], [(0, 0)]))] == 2  # add ara or asa, then remove it
    assert all(sequences_exact16(expl, s) for s in expl.depth)
    assert all(c >= 1 for c in sequences.values())


def test_sequences_refuse_a_broken_exploration(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore16(empty16(), 2, 3)
    one = RState.of(1, [])
    expl.depth[one] = 5
    with pytest.raises(ValueError, match="more than one"):
        count_shortest_sequences16(expl)
    expl = explore16(empty16(), 2, 3)
    # a change that raises the round while the rule says it does not raise the potential is refused
    monkeypatch.setattr("sixteenth.explore.raises_potential", lambda c: False)
    with pytest.raises(ValueError, match="does not raise the potential"):
        count_shortest_sequences16(expl)


def test_cycles() -> None:
    assert cycle16(empty16()) is None and not returns_in_two(empty16())
    one = RState.of(1, [])
    found = cycle16(one)
    assert found is not None and found[0] == Change16(Kind.ADD_TERM) and found[1].kind is Kind.IDENTIFY
    ara = RState.of(1, [(0, 0)])
    found = cycle16(ara)
    assert found is not None and found[0] == Change16(Kind.REMOVE, "r", 0, 0) and found[1].admits
    asa = RState.of(1, [], [(0, 0)])
    found = cycle16(asa)
    assert found is not None and found[0].rel == "s" and found[1].rel == "s"
    assert returns_in_two(one) and returns_in_two(ara) and returns_in_two(asa)
    assert returns_in_two(RState.of(2, [(0, 1)], [(1, 1)], [(0, 0)]))
    assert order16(one) == (1, (0,), (0,), (0,))


def test_unchosen_readings_explore() -> None:
    as_set = explore16(empty16(), 2, 5, reading=Reading.SET)
    drop = explore16(empty16(), 2, 5, reading=Reading.DROP)
    chosen = explore16(empty16(), 2, 5)
    assert len(as_set.depth) < len(chosen.depth) == len(drop.depth)
    assert as_set.reading is Reading.SET and drop.reading is Reading.DROP
