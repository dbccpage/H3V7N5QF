from __future__ import annotations

import pytest

from second.changes import changes, obstruction, perform
from second.explore import explore
from second.invariants import fewest_classes
from xry.state import Sameness, State, canonical, given


def test_fewest_classes() -> None:
    assert fewest_classes(State(0, 0)) == 0
    assert fewest_classes(State.of(1, [])) == 1
    assert fewest_classes(State.of(3, [])) == 1
    assert fewest_classes(State.of(2, [(0, 1)])) == 2
    assert fewest_classes(State.of(2, [(0, 1), (1, 0)])) == 2
    assert fewest_classes(State.of(3, [(0, 1), (1, 2)])) == 2
    assert fewest_classes(State.of(3, [(0, 1), (1, 2), (2, 0)])) == 3
    assert fewest_classes(State.of(4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])) == 4
    assert fewest_classes(State.of(4, [(0, 1), (1, 2), (2, 3), (3, 0)])) == 2
    with pytest.raises(ValueError):
        fewest_classes(State.of(1, [(0, 0)]))


def test_never_decreases_along_a_change_and_can_rise() -> None:
    expl = explore(given(False, Sameness.FREE), 3, rounds=30)
    rose = 0
    for state in expl.depth:
        before = fewest_classes(state)
        for change in changes(state):
            if obstruction(state, change):
                continue
            out = perform(state, change)
            if out.n > 3:
                continue
            after = fewest_classes(canonical(out))
            assert after >= before
            rose += after > before
    assert rose > 0
