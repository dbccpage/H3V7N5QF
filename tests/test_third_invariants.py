from __future__ import annotations

from third.changes import changes, obstruction, perform
from third.explore import explore
from third.invariants import fewest_classes, never_decreases
from xry.state import Sameness, State, canonical, given


def test_never_decreases() -> None:
    s = State.of(2, [(0, 1)])
    assert never_decreases(s, State.of(3, [(0, 1)]))
    assert never_decreases(s, State.of(2, [(0, 1), (1, 0)]))
    assert not never_decreases(s, s)  # size did not rise
    assert not never_decreases(s, State.of(1, [], None))  # a term gone
    assert not never_decreases(State.of(3, [(0, 1), (0, 2)]), State.of(4, [(0, 1)]))  # an assertion gone
    assert not never_decreases(s, State.of(4, [(0, 1)]))  # rose by two


def test_fewest_classes_is_the_second_derivations() -> None:
    assert fewest_classes(State.of(2, [(0, 1)])) == 2
    assert fewest_classes(State.of(3, [(0, 1), (1, 2), (2, 0)])) == 3


def test_nothing_decreases_along_a_change_and_classes_can_rise() -> None:
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
            assert never_decreases(state, out)
            after = fewest_classes(canonical(out))
            assert after >= before
            rose += after > before
    assert rose > 0
