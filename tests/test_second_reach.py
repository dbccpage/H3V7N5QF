from __future__ import annotations

import pytest

from second.explore import explore
from second.reach import carries, carrying_map, reachable, reachable_by_search
from xry.state import Sameness, State, canonical, given

ARB = given(False, Sameness.ANCHORED)
BOTH = given(True, Sameness.ANCHORED)


def test_carries() -> None:
    star = State.of(3, [(0, 1), (0, 2)], (0, 1))
    assert carries((0, 1), ARB, star)
    assert not carries((0,), ARB, star)  # wrong length
    assert not carries((0, 3), ARB, star)  # not a term
    assert not carries((0, 2), ARB, star)  # names not carried
    assert not carries((1, 0), ARB, star)  # arb not carried
    assert not carries((0, 1), ARB, State.of(3, [(0, 1), (0, 2)]))  # names on one side only
    assert carries((1, 0), given(False, Sameness.FREE), State.of(2, [(1, 0)]))


def test_carrying_map_needs_names_on_both_sides_or_neither() -> None:
    with pytest.raises(ValueError):
        carrying_map(given(False, Sameness.FREE), ARB)


def test_carrying_map_examples() -> None:
    assert carrying_map(ARB, State.of(3, [(0, 1)], (0, 1))) == (0, 1)
    assert carrying_map(ARB, BOTH) == (0, 1)
    assert carrying_map(BOTH, ARB) is None
    assert carrying_map(ARB, State.of(1, [], (0, 0))) is None
    assert carrying_map(State.of(1, [], (0, 0)), ARB) is None
    three = State.of(3, [(0, 1), (1, 2), (2, 0)], (0, 1))
    six = State.of(6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)], (0, 1))
    four = State.of(4, [(0, 1), (1, 2), (2, 3), (3, 0)], (0, 1))
    assert carrying_map(six, three) == (0, 1, 2, 0, 1, 2)
    assert carrying_map(three, six) is None
    assert carrying_map(four, three) is None and carrying_map(three, four) is None
    free = State.of(3, [(0, 1), (1, 2)])
    assert carrying_map(free, State.of(2, [(0, 1), (1, 0)])) == (0, 1, 0)
    assert carrying_map(free, State.of(2, [(0, 1)])) is None


def test_what_is_given_can_be_left_and_returned_to() -> None:
    star = State.of(3, [(0, 1), (0, 2)], (0, 1))
    assert reachable(ARB, star) and reachable(star, ARB)
    assert reachable(ARB, BOTH) and not reachable(BOTH, ARB)
    square = State.of(4, [(0, 1), (1, 0), (0, 3), (3, 0), (2, 1), (1, 2), (2, 3), (3, 2)], (0, 1))
    assert reachable(BOTH, square) and reachable(square, BOTH)


def test_search_stays_within_the_bound() -> None:
    assert reachable_by_search(ARB, 2) == {ARB, BOTH}
    assert reachable_by_search(BOTH, 2) == {BOTH}
    assert len(reachable_by_search(ARB, 3)) == 2 + 32


@pytest.mark.parametrize(("sameness", "bra"), [(Sameness.FREE, False), (Sameness.ANCHORED, True)])
def test_carrying_maps_agree_with_the_search(sameness: Sameness, bra: bool) -> None:
    bound = 3
    results = set(explore(given(bra, sameness), bound, rounds=30).depth)
    for s in results:
        found = reachable_by_search(s, bound)
        assert found <= results
        assert found == {t for t in results if reachable(s, t)}
        assert canonical(s) in found


def test_reachable_states_contain_what_is_given() -> None:
    for t in explore(ARB, 3, rounds=30).depth:
        q = carrying_map(ARB, t)
        assert q is not None and q[0] != q[1] and t.has(q[0], q[1])
