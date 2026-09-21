from __future__ import annotations

import pytest

from ninth.changes import Change, Kind, perform
from ninth.state import DState, empty, same, swap
from thirteenth.coarse import (
    add_r_or_s_same_coarser,
    coarse,
    coarse_key,
    determines,
    same_coarser,
    splits,
    swap_keeps_coarse,
)


def test_empty_determines_and_between_does_not() -> None:
    two = DState.of(2, [], [])
    between = DState.of(2, [(0, 1)], [])
    swapped = swap(between)
    assert determines(empty()) and determines(two)
    assert splits(empty()) == 1 and splits(two) == 1
    assert not determines(between)
    assert splits(between) == 2
    assert same_coarser(between, swapped)
    assert not same(between, swapped)
    assert coarse(between) == coarse(swapped)
    assert coarse(between).size == between.size
    assert swap_keeps_coarse(between)
    assert add_r_or_s_same_coarser(two, 0, 1)
    added_r = perform(two, Change(Kind.ADD_ASSERTION, "r", 0, 1))
    added_s = perform(two, Change(Kind.ADD_ASSERTION, "s", 0, 1))
    assert same_coarser(added_r, added_s) and not same(added_r, added_s)
    assert coarse_key(between) == coarse_key(swapped)


def test_both_relations_and_errors() -> None:
    both = DState.of(2, [(0, 1)], [(0, 1)])
    assert splits(both) == 3
    assert determines(both) is False
    assert swap_keeps_coarse(both)
    assert coarse(both).mult[1] == 2
    one = DState.of(1, [(0, 0)], [])
    other = DState.of(1, [], [(0, 0)])
    assert same_coarser(one, other) and one != other
    assert splits(one) == 2
    three = DState.of(3, [(0, 1)], [(1, 2)])
    assert same_coarser(three, swap(three))
    assert not determines(three)
    with pytest.raises(TypeError, match="two-relation"):
        from thirteenth.changes import coarse_of_outcome

        coarse_of_outcome("no", Change(Kind.ADD_TERM))
