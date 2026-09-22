from __future__ import annotations

import pytest

from ninth.state import DState, empty
from eleventh.writing import (
    bell,
    coarser_than,
    determines,
    determines_rel,
    injective,
    read_from,
    terms_after_writing,
    writings,
)


def test_writings_and_bell() -> None:
    assert writings(0) == ((),)
    assert writings(1) == ((0,),)
    assert writings(2) == ((0, 0), (0, 1))
    assert bell(0) == 1 and bell(1) == 1 and bell(2) == 2 and bell(3) == 5
    assert injective((0, 1)) and not injective((0, 0))
    with pytest.raises(ValueError, match="not negative"):
        writings(-1)


def test_empty_and_injective_determine() -> None:
    assert determines(empty(), ())
    one = DState.of(1, [], [])
    assert determines(one, (0,)) and read_from(one, (0,)) is not None
    two = DState.of(2, [], [])
    assert determines(two, (0, 1)) and determines(two, (0, 0))
    between = DState.of(2, [(0, 1)], [])
    assert determines(between, (0, 1))
    assert not determines(between, (0, 0))
    assert not determines_rel(between, (0, 0), "r")
    assert determines_rel(between, (0, 0), "s")
    assert read_from(between, (0, 0)) is None
    read = read_from(between, (0, 1))
    assert read is not None and read["r"][(0, 1)] == 1


def test_coarser_and_collision_forbids() -> None:
    three = DState.of(3, [(0, 1)], [])
    partial = (0, 0, 1)
    collapsed = (0, 0, 0)
    apart = (0, 1, 2)
    assert coarser_than(partial, collapsed) and coarser_than(apart, partial)
    assert not coarser_than(collapsed, apart)
    assert not determines(three, partial) and not determines(three, collapsed)
    assert determines(three, apart)
    with pytest.raises(ValueError, match="same length"):
        coarser_than((0, 1), (0,))


def test_terms_after_writing_is_not_identifying() -> None:
    between = DState.of(2, [(0, 1)], [])
    assert terms_after_writing(between, (0, 0)) == 2
    with pytest.raises(ValueError, match="every term"):
        terms_after_writing(between, (0,))
    with pytest.raises(ValueError, match="every term"):
        determines_rel(between, (0,), "r")
    with pytest.raises(ValueError, match="r or with s"):
        determines_rel(between, (0, 1), "t")
