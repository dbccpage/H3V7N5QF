from __future__ import annotations

import pytest

from second.cost import (
    contains_given,
    cost,
    cost_anchored,
    cost_free,
    cost_free_by_placement,
    given_size,
)
from xry.state import Sameness, State, given


def test_what_is_given_costs_nothing() -> None:
    for sameness in Sameness:
        for bra in (False, True):
            assert cost(given(bra, sameness), bra) == 0
    assert given_size(False) == 3 and given_size(True) == 4


def test_contains_given() -> None:
    with pytest.raises(ValueError):
        contains_given(State.of(2, [(0, 1)]), False)
    arb = State.of(2, [(0, 1)], (0, 1))
    bra = State.of(2, [(1, 0)], (0, 1))
    none = State.of(2, [], (0, 1))
    both = State.of(2, [(0, 1), (1, 0)], (0, 1))
    one = State.of(1, [], (0, 0))
    assert [contains_given(s, False) for s in (arb, bra, none, both, one)] == [
        True, False, False, True, False,
    ]  # fmt: skip
    assert [contains_given(s, True) for s in (arb, bra, none, both, one)] == [
        False, False, False, True, False,
    ]  # fmt: skip


def test_cost_is_the_size_difference_or_unreachable() -> None:
    star = State.of(3, [(0, 1), (0, 2)], (0, 1))
    assert cost_anchored(star, False) == 2 and cost_anchored(star, True) is None
    both = State.of(2, [(0, 1), (1, 0)], (0, 1))
    assert cost_anchored(both, False) == 1 and cost_anchored(both, True) == 0
    assert cost_anchored(State.of(1, [], (0, 0)), False) is None
    assert cost_anchored(State.of(2, [(1, 0)], (0, 1)), False) is None
    assert cost_anchored(State.of(4, [(0, 1)], (0, 1)), False) == 2


def test_free_cost_cases() -> None:
    assert cost_free(State.of(1, []), False) is None
    assert cost_free(State.of(3, []), False) is None
    path = State.of(3, [(0, 1), (1, 2)])
    assert cost_free(path, False) == 2 and cost_free(path, True) is None
    both = State.of(2, [(0, 1), (1, 0)])
    assert cost_free(both, False) == 1 and cost_free(both, True) == 0
    assert cost_free_by_placement(State.of(2, []), False) is None


def test_free_cost_is_the_best_placement_of_the_names() -> None:
    for n in (1, 2, 3):
        for mask in range(1 << (n * n)):
            state = State(n, mask)
            if not state.legal:
                continue
            for bra in (False, True):
                assert cost_free(state, bra) == cost_free_by_placement(state, bra)
                assert cost(state, bra) == cost_free(state, bra)
