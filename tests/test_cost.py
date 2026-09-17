from __future__ import annotations

import pytest

from xry.cost import (
    cost,
    cost_anchored,
    cost_free,
    cost_free_by_placement,
    destroyed,
    given_size,
    has_two_way,
)
from xry.state import Sameness, State, given


def test_what_is_given_costs_nothing() -> None:
    for sameness in Sameness:
        for bra in (False, True):
            assert cost(given(bra, sameness), bra) == 0
    assert given_size(False) == 3 and given_size(True) == 4


def test_destroyed_givens() -> None:
    with pytest.raises(ValueError):
        destroyed(State.of(2, [(0, 1)]), False)
    arb = State.of(2, [(0, 1)], (0, 1))
    bra = State.of(2, [(1, 0)], (0, 1))
    none = State.of(2, [], (0, 1))
    both = State.of(2, [(0, 1), (1, 0)], (0, 1))
    one = State.of(1, [], (0, 0))
    assert [destroyed(s, False) for s in (arb, bra, none, both, one)] == [0, 1, 1, 0, 2]
    assert [destroyed(s, True) for s in (arb, bra, none, both, one)] == [1, 1, 2, 0, 3]


def test_each_destroyed_given_costs_two() -> None:
    assert cost_anchored(State.of(2, [], (0, 1)), False) == 1
    assert cost_anchored(State.of(2, [(1, 0)], (0, 1)), False) == 2
    assert cost_anchored(State.of(1, [], (0, 0)), False) == 2
    assert cost_anchored(State.of(1, [], (0, 0)), True) == 3
    assert cost_anchored(State.of(2, [], (0, 1)), True) == 2
    assert cost_anchored(State.of(3, [(0, 1), (1, 2)], (0, 1)), False) == 2


def test_free_cost_is_the_best_placement_of_the_names() -> None:
    for n in (1, 2, 3):
        for mask in range(1 << (n * n)):
            state = State(n, mask)
            if not state.legal:
                continue
            for bra in (False, True):
                assert cost_free(state, bra) == cost_free_by_placement(state, bra)
                assert cost(state, bra) == cost_free(state, bra)


def test_free_cost_cases() -> None:
    assert cost_free(State.of(1, []), False) == 2 and cost_free(State.of(1, []), True) == 3
    assert cost_free(State.of(3, []), False) == 2 and cost_free(State.of(3, []), True) == 3
    path = State.of(3, [(0, 1), (1, 2)])
    assert cost_free(path, False) == 2 and cost_free(path, True) == 3
    assert has_two_way(State.of(2, [(0, 1), (1, 0)])) and not has_two_way(path)
    with pytest.raises(ValueError):
        cost_free(State(0, 0), False)
    with pytest.raises(ValueError):
        cost_free_by_placement(State(0, 0), False)
