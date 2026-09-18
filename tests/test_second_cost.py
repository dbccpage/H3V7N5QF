from __future__ import annotations

import pytest

from second.cost import (
    contains_given,
    cost,
    cost_anchored,
    cost_free,
    cost_free_by_placement,
    given_size,
    has_two_way,
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


def test_illegal_states_are_unreachable() -> None:
    """A state asserting some `xrx` is never a result, so every cost is `None`.

    Without the legality guard the reachability tests ("contains what is given"
    / "has an assertion") admit self-loops and give a finite, even negative,
    size difference; the two FREE formulas then need not agree either.
    """
    loop = State(1, 1)  # `ara` only: a self-loop, illegal
    assert not loop.legal
    assert cost_free(loop, False) is None and cost_free(loop, True) is None
    assert cost_free_by_placement(loop, False) is None
    assert cost(loop, False) is None
    mixed = State(2, 3)  # `arb` and the self-loop `ara`: illegal, yet contains `arb`
    assert not mixed.legal
    for bra in (False, True):
        assert cost_free(mixed, bra) is None
        assert cost_free(mixed, bra) == cost_free_by_placement(mixed, bra)
    named = State(2, 3, (0, 1))  # the same with names: illegal, so `None`, not 1
    assert cost_anchored(named, False) is None and cost(named, False) is None


def _is_result(state: State, bra: bool) -> bool:
    """Whether `state` is reachable from what is given, stated independently of
    the cost functions: a result is legal and, with names, contains what is
    given; without names, asserts something (with `bra`, a pair both ways)."""
    if not state.legal:
        return False
    if state.names is not None:
        return contains_given(state, bra)
    return has_two_way(state) if bra else state.m > 0


def test_cost_is_none_exactly_off_the_result_set() -> None:
    """Property: over every state -- legal and illegal, both name readings, up
    to a small bound -- `cost` is `None` exactly when the state is not a result,
    and otherwise the non-negative size difference. This exercises the illegal
    states that `check_free_cost` skips, so the legality guard cannot silently
    regress."""
    checked = illegal = 0
    for bra in (False, True):
        for n in range(1, 4):
            for mask in range(1 << (n * n)):
                for names in (None, (0, 0), (0, 1 % n)):
                    state = State(n, mask, names)
                    illegal += not state.legal
                    got = cost(state, bra)
                    if _is_result(state, bra):
                        assert got == state.n + state.m - given_size(bra)
                        assert got is not None and got >= 0
                    else:
                        assert got is None
                    checked += 1
    assert checked > 0 and illegal > 0
