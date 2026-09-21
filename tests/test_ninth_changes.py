from __future__ import annotations

from itertools import product
from math import comb

import pytest

from eighth.changes import changes as changes_eighth
from eighth.changes import perform as perform_eighth
from ninth.changes import (
    KINDS,
    Change,
    Kind,
    attempt_counts,
    changes,
    first_changes,
    is_addition,
    is_change,
    makes_some_loop,
    perform,
)
from ninth.state import DState, empty


def test_the_changes_are_the_eighths_and_the_first_change_adds_a_term() -> None:
    assert changes is changes_eighth and perform is perform_eighth and len(KINDS) == 4
    first = first_changes()
    assert first == (Change(Kind.ADD_TERM),) and is_addition(first[0]) and is_change(first[0])
    assert perform(empty(), first[0]) == DState.of(1, [], [])
    assert attempt_counts(empty()) == (1, 1, 0, 0)
    one = DState.of(1, [], [])
    assert [c.written(one) for c in changes(one)] == ["add a term", "add ara", "add asa"]
    assert not is_addition(Change(Kind.REMOVE, "r", 0, 0)) and not is_addition(Change(Kind.IDENTIFY, "", 0, 1))
    assert Change(Kind.ADD_TERM).additions == (1, 0) and Change(Kind.ADD_ASSERTION, "s", 0, 0).additions == (0, 1)


@pytest.mark.parametrize("n", [0, 1, 2])
def test_attempt_counts_agree_with_the_list(n: int) -> None:
    for r in product(range(2), repeat=n * n):
        for s in product(range(2), repeat=n * n):
            state = DState(n, r, s)
            listed = changes(state)
            total, additions, xrx, xsx = attempt_counts(state)
            assert len(listed) == comb(n, 2) + state.distinct + 1 + 2 * n * n == total
            assert sum(1 for c in listed if is_addition(c)) == 1 + 2 * n * n == additions
            assert sum(1 for c in listed if makes_some_loop(state, c, "r")) == xrx
            assert sum(1 for c in listed if makes_some_loop(state, c, "s")) == xsx
            assert all(is_change(c) for c in listed)
            for c in listed:
                out = perform(state, c)
                assert out.n >= 1
                assert abs(out.size - state.size) == 1
                assert is_addition(c) == (out.size == state.size + 1)


def test_loops_and_identifications_act_on_both_relations() -> None:
    s = DState.of(2, [(0, 1)], [(1, 0)])
    assert makes_some_loop(s, Change(Kind.ADD_ASSERTION, "r", 0, 0), "r")
    assert makes_some_loop(s, Change(Kind.IDENTIFY, "", 0, 1), "r")
    assert makes_some_loop(s, Change(Kind.IDENTIFY, "", 0, 1), "s")
    assert not makes_some_loop(s, Change(Kind.ADD_ASSERTION, "s", 0, 1), "s")
    assert not makes_some_loop(DState.of(1, [(0, 0)], []), Change(Kind.ADD_ASSERTION, "r", 0, 0), "r")
    merged = perform(s, Change(Kind.IDENTIFY, "", 0, 1))
    assert merged == DState.of(1, [(0, 0)], [(0, 0)])
