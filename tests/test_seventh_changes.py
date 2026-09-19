from __future__ import annotations

from itertools import product
from math import comb

import pytest

from fifth.changes import changes as changes_fifth
from fifth.changes import perform as perform_fifth
from seventh.changes import (
    KINDS,
    Change,
    Kind,
    attempt_counts,
    changes,
    first_changes,
    is_addition,
    is_change,
    makes_some_xrx,
    perform,
    related_pairs,
)
from seventh.state import MState, empty


def test_the_changes_are_the_fifths_and_the_first_change_adds_a_term() -> None:
    assert changes is changes_fifth and perform is perform_fifth and len(KINDS) == 4
    first = first_changes()
    assert first == (Change(Kind.ADD_TERM),) and is_addition(first[0]) and is_change(first[0])
    assert perform(empty(), first[0]) == MState.of(1, [])
    assert attempt_counts(empty()) == (1, 1)
    assert [c.written(MState.of(1, [])) for c in changes(MState.of(1, []))] == ["add a term", "add ara"]
    assert not is_addition(Change(Kind.REMOVE, 0, 0)) and not is_addition(Change(Kind.IDENTIFY, 0, 1))


@pytest.mark.parametrize("n", [0, 1, 2, 3])
def test_attempt_counts_agree_with_the_list(n: int) -> None:
    for mult in product(range(2), repeat=n * n):
        state = MState(n, mult)
        listed = changes(state)
        assert len(listed) == comb(n, 2) + state.distinct + 1 + n * n == attempt_counts(state)[0]
        assert sum(1 for c in listed if is_addition(c)) == 1 + n * n == attempt_counts(state)[1]
        assert all(is_change(c) for c in listed)
        for c in listed:
            out = perform(state, c)
            assert out.n >= 1  # every change on any state leaves a state with a term
            assert abs(out.size - state.size) == 1
            assert is_addition(c) == (out.size == state.size + 1)


def test_makes_some_xrx_and_related_pairs_survive_without_names() -> None:
    s = MState.of(2, [(0, 1)])
    assert makes_some_xrx(s, Change(Kind.ADD_ASSERTION, 0, 0)) and makes_some_xrx(s, Change(Kind.IDENTIFY, 0, 1))
    assert not makes_some_xrx(s, Change(Kind.ADD_ASSERTION, 1, 0)) and related_pairs(s) == 1
    assert not makes_some_xrx(MState.of(1, [(0, 0)]), Change(Kind.ADD_ASSERTION, 0, 0))
