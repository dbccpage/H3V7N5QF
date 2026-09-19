from __future__ import annotations

from collections.abc import Iterator
from itertools import product
from math import comb

from fifth.changes import changes as changes_fifth
from fifth.changes import obstruction as obstruction_fifth
from fifth.changes import perform as perform_fifth
from sixth.changes import KINDS, Change, Kind, attempt_counts, changes, is_change, makes_some_xrx, perform, related_pairs
from sixth.state import MState, given
from xry.state import Sameness


def states(upto: int, most: int = 2) -> Iterator[MState]:
    """Every state with 1..upto terms and no multiplicity above `most`, names on 0 and 1 % n."""
    for n in range(1, upto + 1):
        for mult in product(range(most + 1), repeat=n * n):
            yield MState(n, mult, (0, 1 % n))


def test_the_four_kinds_and_the_list_are_the_fifths() -> None:
    assert KINDS == (Kind.IDENTIFY, Kind.REMOVE, Kind.ADD_TERM, Kind.ADD_ASSERTION)
    assert changes is changes_fifth and perform is perform_fifth
    assert all(is_change(Change(kind, 0, 1)) for kind in KINDS)
    g = given(False, Sameness.ANCHORED)
    assert Change(Kind.ADD_ASSERTION, 0, 0).written(g) == "add ara"
    assert Change(Kind.IDENTIFY, 0, 1).written(g) == "identify a and b"


def test_every_change_is_performed_and_counted() -> None:
    seen = 0
    for state in states(3):
        listed = changes(state)
        attempts, xrx = attempt_counts(state)
        n = state.n
        assert len(listed) == attempts == comb(n, 2) + state.distinct + 1 + n * n
        assert sum(1 for c in listed if makes_some_xrx(state, c)) == xrx
        if state.legal:
            assert xrx == n + related_pairs(state)
            assert all(makes_some_xrx(state, c) == bool(obstruction_fifth(state, c)) for c in listed)
        else:
            assert xrx == 0 and not any(makes_some_xrx(state, c) for c in listed)
        for c in listed:
            perform(state, c)  # never refused
        seen += 1
    assert seen > 100
    assert attempt_counts(given(False, Sameness.ANCHORED)) == (7, 3)
    assert attempt_counts(given(True, Sameness.ANCHORED)) == (8, 3)
    assert attempt_counts(MState.of(2, [(0, 1), (0, 0)], (0, 1))) == (8, 0)
    assert related_pairs(MState.of(3, [(0, 1), (1, 1)], (0, 1))) == 1


def test_perform_each_kind_with_nothing_forbidden() -> None:
    s = given(True, Sameness.ANCHORED)
    assert perform(s, Change(Kind.IDENTIFY, 0, 1)) == MState.of(1, [(0, 0), (0, 0)], (0, 0))
    assert perform(s, Change(Kind.ADD_ASSERTION, 0, 0)) == MState.of(2, [(0, 1), (1, 0), (0, 0)], (0, 1))
    loop = MState.of(2, [(0, 1), (0, 0), (1, 1)], (0, 1))
    assert perform(loop, Change(Kind.IDENTIFY, 0, 1)) == MState.of(1, [(0, 0)] * 3, (0, 0))
    assert perform(loop, Change(Kind.REMOVE, 1, 1)) == MState.of(2, [(0, 1), (0, 0)], (0, 1))
    assert perform(loop, Change(Kind.ADD_TERM)) == MState.of(3, [(0, 1), (0, 0), (1, 1)], (0, 1))
    assert makes_some_xrx(s, Change(Kind.IDENTIFY, 0, 1)) and makes_some_xrx(s, Change(Kind.ADD_ASSERTION, 1, 1))
    assert not makes_some_xrx(s, Change(Kind.ADD_ASSERTION, 0, 1)) and not makes_some_xrx(loop, Change(Kind.ADD_ASSERTION, 1, 1))
