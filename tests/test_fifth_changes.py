from __future__ import annotations

from collections.abc import Iterator
from itertools import product
from math import comb

import pytest

from fifth.changes import (
    KINDS,
    REMOVAL_IS_REFUSAL,
    Answer,
    AnswerKind,
    Change,
    Kind,
    answers,
    attempt_counts,
    changes,
    is_build_of,
    is_change,
    obstruction,
    obstruction_counted,
    one_term_builds,
    perform,
)
from fifth.state import MState, given
from fourth.changes import changes as changes_fourth
from xry.state import Sameness


def legal_states(upto: int, most: int = 2) -> Iterator[MState]:
    """Every legal state with 1..upto terms and no multiplicity above `most`, names on 0 and 1 % n."""
    for n in range(1, upto + 1):
        for mult in product(range(most + 1), repeat=n * n):
            state = MState(n, mult, (0, 1 % n))
            if state.legal:
                yield state


def test_four_kinds_in_the_seeds_order() -> None:
    assert KINDS == (Kind.IDENTIFY, Kind.REMOVE, Kind.ADD_TERM, Kind.ADD_ASSERTION)
    assert all(is_change(Change(kind, 0, 1)) for kind in KINDS)
    assert "refusal" in REMOVAL_IS_REFUSAL
    assert Change(Kind.ADD_TERM).additions == (1, 0) and Change(Kind.ADD_ASSERTION, 0, 1).additions == (0, 1)
    assert Change(Kind.REMOVE, 0, 1).additions == (0, 0) == Change(Kind.IDENTIFY, 0, 1).additions
    g = given(False, Sameness.ANCHORED)
    assert Change(Kind.ADD_TERM).written(g) == "add a term"
    assert Change(Kind.ADD_ASSERTION, 1, 0).written(g) == "add bra"
    assert Change(Kind.REMOVE, 0, 1).written(g) == "remove arb"
    assert Change(Kind.IDENTIFY, 0, 1).written(g) == "identify a and b"


def test_the_list_of_changes_and_its_counts() -> None:
    seen = 0
    for state in legal_states(3):
        listed = changes(state)
        kinds = [c.kind for c in listed]
        assert kinds == sorted(kinds, key=list(Kind).index)
        additions = [sum(c.additions) for c in listed]
        assert additions == sorted(additions)
        attempts, obstructed = attempt_counts(state)
        n = state.n
        assert len(listed) == attempts == comb(n, 2) + state.distinct + 1 + n * n
        assert sum(1 for c in listed if obstruction(state, c)) == obstructed
        assert sum(1 for c in listed if c.kind is Kind.REMOVE) == state.distinct
        assert [c for c in listed if c.kind is Kind.REMOVE] == [Change(Kind.REMOVE, x, y) for x, y in state.pairs]
        # The fourth derivation's changes are the additions of this list.
        ours = [(c.kind, c.x, c.y) for c in listed if c.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION)]
        assert ours == [(c.kind, c.x, c.y) for c in changes_fourth(state)]
        seen += 1
    assert seen > 100
    g = given(False, Sameness.ANCHORED)
    assert len(changes(g)) == 7 and attempt_counts(g) == (7, 3)
    assert attempt_counts(given(True, Sameness.ANCHORED)) == (8, 3)
    assert attempt_counts(MState.of(2, [], (0, 1))) == (6, 2)


def test_perform_each_kind() -> None:
    s = given(True, Sameness.ANCHORED)
    assert perform(s, Change(Kind.ADD_TERM)) == MState.of(3, [(0, 1), (1, 0)], (0, 1))
    assert perform(s, Change(Kind.ADD_ASSERTION, 0, 1)) == MState.of(2, [(0, 1), (0, 1), (1, 0)], (0, 1))
    assert perform(s, Change(Kind.REMOVE, 1, 0)) == given(False, Sameness.ANCHORED)
    assert perform(s, Change(Kind.IDENTIFY, 0, 1)) == MState.of(1, [(0, 0), (0, 0)], (0, 0))
    assert not perform(s, Change(Kind.IDENTIFY, 0, 1)).legal
    assert not perform(s, Change(Kind.ADD_ASSERTION, 1, 1)).legal
    with pytest.raises(ValueError):
        perform(s, Change(Kind.REMOVE, 0, 0))
    three = MState.of(3, [(0, 1), (2, 1)], (0, 1))
    assert perform(three, Change(Kind.IDENTIFY, 0, 2)) == MState.of(2, [(0, 1), (0, 1)], (0, 1))
    assert perform(three, Change(Kind.IDENTIFY, 1, 2)) == MState.of(2, [(0, 1), (1, 1)], (0, 1))


def test_obstructed_exactly_when_xrx_would_be_asserted() -> None:
    seen = 0
    for state in legal_states(3):
        for change in changes(state):
            blocked = bool(obstruction(state, change))
            assert blocked == (not perform(state, change).legal)
            if change.kind is Kind.IDENTIFY:
                assert blocked == state.related(change.x, change.y)
                assert set(obstruction(state, change)) <= {(change.x, change.y), (change.y, change.x)}
            elif change.kind is Kind.ADD_ASSERTION:
                assert blocked == (change.x == change.y)
            else:
                assert not blocked
            counted = obstruction_counted(state, change)
            assert [(x, y) for x, y, _ in counted] == list(obstruction(state, change))
            assert all(k == (1 if change.kind is Kind.ADD_ASSERTION else state.mult_of(x, y)) for x, y, k in counted)
            seen += blocked
    assert seen > 0


def test_answers_to_an_obstructed_identification() -> None:
    s = MState.of(2, [(0, 1), (0, 1), (1, 0)], (0, 1))
    change = Change(Kind.IDENTIFY, 0, 1)
    got = answers(s, change)
    assert [a.kind for a in got] == [AnswerKind.REFUSE, AnswerKind.REMOVE_OBSTRUCTION, AnswerKind.BUILD]
    refuse, removal, build = got
    assert refuse.result == s and refuse.performed == 0
    assert removal.completes and removal.performed == 4
    assert [c.kind for c in removal.further] == [Kind.REMOVE] * 3
    assert removal.result == MState.of(1, [], (0, 0)) and removal.result.legal
    assert build.result == s and build.performed == 0 and not build.completes
    assert is_build_of(build.result, s, change)
    assert obstruction_counted(s, change) == ((0, 1, 2), (1, 0, 1))
    one_way = answers(given(False, Sameness.FREE), change)
    assert one_way[1].performed == 2 and one_way[1].result == MState.of(1, [])


def test_answers_to_adding_xrx_are_the_fourth_derivations() -> None:
    s = given(False, Sameness.ANCHORED)
    change = Change(Kind.ADD_ASSERTION, 0, 0)
    got = answers(s, change)
    assert [a.kind for a in got] == [AnswerKind.REFUSE, AnswerKind.BUILD, AnswerKind.BUILD]
    assert all(a.result.legal for a in got) and got[0].result == s
    for build in got[1:]:
        assert build.performed == 2 and not build.completes
        assert [c.kind for c in build.further] == [Kind.ADD_TERM, Kind.ADD_ASSERTION]
        assert is_build_of(build.result, s, change)
    assert got[1].result.pairs == ((0, 1), (0, 2)) and got[2].result.pairs == ((0, 1), (2, 0))
    assert [b.result for b in got[1:]] == list(one_term_builds(s, 0))
    with pytest.raises(ValueError):
        answers(s, Change(Kind.ADD_TERM))
    with pytest.raises(ValueError):
        answers(s, Change(Kind.REMOVE, 0, 1))
    with pytest.raises(ValueError):
        answers(MState.of(2, [], (0, 1)), Change(Kind.IDENTIFY, 0, 1))
    assert Answer(AnswerKind.REFUSE, (Change(Kind.ADD_TERM),), True, s).performed == 2


def test_is_build_of() -> None:
    s = MState.of(3, [(0, 1), (1, 2)], (0, 1))
    add = Change(Kind.ADD_ASSERTION, 2, 2)
    assert all(is_build_of(b, s, add) for b in one_term_builds(s, 2))
    assert not is_build_of(MState.of(3, [(0, 1), (1, 2), (2, 2)], (0, 1)), s, add)  # illegal
    assert not is_build_of(s, s, Change(Kind.ADD_ASSERTION, 0, 2))  # unobstructed
    ident = Change(Kind.IDENTIFY, 0, 2)
    assert not obstruction(s, ident)
    assert not is_build_of(s, s, ident)  # unobstructed
    blocked = Change(Kind.IDENTIFY, 1, 2)
    assert is_build_of(s, s, blocked)
    assert not is_build_of(MState.of(4, [(0, 1), (1, 2)], (0, 1)), s, blocked)  # a term added
    assert not is_build_of(MState.of(3, [(0, 1), (1, 2)], (1, 0)), s, blocked)  # names moved
    assert not is_build_of(MState.of(3, [(0, 1)], (0, 1)), s, blocked)  # an assertion missing
    assert not is_build_of(MState.of(3, [(0, 1), (1, 2), (0, 2)], (0, 1)), s, blocked)  # something else added
    assert not is_build_of(MState.of(3, [(0, 1), (1, 2)], (0, 1)), s, Change(Kind.REMOVE, 0, 1))
