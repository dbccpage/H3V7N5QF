from __future__ import annotations

from collections.abc import Iterator

import pytest

from second.changes import (
    KINDS,
    REMOVAL_IMPOSSIBLE,
    answers,
    changes,
    is_build_of,
    is_change,
    obstruction,
    perform,
)
from xry.changes import AnswerKind, Change, Kind
from xry.changes import changes as changes_first
from xry.state import Sameness, State, given


def legal_states(upto: int) -> Iterator[State]:
    """Every legal state with 1..upto terms, in every writing, names on 0 and 1 % n."""
    for n in range(1, upto + 1):
        for mask in range(1 << (n * n)):
            state = State(n, mask, (0, 1 % n))
            if state.legal:
                yield state


def test_three_kinds_in_the_seeds_order() -> None:
    assert KINDS == (Kind.IDENTIFY, Kind.ADD_TERM, Kind.ADD_ASSERTION)
    assert not is_change(Change(Kind.REMOVE, 0, 1))
    assert all(is_change(Change(kind, 0, 1)) for kind in KINDS)
    assert "un-asserts" in REMOVAL_IMPOSSIBLE


def test_changes_are_the_first_derivations_without_removals() -> None:
    seen = 0
    for state in legal_states(3):
        listed = changes(state)
        assert listed == tuple(c for c in changes_first(state) if c.kind is not Kind.REMOVE)
        kinds = [c.kind for c in listed]
        assert kinds == sorted(kinds, key=list(Kind).index)
        assert [sum(c.additions) for c in listed] == sorted(sum(c.additions) for c in listed)
        assert all(is_change(c) for c in listed)
        seen += 1
    assert seen == 1 + 4 + 64
    s = State.of(3, [(0, 1), (1, 2)])
    assert len(changes(s)) == 3 + 1 + (9 - 2)


def test_perform_refuses_a_removal() -> None:
    s = given(False, Sameness.FREE)
    with pytest.raises(ValueError):
        perform(s, Change(Kind.REMOVE, 0, 1))
    assert perform(s, Change(Kind.ADD_TERM)) == State.of(3, [(0, 1)])
    assert perform(s, Change(Kind.ADD_ASSERTION, 1, 0)) == given(True, Sameness.FREE)
    assert perform(s, Change(Kind.IDENTIFY, 0, 1)) == State.of(1, [(0, 0)])


def test_obstructed_exactly_when_some_xrx_would_be_asserted() -> None:
    seen = 0
    for state in legal_states(3):
        for change in changes(state):
            blocked = bool(obstruction(state, change))
            assert blocked == (not perform(state, change).legal)
            if change.kind is Kind.ADD_TERM:
                assert not blocked
            if change.kind is Kind.ADD_ASSERTION:
                assert blocked == (change.x == change.y)
            if change.kind is Kind.IDENTIFY:
                assert blocked == state.related(change.x, change.y)
            seen += blocked
    assert seen > 0


def test_answers_to_an_obstructed_identification() -> None:
    s = State.of(3, [(0, 1), (1, 0), (1, 2)], (0, 1))
    change = Change(Kind.IDENTIFY, 0, 1)
    got = answers(s, change)
    assert [a.kind for a in got] == [AnswerKind.REFUSE, AnswerKind.BUILD]
    refuse, build = got
    assert refuse.result == s and refuse.performed == 0 and not refuse.completes
    assert build.result == s and build.performed == 0 and not build.completes
    assert is_build_of(build.result, s, change)


def test_answers_to_adding_xrx() -> None:
    s = given(False, Sameness.ANCHORED)
    change = Change(Kind.ADD_ASSERTION, 0, 0)
    got = answers(s, change)
    assert [a.kind for a in got] == [AnswerKind.REFUSE, AnswerKind.BUILD, AnswerKind.BUILD]
    assert all(a.result.legal for a in got)
    for build in got[1:]:
        assert build.performed == 2 and not build.completes
        assert [c.kind for c in build.further] == [Kind.ADD_TERM, Kind.ADD_ASSERTION]
        assert is_build_of(build.result, s, change)
    assert got[1].result.pairs == ((0, 1), (0, 2))
    assert got[2].result.pairs == ((0, 1), (2, 0))


def test_only_an_obstructed_change_of_the_seed_is_answered() -> None:
    s = given(False, Sameness.ANCHORED)
    with pytest.raises(ValueError):
        answers(s, Change(Kind.ADD_TERM))
    with pytest.raises(ValueError):
        answers(s, Change(Kind.REMOVE, 0, 1))


def test_no_answer_removes_the_obstruction() -> None:
    for state in legal_states(3):
        for change in changes(state):
            if obstruction(state, change):
                assert all(a.kind is not AnswerKind.REMOVE_OBSTRUCTION for a in answers(state, change))
