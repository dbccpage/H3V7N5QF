from __future__ import annotations

from collections.abc import Iterator

import pytest

from xry.changes import (
    AnswerKind,
    Change,
    Kind,
    answers,
    changes,
    identification_map,
    is_build_of,
    obstruction,
    one_term_builds,
    perform,
)
from xry.state import Sameness, State, canonical, given


def legal_states(upto: int) -> Iterator[State]:
    """Every legal state with 1..upto terms, in every writing, names on 0 and 1 % n."""
    for n in range(1, upto + 1):
        for mask in range(1 << (n * n)):
            state = State(n, mask, (0, 1 % n))
            if state.legal:
                yield state


def test_every_change_is_listed_fewest_additions_first() -> None:
    s = State.of(3, [(0, 1), (1, 2)])
    listed = changes(s)
    kinds = [c.kind for c in listed]
    assert kinds == sorted(kinds, key=list(Kind).index)
    assert len(listed) == 3 + 2 + 1 + (9 - 2)
    assert [sum(c.additions) for c in listed] == sorted(sum(c.additions) for c in listed)
    assert Change(Kind.ADD_TERM).additions == (1, 0)
    assert Change(Kind.ADD_ASSERTION, 0, 2).additions == (0, 1)
    assert Change(Kind.REMOVE, 0, 1).additions == (0, 0)


def test_changes_in_words() -> None:
    s = given(True, Sameness.ANCHORED)
    assert Change(Kind.IDENTIFY, 0, 1).written(s) == "identify a and b"
    assert Change(Kind.REMOVE, 1, 0).written(s) == "remove bra"
    assert Change(Kind.ADD_ASSERTION, 0, 0).written(s) == "add ara"
    assert Change(Kind.ADD_TERM).written(s) == "add a term"


def test_identifying_replaces_both_by_one_term_in_every_assertion() -> None:
    assert identification_map(4, 1, 2) == (0, 1, 1, 2)
    s = State.of(4, [(0, 1), (2, 3), (3, 0)], (2, 3))
    out = perform(s, Change(Kind.IDENTIFY, 1, 2))
    assert out.n == 3 and out.pairs == ((0, 1), (1, 2), (2, 0)) and out.names == (1, 2)
    free = perform(State.of(3, [(0, 2)]), Change(Kind.IDENTIFY, 0, 1))
    assert free.pairs == ((0, 1),) and free.names is None
    for bad in ((1, 1), (2, 1), (0, 4), (-1, 2)):
        with pytest.raises(ValueError):
            identification_map(4, *bad)


def test_the_other_three_kinds() -> None:
    s = given(False, Sameness.ANCHORED)
    assert perform(s, Change(Kind.ADD_TERM)) == State.of(3, [(0, 1)], (0, 1))
    assert perform(s, Change(Kind.REMOVE, 0, 1)) == State.of(2, [], (0, 1))
    assert perform(s, Change(Kind.ADD_ASSERTION, 1, 0)) == given(True, Sameness.ANCHORED)
    assert not perform(s, Change(Kind.ADD_ASSERTION, 1, 1)).legal


def test_nothing_else_is_a_change() -> None:
    s = given(False, Sameness.FREE)
    with pytest.raises(ValueError):
        perform(s, Change(Kind.REMOVE, 1, 0))
    with pytest.raises(ValueError):
        perform(s, Change(Kind.ADD_ASSERTION, 0, 1))
    with pytest.raises(ValueError):
        perform(s, Change(Kind.ADD_ASSERTION, 0, 2))
    with pytest.raises(ValueError):
        perform(s, Change(Kind.REMOVE, -1, 0))


def test_obstructed_exactly_when_some_xrx_would_be_asserted() -> None:
    seen = 0
    for state in legal_states(3):
        for change in changes(state):
            blocked = bool(obstruction(state, change))
            assert blocked == (not perform(state, change).legal)
            if change.kind in (Kind.REMOVE, Kind.ADD_TERM):
                assert not blocked
            seen += blocked
    assert seen > 0


def test_obstruction_names_the_assertions_in_the_way() -> None:
    both = given(True, Sameness.FREE)
    assert obstruction(both, Change(Kind.IDENTIFY, 0, 1)) == ((0, 1), (1, 0))
    assert obstruction(given(False, Sameness.FREE), Change(Kind.IDENTIFY, 0, 1)) == ((0, 1),)
    assert obstruction(both, Change(Kind.ADD_ASSERTION, 1, 1)) == ((1, 1),)
    assert obstruction(both, Change(Kind.ADD_TERM)) == ()


def test_answers_to_an_obstructed_identification() -> None:
    s = State.of(3, [(0, 1), (1, 0), (1, 2)], (0, 1))
    change = Change(Kind.IDENTIFY, 0, 1)
    refuse, remove, build = answers(s, change)
    assert refuse.kind is AnswerKind.REFUSE and refuse.result == s and refuse.performed == 0
    assert remove.kind is AnswerKind.REMOVE_OBSTRUCTION and remove.completes
    assert [c.kind for c in remove.further] == [Kind.REMOVE, Kind.REMOVE]
    assert remove.performed == 3
    assert remove.result == State.of(2, [(0, 1)], (0, 0))
    assert build.kind is AnswerKind.BUILD and build.result == s and build.performed == 0
    assert is_build_of(build.result, s, change)


def test_answers_to_adding_xrx() -> None:
    s = given(False, Sameness.ANCHORED)
    change = Change(Kind.ADD_ASSERTION, 0, 0)
    got = answers(s, change)
    assert [a.kind for a in got] == [AnswerKind.REFUSE, AnswerKind.BUILD, AnswerKind.BUILD]
    assert all(a.result.legal for a in got)
    for build in got[1:]:
        assert build.performed == 2 and not build.completes
        assert is_build_of(build.result, s, change)
    assert got[1].result.pairs == ((0, 1), (0, 2))
    assert got[2].result.pairs == ((0, 1), (2, 0))
    with pytest.raises(ValueError):
        answers(s, Change(Kind.ADD_TERM))


def test_removing_the_obstruction_first_or_last_gives_the_same_result() -> None:
    for state in legal_states(3):
        for change in changes(state):
            if change.kind is not Kind.IDENTIFY or not obstruction(state, change):
                continue
            removed_first = answers(state, change)[1].result
            forced = perform(state, change)
            (x,) = forced.loops
            removed_last = perform(forced, Change(Kind.REMOVE, x, x))
            assert removed_first == removed_last


def test_every_build_with_one_added_term() -> None:
    s = State.of(3, [(0, 1), (2, 0)], (0, 1))
    builds = one_term_builds(s, 0)
    assert len(builds) == 3 * 2**2 == len(set(builds))
    change = Change(Kind.ADD_ASSERTION, 0, 0)
    assert all(is_build_of(b, s, change) for b in builds)
    fewest = min(b.m for b in builds)
    assert fewest == s.m + 1
    assert {canonical(b) for b in builds if b.m == fewest} == {
        canonical(a.result) for a in answers(s, change)[1:]
    }
    with pytest.raises(ValueError):
        one_term_builds(s, 3)


def test_what_is_not_a_build() -> None:
    s = given(False, Sameness.ANCHORED)
    add = Change(Kind.ADD_ASSERTION, 0, 0)
    ident = Change(Kind.IDENTIFY, 0, 1)
    good = State.of(3, [(0, 1), (0, 2)], (0, 1))
    assert is_build_of(good, s, add)
    assert not is_build_of(State.of(3, [(0, 1), (0, 2), (2, 2)], (0, 1)), s, add)  # not legal
    assert not is_build_of(good, s, Change(Kind.ADD_TERM))  # nothing was obstructed
    assert not is_build_of(s, s, add)  # no term added
    assert not is_build_of(good, s, ident)  # an identification is answered with no addition
    assert not is_build_of(State.of(3, [(0, 1), (0, 2)], (1, 0)), s, add)  # names moved
    assert not is_build_of(State.of(3, [(0, 2)], (0, 1)), s, add)  # arb was dropped
    assert not is_build_of(State.of(3, [(0, 1), (1, 2)], (0, 1)), s, add)  # wrong image
    assert not is_build_of(State.of(3, [(0, 1)], (0, 1)), s, add)  # xrx is not the image of anything
    assert is_build_of(s, s, ident)
