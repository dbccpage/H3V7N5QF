from __future__ import annotations

from collections.abc import Iterator
from itertools import product

import pytest

from fourth.changes import (
    KINDS,
    REMOVAL_IMPOSSIBLE,
    Answer,
    AnswerKind,
    Change,
    Kind,
    answers,
    attempt_counts,
    changes,
    image,
    is_build_of,
    is_change,
    obstruction,
    one_term_builds,
    perform,
)
from fourth.state import MState, given, of_state, support
from third.changes import answers as answers_third
from third.changes import changes as changes_third
from xry.changes import Change as ChangeThird
from xry.state import Sameness, State


def legal_states(upto: int, most: int = 2) -> Iterator[MState]:
    """Every legal state with 1..upto terms and no multiplicity above `most`, names on 0 and 1 % n."""
    for n in range(1, upto + 1):
        for mult in product(range(most + 1), repeat=n * n):
            state = MState(n, mult, (0, 1 % n))
            if state.legal:
                yield state


def test_two_kinds_in_the_seeds_order() -> None:
    assert KINDS == (Kind.ADD_TERM, Kind.ADD_ASSERTION)
    assert not is_change(Change(Kind.REMOVE, 0, 1))
    assert not is_change(Change(Kind.IDENTIFY, 0, 1))
    assert all(is_change(Change(kind, 0, 1)) for kind in KINDS)
    assert "lowers a multiplicity" in REMOVAL_IMPOSSIBLE and "refusal" in REMOVAL_IMPOSSIBLE
    assert Change(Kind.ADD_TERM).additions == (1, 0) and Change(Kind.ADD_ASSERTION, 0, 1).additions == (0, 1)
    g = given(False, Sameness.ANCHORED)
    assert Change(Kind.ADD_TERM).written(g) == "add a term"
    assert Change(Kind.ADD_ASSERTION, 1, 0).written(g) == "add bra"


def test_every_pair_is_a_change_and_the_third_derivations_list_is_the_new_pairs() -> None:
    seen = 0
    for state in legal_states(3, most=1):
        listed = changes(state)
        assert listed[0] == Change(Kind.ADD_TERM)
        assert all(sum(c.additions) == 1 and is_change(c) for c in listed)
        kinds = [c.kind for c in listed]
        assert kinds == sorted(kinds, key=list(Kind).index)
        attempts, obstructed = attempt_counts(state)
        assert len(listed) == attempts == 1 + state.n * state.n
        assert sum(1 for c in listed if obstruction(state, c)) == obstructed == state.n
        third = changes_third(support(state))
        kept = tuple(c for c in listed if c.kind is Kind.ADD_TERM or not state.has(c.x, c.y))
        assert [(c.kind, c.x, c.y) for c in kept] == [(c.kind, c.x, c.y) for c in third]
        seen += 1
    assert seen == 1 + 4 + 64
    twice = MState.of(2, [(0, 1), (0, 1)])
    assert len(changes(twice)) == 5 == len(changes(given(True, Sameness.FREE)))


def test_perform() -> None:
    s = given(False, Sameness.FREE)
    with pytest.raises(ValueError):
        perform(s, Change(Kind.REMOVE, 0, 1))
    with pytest.raises(ValueError):
        perform(s, Change(Kind.IDENTIFY, 0, 1))
    with pytest.raises(ValueError):
        perform(s, Change(Kind.ADD_ASSERTION, 0, 2))
    assert perform(s, Change(Kind.ADD_TERM)) == MState.of(3, [(0, 1)])
    assert perform(s, Change(Kind.ADD_ASSERTION, 1, 0)) == given(True, Sameness.FREE)
    assert perform(s, Change(Kind.ADD_ASSERTION, 0, 1)) == MState.of(2, [(0, 1), (0, 1)])
    assert not perform(s, Change(Kind.ADD_ASSERTION, 0, 0)).legal
    big = MState.of(3, [(0, 1), (0, 1), (2, 1)], (0, 1))
    grown = perform(big, Change(Kind.ADD_TERM))
    assert grown == MState.of(4, [(0, 1), (0, 1), (2, 1)], (0, 1)) and grown.names == (0, 1)


def test_obstructed_exactly_when_xrx_is_added() -> None:
    seen = 0
    for state in legal_states(3):
        for change in changes(state):
            blocked = bool(obstruction(state, change))
            assert blocked == (not perform(state, change).legal)
            assert blocked == (change.kind is Kind.ADD_ASSERTION and change.x == change.y)
            if blocked:
                assert obstruction(state, change) == ((change.x, change.x),)
            seen += blocked
    assert seen > 0


def test_answers_to_adding_xrx() -> None:
    s = given(False, Sameness.ANCHORED)
    change = Change(Kind.ADD_ASSERTION, 0, 0)
    got = answers(s, change)
    assert [a.kind for a in got] == [AnswerKind.REFUSE, AnswerKind.BUILD, AnswerKind.BUILD]
    assert all(a.result.legal for a in got)
    refuse = got[0]
    assert refuse.result == s and refuse.performed == 0 and not refuse.completes
    for build in got[1:]:
        assert build.performed == 2 and not build.completes
        assert [c.kind for c in build.further] == [Kind.ADD_TERM, Kind.ADD_ASSERTION]
        assert is_build_of(build.result, s, change)
    assert got[1].result.pairs == ((0, 1), (0, 2))
    assert got[2].result.pairs == ((0, 1), (2, 0))
    twice = MState.of(2, [(0, 1), (0, 1)], (0, 1))
    assert answers(twice, change)[1].result == MState.of(3, [(0, 1), (0, 1), (0, 2)], (0, 1))
    assert Answer(AnswerKind.REFUSE, (Change(Kind.ADD_TERM),), True, s).performed == 2


def test_only_an_obstructed_change_of_the_seed_is_answered() -> None:
    s = given(False, Sameness.ANCHORED)
    with pytest.raises(ValueError):
        answers(s, Change(Kind.ADD_TERM))
    with pytest.raises(ValueError):
        answers(s, Change(Kind.ADD_ASSERTION, 1, 0))
    with pytest.raises(ValueError):
        answers(s, Change(Kind.ADD_ASSERTION, 0, 1))
    with pytest.raises(ValueError):
        answers(s, Change(Kind.IDENTIFY, 0, 1))


def test_no_answer_removes_the_obstruction() -> None:
    for state in legal_states(3, most=1):
        for change in changes(state):
            if obstruction(state, change):
                kinds = [a.kind for a in answers(state, change)]
                assert AnswerKind.REMOVE_OBSTRUCTION not in kinds
                assert kinds == [AnswerKind.REFUSE, AnswerKind.BUILD, AnswerKind.BUILD]


def test_image_adds_up_multiplicities() -> None:
    built = MState.of(3, [(0, 1), (0, 2), (2, 1)], (0, 1))
    assert image(built, (0, 1, 0), 2, (0, 1)) == MState.of(2, [(0, 1), (0, 0), (0, 1)], (0, 1))
    assert image(built, (0, 1, 2), 3, (0, 1)) == built


def test_exactly_two_builds_add_one_term() -> None:
    with pytest.raises(ValueError):
        one_term_builds(given(False, Sameness.ANCHORED), 2)
    for state in [given(False, Sameness.ANCHORED), MState.of(2, [(0, 1), (0, 1), (1, 0)], (0, 1)), given(True, Sameness.FREE)]:
        for x in range(state.n):
            change = Change(Kind.ADD_ASSERTION, x, x)
            two = one_term_builds(state, x)
            assert len(two) == 2 and all(is_build_of(b, state, change) for b in two)
            assert two[0].mult_of(x, state.n) == 1 and two[1].mult_of(state.n, x) == 1
            # Every other candidate with one added term and multiplicities at most 2 is not a build.
            n = state.n + 1
            found = []
            for extra in product(range(3), repeat=2 * state.n + 1):
                mult = list(perform(state, Change(Kind.ADD_TERM)).mult)
                cells = [(u, n - 1) for u in range(state.n)] + [(n - 1, v) for v in range(state.n)] + [(n - 1, n - 1)]
                for (u, v), k in zip(cells, extra):
                    mult[u * n + v] = k
                cand = MState(n, tuple(mult), state.names)
                if is_build_of(cand, state, change):
                    found.append(cand)
            assert sorted(found, key=lambda s: s.mult) == sorted(two, key=lambda s: s.mult)


def test_is_build_of_refuses_what_is_not_a_build() -> None:
    s = given(False, Sameness.ANCHORED)
    change = Change(Kind.ADD_ASSERTION, 0, 0)
    good = one_term_builds(s, 0)[0]
    assert is_build_of(good, s, change)
    assert not is_build_of(MState.of(3, [(0, 1), (0, 0)], (0, 1)), s, change)  # illegal
    assert not is_build_of(good, s, Change(Kind.ADD_ASSERTION, 0, 1))  # unobstructed
    assert not is_build_of(MState.of(2, [(0, 1)], (0, 1)), s, change)  # no added term
    assert not is_build_of(MState.of(3, [(0, 1), (0, 2)], (1, 0)), s, change)  # names moved
    assert not is_build_of(MState.of(3, [(0, 1), (0, 1), (0, 2)], (0, 1)), s, change)  # arb raised
    assert not is_build_of(MState.of(3, [(0, 1), (0, 2), (2, 0)], (0, 1)), s, change)  # xrx twice
    assert not is_build_of(MState.of(3, [(0, 1), (0, 2), (2, 1)], (0, 1)), s, change)  # a copy of arb
    assert not is_build_of(MState.of(3, [(0, 1)], (0, 1)), s, change)  # nothing stands for xrx
    two = MState.of(4, [(0, 1), (0, 2), (3, 1)], (0, 1))
    assert not is_build_of(two, s, change)
    assert is_build_of(MState.of(4, [(0, 1), (0, 2)], (0, 1)), s, change)  # two added terms, one used


def test_the_third_derivations_answers_are_the_answers_on_simple_states() -> None:
    for state in legal_states(3, most=1):
        for change in changes(state):
            if not obstruction(state, change):
                continue
            ours = answers(state, change)
            theirs = answers_third(support(state), ChangeThird(change.kind, change.x, change.y))
            assert [a.kind for a in ours] == [a.kind for a in theirs]
            assert [support(a.result) for a in ours] == [a.result for a in theirs]
            assert [of_state(a.result) for a in theirs] == [a.result for a in ours]
    assert State.of(2, [(0, 1)]) == support(given(False, Sameness.FREE))
