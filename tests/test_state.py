from __future__ import annotations

from itertools import permutations

import pytest

from xry.state import (
    LETTERS,
    Sameness,
    State,
    added,
    canonical,
    given,
    letter,
    rewrite,
    same,
)


def test_letters_leave_out_r() -> None:
    assert "r" not in LETTERS and len(LETTERS) == 25
    assert [letter(i) for i in (0, 1, 16, 17, 24)] == ["a", "b", "q", "s", "z"]
    assert letter(25) == "aa" and letter(26) == "ab" and letter(25 + 25 * 25) == "aaa"
    with pytest.raises(ValueError):
        letter(-1)


def test_letters_are_distinct() -> None:
    assert len({letter(i) for i in range(2000)}) == 2000


def test_state_rejects_what_is_not_there() -> None:
    with pytest.raises(ValueError):
        State(-1, 0)
    with pytest.raises(ValueError):
        State(2, 16)
    with pytest.raises(ValueError):
        State(2, -1)
    with pytest.raises(ValueError):
        State(2, 0, (0, 2))
    with pytest.raises(ValueError):
        State.of(2, [(0, 2)])


def test_reading_a_state() -> None:
    s = State.of(3, [(0, 1), (1, 0), (2, 2)], (0, 1))
    assert s.pairs == ((0, 1), (1, 0), (2, 2))
    assert s.m == 3
    assert s.has(0, 1) and not s.has(0, 2)
    assert s.related(1, 0) and not s.related(0, 2)
    assert s.loops == (2,) and not s.legal
    assert State.of(3, [(0, 1)]).legal
    assert s.key() == "3:01:0-1.1-0.2-2"
    assert State.of(2, []).key() == "2::"


def test_writing_a_state() -> None:
    assert given(False, Sameness.ANCHORED).written() == "terms a b; asserted arb"
    assert given(True, Sameness.FREE).written() == "terms a b; asserted arb bra"
    named = State.of(3, [(2, 0)], (2, 0))
    assert named.term_writing() == ("b", "c", "a")
    assert named.written() == "terms b c a; asserted arb"
    merged = State.of(2, [(1, 0)], (0, 0))
    assert merged.written() == "terms a c (a and b are one term); asserted cra"
    assert State.of(1, []).written() == "terms a; asserted nothing"


def test_canonical_is_the_same_for_every_rewriting() -> None:
    s = State.of(4, [(0, 1), (1, 2), (3, 1)], (2, 3))
    forms = {canonical(rewrite(s, p)) for p in permutations(range(4))}
    assert len(forms) == 1
    free = State.of(4, s.pairs)
    assert len({canonical(rewrite(free, p)) for p in permutations(range(4))}) == 1
    assert canonical(s) is canonical(s)  # the second call is a cache hit


def test_the_two_readings_of_sameness_differ() -> None:
    arb = State.of(2, [(0, 1)])
    bra = State.of(2, [(1, 0)])
    assert same(arb, bra)
    assert not same(State(2, arb.mask, (0, 1)), State(2, bra.mask, (0, 1)))
    assert same(State(2, arb.mask, (0, 1)), State(2, bra.mask, (1, 0)))
    assert not same(arb, State.of(3, [(0, 1)]))
    assert not same(arb, State(2, arb.mask, (0, 1)))


def test_no_terms_at_all_is_a_state_but_not_a_result() -> None:
    empty = State(0, 0)
    assert canonical(empty) == empty and empty.pairs == ()


def test_rewrite_needs_a_rewriting() -> None:
    with pytest.raises(ValueError):
        rewrite(State.of(2, []), (0, 0))


def test_what_is_given() -> None:
    a = given(False, Sameness.ANCHORED)
    b = given(True, Sameness.ANCHORED)
    assert a.names == (0, 1) and a.pairs == ((0, 1),)
    assert b.pairs == ((0, 1), (1, 0))
    assert given(False, Sameness.FREE).names is None
    assert added(a) == (0, 0) and added(b) == (0, 1)
    assert added(State.of(1, [])) == (-1, -1)
