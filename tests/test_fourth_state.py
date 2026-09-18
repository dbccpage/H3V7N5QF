from __future__ import annotations

from itertools import permutations

import pytest

from fourth.state import (
    GIVEN_ASSERTIONS,
    GIVEN_TERMS,
    MState,
    added,
    canonical,
    given,
    of_state,
    rewrite,
    same,
    support,
)
from xry.state import Sameness, State
from xry.state import canonical as canonical_support


def test_a_state_is_checked() -> None:
    with pytest.raises(ValueError):
        MState(-1, ())
    with pytest.raises(ValueError):
        MState(2, (0, 1, 0))
    with pytest.raises(ValueError):
        MState(2, (0, -1, 0, 0))
    with pytest.raises(ValueError):
        MState(2, (0, 1, 0, 0), (0, 2))
    with pytest.raises(ValueError):
        MState.of(2, [(0, 2)])
    assert MState(0, ()).size == 0 and MState(0, ()).most == 0


def test_multiplicities_are_counted() -> None:
    s = MState.of(3, [(0, 1), (0, 1), (1, 2)], (0, 1))
    assert s.mult == (0, 2, 0, 0, 0, 1, 0, 0, 0)
    assert s.mult_of(0, 1) == 2 and s.mult_of(1, 0) == 0
    assert s.has(0, 1) and s.has(1, 2) and not s.has(2, 1)
    assert s.pairs == ((0, 1), (1, 2)) and s.counted == ((0, 1, 2), (1, 2, 1))
    assert s.m == 3 and s.distinct == 2 and s.size == 6 and s.most == 2
    assert s.legal and not s.simple and s.loops == ()
    assert s.related(2, 1) and s.related(1, 2) and not s.related(0, 2)
    loop = MState.of(2, [(1, 1), (1, 1)])
    assert loop.loops == (1,) and not loop.legal and not loop.simple
    assert MState.of(2, [(0, 1)]).simple and MState.of(1, []).simple


def test_writing() -> None:
    s = MState.of(3, [(0, 1), (0, 1), (2, 0)], (0, 1))
    assert s.key() == "3:01:0-1*2.2-0*1"
    assert s.term_writing() == ("a", "b", "c")
    assert s.written() == "terms a b c; asserted arb(2) cra"
    assert MState.of(2, [], (0, 0)).written() == "terms a c (a and b are one term); asserted nothing"
    assert MState.of(3, [(2, 1)], (1, 0)).written() == "terms b a c; asserted cra"
    free = MState.of(2, [(1, 0)])
    assert free.key() == "2::1-0*1" and free.written() == "terms a b; asserted bra"
    assert MState.of(3, [], (1, 1)).term_writing() == ("c", "a", "d")


def test_support_and_indicator() -> None:
    s = MState.of(3, [(0, 1), (0, 1), (2, 0)], (0, 1))
    assert support(s) == State.of(3, [(0, 1), (2, 0)], (0, 1))
    assert of_state(support(s)) == MState.of(3, [(0, 1), (2, 0)], (0, 1))
    simple = MState.of(3, [(0, 1), (2, 0)])
    assert of_state(support(simple)) == simple
    assert support(of_state(State.of(2, [(0, 1), (1, 0)]))) == State.of(2, [(0, 1), (1, 0)])


def test_rewrite() -> None:
    s = MState.of(3, [(0, 1), (0, 1), (1, 2)], (0, 1))
    t = rewrite(s, (2, 0, 1))
    assert t == MState.of(3, [(2, 0), (2, 0), (0, 1)], (2, 0))
    assert rewrite(t, (1, 2, 0)) == s
    with pytest.raises(ValueError):
        rewrite(s, (0, 0, 1))
    assert rewrite(MState.of(2, [(0, 1)]), (1, 0)) == MState.of(2, [(1, 0)])


def test_canonical_is_the_least_writing_and_equal_exactly_for_same_states() -> None:
    s = MState.of(3, [(0, 1), (0, 1), (1, 2)], (0, 1))
    for p in permutations(range(3)):
        t = rewrite(s, p)
        assert canonical(t) == canonical(s) and same(s, t)
        assert canonical(t) == min((rewrite(t, q) for q in permutations(range(3))), key=lambda u: (u.names, u.mult))
    free = MState(3, s.mult)
    assert canonical(free).names is None
    assert all(canonical(rewrite(free, p)) == canonical(free) for p in permutations(range(3)))
    assert canonical(s) is canonical(s)  # cached
    assert canonical(s).names == (0, 1) and canonical(MState.of(2, [(1, 0)], (1, 0))) == MState.of(2, [(0, 1)], (0, 1))
    assert not same(s, free) and not same(s, MState.of(2, [(0, 1)], (0, 1)))
    assert not same(s, MState.of(3, [(0, 1), (1, 2)], (0, 1)))  # a multiplicity differs
    swapped = MState.of(2, [(0, 1), (0, 1), (1, 0)], (0, 1))
    assert same(swapped, MState.of(2, [(1, 0), (1, 0), (0, 1)], (1, 0)))
    assert not same(swapped, MState.of(2, [(1, 0), (1, 0), (0, 1)], (0, 1)))  # names kept: bra twice differs
    assert same(MState(2, swapped.mult), MState.of(2, [(1, 0), (1, 0), (0, 1)]))  # any rewriting


def test_canonical_agrees_with_the_support_on_simple_states() -> None:
    for n in range(1, 4):
        for mask in range(1 << (n * n)):
            state = State(n, mask, (0, 1 % n))
            simple = of_state(state)
            assert canonical_support(support(canonical(simple))) == canonical_support(state)
            assert same(simple, of_state(canonical_support(state)))
            free = State(n, mask)
            assert canonical_support(support(canonical(of_state(free)))) == canonical_support(free)


def test_what_is_given() -> None:
    assert given(False, Sameness.ANCHORED) == MState.of(2, [(0, 1)], (0, 1))
    assert given(True, Sameness.ANCHORED) == MState.of(2, [(0, 1), (1, 0)], (0, 1))
    assert given(False, Sameness.FREE) == MState.of(2, [(0, 1)])
    assert given(True, Sameness.FREE).names is None and given(True, Sameness.FREE).m == 2
    for bra in (False, True):
        g = given(bra, Sameness.ANCHORED)
        assert g.legal and g.simple and g.mult_of(0, 1) == 1 and g.mult_of(1, 0) == int(bra)
        assert added(g) == (0, int(bra))
    assert (GIVEN_TERMS, GIVEN_ASSERTIONS) == (2, 1)
    assert added(MState.of(3, [(0, 1), (0, 1), (0, 1)], (0, 1))) == (1, 2)
    assert added(MState.of(1, [], (0, 0))) == (-1, -1)
