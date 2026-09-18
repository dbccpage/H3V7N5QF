from __future__ import annotations

from itertools import product

import pytest

from fourth.cost import (
    contains_given,
    cost,
    cost_anchored,
    cost_free,
    cost_free_by_placement,
    given_size,
    has_two_way,
)
from fourth.explore import explore
from fourth.reach import contains, embedding, embeds, reachable, reachable_by_search
from fourth.state import MState, canonical, given, support
from third.reach import reachable as reachable_third
from xry.state import Sameness
from xry.state import canonical as canonical_support

ARB = given(False, Sameness.ANCHORED)
BOTH = given(True, Sameness.ANCHORED)
TWICE = MState.of(2, [(0, 1), (0, 1)], (0, 1))


def test_cost_in_closed_form() -> None:
    with pytest.raises(ValueError):
        contains_given(given(False, Sameness.FREE), False)
    assert contains_given(ARB, False) and not contains_given(ARB, True)
    assert contains_given(BOTH, True) and contains_given(TWICE, False)
    assert not contains_given(MState.of(2, [(0, 1)], (0, 0)), False)
    assert has_two_way(BOTH) and not has_two_way(TWICE)
    assert given_size(False) == 3 and given_size(True) == 4
    assert cost_anchored(TWICE, False) == 1 and cost_anchored(TWICE, True) is None
    assert cost_anchored(MState.of(2, [(0, 1), (1, 1)], (0, 1)), False) is None
    assert cost_free(MState.of(2, [(0, 1), (0, 1), (0, 1)]), False) == 2
    assert cost_free(MState.of(2, [(0, 1), (0, 1)]), True) is None
    assert cost_free(MState.of(3, [(1, 2), (2, 1), (2, 1)]), True) == 2
    assert cost_free(MState.of(3, []), False) is None
    assert cost_free(MState.of(2, [(0, 0), (0, 1)]), False) is None
    assert cost(TWICE, False) == 1 and cost(MState(2, TWICE.mult), False) == 1
    for bra in (False, True):
        for n in (1, 2, 3):
            for mult in product(range(3), repeat=n * n):
                state = MState(n, mult)
                assert cost_free(state, bra) == cost_free_by_placement(state, bra)


def test_contains_as_written() -> None:
    star = MState.of(3, [(0, 1), (0, 2)], (0, 1))
    assert contains(ARB, star) and not contains(star, ARB)
    assert contains(ARB, ARB) and contains(ARB, BOTH) and not contains(BOTH, ARB)
    assert contains(ARB, TWICE) and not contains(TWICE, ARB)
    assert not contains(ARB, MState.of(3, [(0, 1), (0, 2)]))  # names on one side only
    assert not contains(ARB, MState.of(3, [(0, 1), (0, 2)], (1, 0)))  # names moved
    assert not contains(ARB, MState.of(3, [(1, 0), (0, 2)], (0, 1)))  # arb missing
    assert contains(given(False, Sameness.FREE), MState.of(3, [(0, 1), (2, 0)]))


def test_embeds() -> None:
    star = MState.of(3, [(0, 1), (0, 2)], (0, 1))
    assert embeds((0, 1), ARB, star)
    assert not embeds((0,), ARB, star)  # wrong length
    assert not embeds((0, 0), MState.of(2, [], (0, 0)), MState.of(1, [], (0, 0)))  # not one-to-one
    assert not embeds((0, 3), ARB, star)  # out of range
    assert not embeds((1, 0), ARB, star)  # names not carried
    assert not embeds((0, 1), ARB, MState.of(3, [(0, 1), (0, 2)]))  # names on one side only
    assert not embeds((0, 1), given(False, Sameness.FREE), star)
    assert not embeds((0, 1), TWICE, ARB)  # a multiplicity falls short
    assert embeds((0, 1), ARB, TWICE)
    free = MState.of(2, [(0, 1)])
    assert embeds((2, 0), free, MState.of(3, [(2, 0)])) and not embeds((0, 0), free, MState.of(2, [(0, 0)]))


def test_embedding_needs_names_on_both_sides_or_neither() -> None:
    with pytest.raises(ValueError):
        embedding(given(False, Sameness.FREE), ARB)


def test_embedding_examples() -> None:
    assert embedding(ARB, MState.of(3, [(0, 1)], (0, 1))) == (0, 1)
    assert embedding(ARB, BOTH) == (0, 1) and embedding(ARB, TWICE) == (0, 1)
    assert embedding(BOTH, ARB) is None and embedding(TWICE, ARB) is None
    assert embedding(TWICE, BOTH) is None and embedding(BOTH, TWICE) is None
    assert embedding(ARB, MState.of(1, [], (0, 0))) is None
    assert embedding(MState.of(1, [], (0, 0)), ARB) is None
    assert embedding(MState.of(2, [], (0, 0)), MState.of(2, [], (0, 1))) is None  # a = b on one side
    assert embedding(MState.of(1, [(0, 0)]), MState.of(2, [(0, 1), (1, 0)])) is None  # xrx never carried
    free = MState.of(3, [(0, 1), (1, 2), (1, 2)])
    around = MState.of(3, [(1, 0), (0, 2), (0, 2), (2, 1)])
    q = embedding(free, around)
    assert q is not None and embeds(q, free, around)
    assert embedding(free, MState.of(3, [(1, 0), (0, 2), (2, 1)])) is None  # one multiplicity short
    assert embedding(free, MState.of(3, [(0, 1)])) is None


def test_what_is_given_is_never_returned_to() -> None:
    star = MState.of(3, [(0, 1), (0, 2)], (0, 1))
    assert reachable(ARB, star) and not reachable(star, ARB)
    assert reachable(ARB, BOTH) and not reachable(BOTH, ARB)
    assert reachable(ARB, TWICE) and not reachable(TWICE, ARB)
    more = MState.of(2, [(0, 1), (0, 1), (1, 0), (1, 0)], (0, 1))
    assert reachable(TWICE, more) and reachable(BOTH, more) and not reachable(more, TWICE)


def test_search_stays_within_the_bound() -> None:
    assert reachable_by_search(ARB, 2, 0) == {canonical(ARB)}
    assert reachable_by_search(ARB, 2, 1) == {canonical(ARB), canonical(BOTH), canonical(TWICE)}
    assert len(reachable_by_search(ARB, 2, 10)) == sum(r + 1 for r in range(11))
    assert len(reachable_by_search(ARB, 3, 3)) == len(explore(ARB, 3, 3).depth)


@pytest.mark.parametrize(("sameness", "bra"), [(Sameness.FREE, False), (Sameness.ANCHORED, True)])
def test_embeddings_agree_with_the_search_and_are_one_way(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 3, 4
    expl = explore(given(bra, sameness), bound, rounds)
    results = set(expl.depth)
    for s in results:
        found = reachable_by_search(s, bound, rounds - expl.depth[s])
        assert found <= results
        assert found == {t for t in results if reachable(s, t)}
        assert canonical(s) in found
        for t in found:
            if t != s:
                assert not reachable(t, s)
            if s.simple and t.simple:
                assert reachable_third(canonical_support(support(s)), canonical_support(support(t)))


def test_reachable_states_contain_what_is_given() -> None:
    for t in explore(ARB, 3, 5).depth:
        q = embedding(ARB, t)
        assert q is not None and q[0] != q[1] and t.has(q[0], q[1])
