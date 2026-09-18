from __future__ import annotations

import pytest

from second.reach import reachable as reachable_second
from third.explore import explore
from third.reach import contains, embedding, embeds, reachable, reachable_by_search
from xry.state import Sameness, State, canonical, given

ARB = given(False, Sameness.ANCHORED)
BOTH = given(True, Sameness.ANCHORED)


def test_contains_as_written() -> None:
    star = State.of(3, [(0, 1), (0, 2)], (0, 1))
    assert contains(ARB, star) and not contains(star, ARB)
    assert contains(ARB, ARB) and contains(ARB, BOTH) and not contains(BOTH, ARB)
    assert not contains(ARB, State.of(3, [(0, 1), (0, 2)]))  # names on one side only
    assert not contains(ARB, State.of(3, [(0, 1), (0, 2)], (1, 0)))  # names moved
    assert not contains(ARB, State.of(3, [(1, 0), (0, 2)], (0, 1)))  # arb missing
    assert contains(given(False, Sameness.FREE), State.of(3, [(0, 1), (2, 0)]))


def test_embeds() -> None:
    star = State.of(3, [(0, 1), (0, 2)], (0, 1))
    assert embeds((0, 1), ARB, star)
    assert not embeds((0, 0), State.of(2, [], (0, 0)), State.of(1, [], (0, 0)))  # not one-to-one
    assert not embeds((1, 0), ARB, star)  # names not carried
    free = State.of(2, [(0, 1)])
    assert embeds((2, 0), free, State.of(3, [(2, 0)])) and not embeds((0, 0), free, State.of(2, [(0, 0)]))


def test_embedding_needs_names_on_both_sides_or_neither() -> None:
    with pytest.raises(ValueError):
        embedding(given(False, Sameness.FREE), ARB)


def test_embedding_examples() -> None:
    assert embedding(ARB, State.of(3, [(0, 1)], (0, 1))) == (0, 1)
    assert embedding(ARB, BOTH) == (0, 1)
    assert embedding(BOTH, ARB) is None
    assert embedding(ARB, State.of(1, [], (0, 0))) is None
    assert embedding(State.of(1, [], (0, 0)), ARB) is None
    assert embedding(State.of(2, [], (0, 0)), State.of(2, [], (0, 1))) is None  # a = b on one side
    three = State.of(3, [(0, 1), (1, 2), (2, 0)], (0, 1))
    six = State.of(6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)], (0, 1))
    assert embedding(six, three) is None  # the second seed carried it; no embedding
    assert reachable_second(six, three) and not reachable(six, three)
    assert embedding(three, six) is None
    free = State.of(3, [(0, 1), (1, 2)])
    assert embedding(free, State.of(2, [(0, 1), (1, 0)])) is None  # the second seed merged terms
    around = State.of(3, [(1, 0), (0, 2), (2, 1)])
    q = embedding(free, around)
    assert q is not None and embeds(q, free, around)
    assert embedding(free, State.of(3, [(0, 1)])) is None


def test_what_is_given_is_never_returned_to() -> None:
    star = State.of(3, [(0, 1), (0, 2)], (0, 1))
    assert reachable(ARB, star) and not reachable(star, ARB)
    assert reachable(ARB, BOTH) and not reachable(BOTH, ARB)
    square = State.of(4, [(0, 1), (1, 0), (0, 3), (3, 0), (2, 1), (1, 2), (2, 3), (3, 2)], (0, 1))
    assert reachable(BOTH, square) and not reachable(square, BOTH)
    assert reachable_second(square, BOTH)


def test_search_stays_within_the_bound() -> None:
    assert reachable_by_search(ARB, 2) == {ARB, BOTH}
    assert reachable_by_search(BOTH, 2) == {BOTH}
    assert len(reachable_by_search(ARB, 3)) == 2 + 32


@pytest.mark.parametrize(("sameness", "bra"), [(Sameness.FREE, False), (Sameness.ANCHORED, True)])
def test_embeddings_agree_with_the_search_and_are_one_way(sameness: Sameness, bra: bool) -> None:
    bound = 3
    results = set(explore(given(bra, sameness), bound, rounds=30).depth)
    for s in results:
        found = reachable_by_search(s, bound)
        assert found <= results
        assert found == {t for t in results if reachable(s, t)}
        assert canonical(s) in found
        for t in found:
            assert reachable_second(s, t)
            if t != s:
                assert not reachable(t, s)


def test_reachable_states_contain_what_is_given() -> None:
    for t in explore(ARB, 3, rounds=30).depth:
        q = embedding(ARB, t)
        assert q is not None and q[0] != q[1] and t.has(q[0], q[1])
