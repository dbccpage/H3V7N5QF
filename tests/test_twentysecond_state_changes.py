"""The twenty-second seed's states and changes: the excess, the plain state, what is recorded, the moves."""

from __future__ import annotations

from itertools import permutations

import pytest

from twentysecond.changes import (
    Change,
    Kind,
    add_r_then_s,
    attempt_count,
    merge_loss,
    pad,
    padded_removals,
    perform,
    predicted_move,
    removal_move,
    result_changes,
)
from twentysecond.state import (
    DState,
    common,
    cost,
    empty,
    excess,
    is_plain,
    plain,
    recorded,
    result_of,
    rewrite,
    same,
    swap,
    together_count,
    written,
)

A = DState.of(1, [], [])
ARA = DState.of(1, [(0, 0)], [])
ASA = DState.of(1, [], [(0, 0)])
BOTH = DState.of(1, [(0, 0)], [(0, 0)])


def test_excess_plain_common() -> None:
    g = DState.of(2, [(0, 1), (0, 1), (1, 0)], [(0, 1), (1, 1)])
    assert excess(g, 0, 1) == 1 and excess(g, 1, 0) == 1 and excess(g, 1, 1) == -1 and excess(g, 0, 0) == 0
    assert common(g) == (0, 1, 0, 0) and together_count(g) == 1 and not is_plain(g)
    p = plain(g)
    assert p == DState.of(2, [(0, 1), (1, 0)], [(1, 1)]) and is_plain(p) and plain(p) == p
    assert recorded(g) == (2, 2, 1) and cost(g) == 5 and g.size == 7


def test_same_is_rewriting_and_pairs_together() -> None:
    assert same(A, BOTH) and not same(A, ARA) and not same(ARA, ASA)
    assert same(DState.of(2, [(0, 0)], []), DState.of(2, [(1, 1)], []))
    assert not same(A, DState.of(2, [], []))
    assert result_of(BOTH) == A
    g = DState.of(3, [(0, 1), (1, 2)], [(2, 0), (0, 1)])
    for p in permutations(range(3)):
        assert same(g, rewrite(g, p))
        assert same(g, pad(rewrite(g, p), p[0], p[1]))


def test_swap_negates_the_excess() -> None:
    g = DState.of(2, [(0, 1), (0, 1)], [(1, 0)])
    s = swap(g)
    assert all(excess(s, x, y) == -excess(g, x, y) for x in range(2) for y in range(2))
    assert recorded(s) == (2, 1, 2) and cost(s) == cost(g)


def test_written() -> None:
    assert written(empty()) == "no terms; asserted nothing"
    assert written(ARA).startswith("terms a")


def test_result_changes_and_attempt_count() -> None:
    assert [c.kind for c in result_changes(empty())] == [Kind.ADD_TERM]
    assert result_changes(BOTH) == result_changes(A)
    assert attempt_count(A) == 0 + 0 + 1 + 2
    assert attempt_count(BOTH) == attempt_count(A)
    assert attempt_count(DState.of(2, [(0, 1)], [(1, 0)])) == 1 + 2 + 1 + 8


def test_merge_loss() -> None:
    g = DState.of(2, [(0, 1)] * 3, [(1, 0)] * 3)
    assert merge_loss(g, 0, 1) == 3
    assert merge_loss(DState.of(2, [(0, 1)], [(0, 1)]), 0, 1) == 0
    assert merge_loss(DState.of(2, [(0, 0), (1, 1)], []), 0, 1) == 0
    assert merge_loss(DState.of(3, [(0, 2)], [(1, 2)]), 0, 1) == 1


def test_predicted_moves() -> None:
    assert predicted_move(ARA, Change(Kind.ADD_TERM)) == (1, 0)
    assert predicted_move(ARA, Change(Kind.ADD_ASSERTION, "s", 0, 0)) == (0, -1)
    assert predicted_move(ARA, Change(Kind.ADD_ASSERTION, "r", 0, 0)) == (0, 1)
    assert predicted_move(ASA, Change(Kind.ADD_ASSERTION, "r", 0, 0)) == (0, -1)
    assert predicted_move(ASA, Change(Kind.ADD_ASSERTION, "s", 0, 0)) == (0, 1)
    assert predicted_move(ARA, Change(Kind.REMOVE, "r", 0, 0)) == (0, -1)
    assert predicted_move(DState.of(2, [(0, 1)], [(1, 0)]), Change(Kind.IDENTIFY, "", 0, 1)) == (-1, -2)
    assert removal_move(BOTH, "r", 0, 0) == 1 and removal_move(BOTH, "s", 0, 0) == 1
    assert removal_move(ASA, "s", 0, 0) == -1 and removal_move(ARA, "s", 0, 0) == 1


def test_pad_and_padded_removals() -> None:
    assert pad(A, 0, 0) == BOTH
    listed = padded_removals(ARA)
    assert [(s, c.rel) for s, c in listed] == [(DState.of(1, [(0, 0), (0, 0)], [(0, 0)]), "r"), (DState.of(1, [(0, 0), (0, 0)], [(0, 0)]), "s")]
    outs = {result_of(perform(ARA, c)) for c in result_changes(ARA)}
    for padded, removal in listed:
        assert same(padded, ARA)
        assert result_of(perform(padded, removal)) in outs


def test_add_r_then_s_undoes() -> None:
    for g in (A, ARA, DState.of(2, [(0, 1)], [(1, 1)])):
        for x in range(g.n):
            for y in range(g.n):
                h = add_r_then_s(g, x, y)
                assert same(g, h) and h.size == g.size + 2


def test_removal_is_adding_the_other() -> None:
    assert same(perform(BOTH, Change(Kind.REMOVE, "r", 0, 0)), perform(A, Change(Kind.ADD_ASSERTION, "s", 0, 0)))


@pytest.mark.parametrize("state", [A, ARA, BOTH, DState.of(2, [(0, 1), (0, 1)], [(1, 0), (0, 0)])])
def test_every_change_moves_the_record_as_predicted(state: DState) -> None:
    p = plain(state)
    for change in result_changes(state):
        before, after = recorded(p), recorded(perform(p, change))
        move = (after[0] - before[0], after[1] + after[2] - before[1] - before[2])
        assert move == predicted_move(p, change)
