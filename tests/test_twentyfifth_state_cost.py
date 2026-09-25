"""Filled triples, the states carrying them, the five kinds of change, balance and the cost (twenty-fifth seed)."""

from __future__ import annotations

import pytest

from ninth.changes import Change, Kind
from twentythird.state import DState, raise_term

from twentyfifth.cost import cost, cost23, record
from twentyfifth.state import (
    FState,
    Filling,
    align,
    balance_record,
    balances,
    canonical_state,
    carry,
    changes,
    embed,
    empty25,
    forget_marks,
    is_addition,
    nothing_with,
    oriented_triples,
    perform,
    plain_state,
    rename_triples,
    result_mark,
    rewrite25,
    swap25,
    unbalanced,
    way_round,
    written25,
)

THREE = DState(3, (0,) * 9, (0,) * 9)


def test_way_round_starts_from_the_least_term() -> None:
    assert way_round(0, 1, 2) == (0, 1, 2)
    assert way_round(1, 2, 0) == (0, 1, 2)
    assert way_round(2, 0, 1) == (0, 1, 2)
    assert way_round(0, 2, 1) == (0, 2, 1)
    assert way_round(2, 1, 0) == (0, 2, 1)
    assert oriented_triples(3) == ((0, 1, 2), (0, 2, 1))
    assert len(oriented_triples(5)) == 20 and list(oriented_triples(4)) == sorted(oriented_triples(4))


@pytest.mark.parametrize(
    ("state", "filled", "message"),
    [
        (DState(3, (0,) * 9, (0,) * 9, (0, 1)), (), "no names"),
        (THREE, ((0, 1, 3),), "three different terms"),
        (THREE, ((0, 0, 1),), "three different terms"),
        (THREE, ((1, 2, 0),), "least term"),
        (THREE, ((0, 2, 1), (0, 1, 2)), "once each"),
        (THREE, ((0, 1, 2), (0, 1, 2)), "once each"),
    ],
)
def test_a_state_refuses_what_is_not_one(state: DState, filled: tuple[tuple[int, int, int], ...], message: str) -> None:
    with pytest.raises(ValueError, match=message):
        FState(state, filled)


def test_writing_and_the_empty_beginning() -> None:
    assert empty25().n == 0 and written25(empty25()) == "no terms; asserted nothing"
    fs = FState(DState.of(3, [(0, 1)], []), ((0, 1, 2),))
    assert written25(fs).endswith("; filled abc")
    assert written25(embed(THREE)) == "terms a b c; asserted nothing"
    assert fs.key().endswith("|012")
    assert Filling(0, 2, 1).written(THREE) == "fill a c b"


def test_the_five_kinds_of_change() -> None:
    fs = embed(THREE)
    kinds = changes(fs)
    fills = [c for c in kinds if isinstance(c, Filling)]
    assert [(c.x, c.y, c.z) for c in fills] == [(0, 1, 2), (0, 2, 1)]
    first_fill = kinds.index(fills[0])
    term = next(i for i, c in enumerate(kinds) if isinstance(c, Change) and c.kind is Kind.ADD_TERM)
    assert all(isinstance(c, Change) and c.kind in (Kind.IDENTIFY, Kind.REMOVE) for c in kinds[:first_fill])
    assert first_fill < term
    one = perform(fs, Filling(1, 2, 0))
    assert one.filled == ((0, 1, 2),)
    assert len([c for c in changes(one) if isinstance(c, Filling)]) == 1
    with pytest.raises(ValueError, match="not a change"):
        perform(one, Filling(2, 0, 1))
    assert not is_addition(Filling(0, 1, 2))
    assert is_addition(Change(Kind.ADD_TERM, "", -1, -1)) and not is_addition(Change(Kind.IDENTIFY, "", 0, 1))
    grown = perform(one, Change(Kind.ADD_TERM, "", -1, -1))
    assert grown.n == 4 and grown.filled == ((0, 1, 2),)
    added = perform(one, Change(Kind.ADD_ASSERTION, "r", 0, 1))
    assert added.state.r[1] == 1 and added.filled == ((0, 1, 2),)


def test_identifying_carries_drops_and_merges_the_filled_triples() -> None:
    assert carry(3, [(0, 1, 2)], 0, 1) == ()
    assert carry(4, [(0, 1, 2), (0, 1, 3)], 2, 3) == ((0, 1, 2),)
    assert carry(4, [(0, 1, 3)], 0, 2) == ((0, 1, 2),)
    fs = FState(DState(4, (0,) * 16, (0,) * 16), ((0, 1, 2), (0, 1, 3)))
    out = perform(fs, Change(Kind.IDENTIFY, "", 2, 3))
    assert out.n == 3 and out.filled == ((0, 1, 2),)


def test_marks_writings_and_alignment() -> None:
    a = FState(THREE, ((0, 1, 2),))
    b = FState(THREE, ((0, 2, 1),))
    assert result_mark(a) == result_mark(b)
    assert canonical_state(a) == canonical_state(b) == canonical_state(a)
    assert rename_triples([(0, 1, 2)], (0, 2, 1)) == ((0, 2, 1),)
    moved = rewrite25(FState(DState.of(3, [(0, 1)], []), ((0, 1, 2),)), (1, 0, 2))
    assert moved.state.r[3] == 1 and moved.filled == ((0, 2, 1),)
    raised = FState(raise_term(DState.of(3, [(0, 1)], []), 1), ((0, 1, 2),))
    assert result_mark(raised) == result_mark(FState(DState.of(3, [(0, 1)], []), ((0, 1, 2),)))
    back = align(b, a)
    assert back.filled == a.filled
    with pytest.raises(ValueError, match="not one result"):
        align(a, embed(THREE))
    assert plain_state(FState(DState.of(3, [(0, 1)], [(0, 1)]), ())).state == THREE
    assert forget_marks() > 0


def test_balance_and_the_record() -> None:
    arc = DState.of(3, [(0, 1)], [(1, 0)])
    fs = FState(arc, ((0, 1, 2), (0, 2, 1)))
    assert not balances(fs, (0, 1, 2)) and not balances(fs, (0, 2, 1))
    assert unbalanced(fs) == ((0, 1, 2), (0, 2, 1))
    assert balance_record(nothing_with(fs)) == (((0, 1, 2), True), ((0, 2, 1), True))
    arb = FState(DState.of(3, [(0, 1)], []), ((0, 1, 2), (0, 2, 1)))
    assert balance_record(arb) == (((0, 1, 2), False), ((0, 2, 1), True))
    assert swap25(arb).state.s == arb.state.r and swap25(arb).filled == arb.filled
    assert balance_record(swap25(arb)) == balance_record(arb)


def test_cost_is_the_twentythird_cost_plus_the_filled_triples() -> None:
    fs = FState(THREE, ((0, 1, 2),))
    assert cost23(THREE) == 3 and cost(fs) == 4
    merged = perform(fs, Change(Kind.IDENTIFY, "", 0, 1))
    assert cost(merged) == 2
    assert record(FState(DState.of(3, [(0, 1)], [(1, 2)]), ())) == (3, 1, 1)
