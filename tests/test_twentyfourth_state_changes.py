"""States with filled terms, their marks and balance, the five changes, the cost and the counts."""

from __future__ import annotations

import pytest

from ninth.changes import Change, Kind
from twentyfourth.changes import (
    CHOSEN,
    FILL_BALANCE,
    FILL_COUNT,
    FILL_LOOPS,
    ID_BOTH,
    ID_NEVER,
    Fill,
    Reading,
    is_raising,
    kind_of,
    moves,
    perform24,
    written,
)
from twentyfourth.cost import cost, cost_counted, potential
from twentyfourth.orbits import (
    counts_within,
    layer_counts,
    listing_counts,
    one_term_count,
    one_term_sequences,
    three_term_counts,
    two_term_count,
    two_term_count_by_points,
    two_term_round_count,
)
from twentyfourth.state import (
    DState,
    FState,
    balance_record,
    balances,
    canonical,
    empty,
    forget,
    forget_caches,
    keeping_size,
    keeping_terms,
    key_balance,
    of_state,
    plain,
    result_key,
    rewrite,
    same,
    state_of,
    swap,
    tell_class,
    told,
    unbalanced_filled,
)


def f(n: int, r: list[tuple[int, int]], s: list[tuple[int, int]], fills: tuple[int, ...]) -> FState:
    return FState(DState.of(n, r, s), fills)


def test_state_basics() -> None:
    e = empty()
    assert e.n == 0 and e.filled == () and e.written() == "no terms; asserted nothing"
    a = f(2, [(0, 0)], [(1, 0)], (1, 0))
    assert a.filled == (0,) and a.filled_count == 1 and a.fillings == 1
    assert a.written().endswith("filled a") and "|f10" in a.key()
    assert f(1, [], [], (0,)).written().endswith("filled none")
    assert f(1, [], [], (2,)).written().endswith("filled a(2)")
    assert forget(a) == a.base and of_state(a.base).fills == (0, 0)
    with pytest.raises(ValueError):
        FState(DState(1, (0,), (0,), (0, 0)), (0,))
    with pytest.raises(ValueError):
        FState(DState(1, (0,), (0,)), (0, 0))
    with pytest.raises(ValueError):
        FState(DState(1, (0,), (0,)), (-1,))


def test_rewrite_canonical_plain_swap() -> None:
    a = f(2, [(0, 1)], [(0, 1), (1, 1)], (0, 1))
    assert plain(a).base.total_r == 0 and plain(a).fills == a.fills
    b = rewrite(a, (1, 0))
    assert b.fills == (1, 0) and b.base.s[0] == 1
    assert canonical(a) == canonical(b)
    assert state_of(a) == canonical(plain(a))
    assert swap(swap(a)) == a and swap(a).fills == a.fills
    with pytest.raises(ValueError):
        rewrite(a, (0, 0))
    assert forget_caches() > 0
    assert canonical(a) == canonical(b)


def test_marks_and_sameness() -> None:
    # `a b` raised at `a` is the result asserting nothing on two terms, with the same filled terms
    raised = f(2, [(0, 1)], [(1, 0)], (1, 0))
    nothing = f(2, [], [], (0, 1))
    assert same(raised, nothing)
    assert not same(raised, f(2, [], [], (0, 0)))
    assert not same(raised, f(1, [], [], (1,)))
    assert result_key(raised) == (2, (0, 0, 0, 0), (0, 1))


def test_balance_and_tell_classes() -> None:
    told_one = f(1, [(0, 0)], [], (1,))
    assert not balances(told_one, 0) and unbalanced_filled(told_one) == (0,) and told(told_one)
    assert balance_record(told_one) == (0, 1) and tell_class(told_one) == "told"
    assert key_balance(result_key(told_one)) == ((0, False),)
    away = f(2, [(1, 1)], [], (1, 0))
    assert balances(away, 0) and not balances(away, 1) and tell_class(away) == "one filling away"
    assert tell_class(f(2, [(0, 1)], [], (1, 1))) == "two terms"
    assert tell_class(f(3, [(0, 1)], [(1, 0)], (1, 1, 1))) == "three terms"
    assert tell_class(f(2, [(0, 1)], [(1, 0)], (1, 1))) == "nothing"


def test_keeping() -> None:
    assert keeping_size(DState.of(2, [])) == 0 and keeping_terms(DState.of(2, [])) == 0
    assert keeping_size(DState.of(2, [(0, 0)])) == 1 and keeping_terms(DState.of(2, [(0, 0)])) == 1
    assert keeping_size(DState.of(2, [(0, 1)])) == 2 and keeping_terms(DState.of(2, [(0, 1)])) == 2
    three = DState.of(3, [(0, 1)], [(1, 0)])
    assert keeping_size(three) == 3 and keeping_terms(three) == 3
    # a loop at `a` (so no pair or triple through `a` is smallest), and a two-way sum at `b c`
    assert keeping_terms(DState.of(3, [(0, 0), (0, 1)], [(1, 2)])) == 3
    # two terms with a two-way sum make every triple through them not smallest
    assert keeping_terms(DState.of(3, [(0, 1)])) == 2


def test_moves_and_perform() -> None:
    s = f(2, [(0, 1)], [], (1, 0))
    ms = moves(s)
    kinds = [kind_of(m) for m in ms]
    assert kinds[0] == "identify two terms" and "fill one term" in kinds and kinds[-1] == "add an assertion"
    assert Fill(0) not in ms and Fill(1) in ms
    assert Fill(0) in moves(s, Reading(fill=FILL_COUNT))
    assert written(Fill(1), s) == "fill b" and written(Change(Kind.ADD_TERM), s) == "add a term"
    assert is_raising(Fill(0)) and is_raising(Change(Kind.ADD_TERM)) and not is_raising(Change(Kind.IDENTIFY, "", 0, 1))
    assert perform24(s, Fill(1)).fills == (1, 1)
    assert perform24(s, Change(Kind.ADD_TERM)).fills == (1, 0, 0)
    assert perform24(s, Change(Kind.ADD_ASSERTION, "s", 1, 1)).fills == (1, 0)
    with pytest.raises(ValueError):
        perform24(s, Fill(0))
    with pytest.raises(ValueError):
        perform24(s, Fill(5))


def test_identifying_readings() -> None:
    both = f(3, [], [], (1, 1, 0))
    one = f(3, [], [], (1, 0, 0))
    ident = Change(Kind.IDENTIFY, "", 0, 1)
    assert perform24(both, ident).fills == (1, 0)
    assert perform24(one, ident).fills == (1, 0)
    assert perform24(one, ident, Reading(identify=ID_BOTH)).fills == (0, 0)
    assert perform24(both, ident, Reading(identify=ID_BOTH)).fills == (1, 0)
    assert perform24(both, ident, Reading(identify=ID_NEVER)).fills == (0, 0)
    counted = FState(both.base, (2, 1, 0))
    assert perform24(counted, ident, Reading(fill=FILL_COUNT)).fills == (3, 0)
    with pytest.raises(ValueError):
        Reading(fill="other")
    with pytest.raises(ValueError):
        Reading(identify="other")
    assert CHOSEN.tag == "fill-mark_identify-either"


def test_filling_readings() -> None:
    s = f(1, [(0, 0), (0, 0)], [], (0,))
    loops = perform24(s, Fill(0), Reading(fill=FILL_LOOPS))
    assert loops.base.r == (3,) and loops.base.s == (1,) and same(loops, perform24(s, Fill(0)))
    bal = perform24(s, Fill(0), Reading(fill=FILL_BALANCE))
    assert bal.base.r == (2,) and bal.base.s == (2,) and not told(bal)
    twice = perform24(perform24(s, Fill(0), Reading(fill=FILL_COUNT)), Fill(0), Reading(fill=FILL_COUNT))
    assert twice.fills == (2,) and twice.fillings == 2 and twice.filled_count == 1


def test_cost() -> None:
    assert cost(empty()) == 0
    assert cost(f(1, [], [], (1,))) == 2
    assert cost(f(2, [], [], (1, 1))) == 4
    assert cost(f(2, [(0, 1)], [(1, 0)], (1, 0))) == 3
    assert potential(f(2, [(0, 1)], [(1, 0)], (1, 0))) == 5
    assert cost_counted(FState(DState.of(1, []), (2,))) == 3


def test_counts() -> None:
    assert [one_term_count(k, t) for k in (0, 1) for t in (0, 1, 2)] == [1, 2, 2, 1, 2, 2]
    assert [one_term_sequences(1, t) for t in (0, 1, 2)] == [1, 2, 3] and one_term_sequences(0, 4) == 1
    for k in (0, 1, 2):
        for t in range(5):
            assert two_term_count(k, t) == two_term_count_by_points(k, t)
    assert [two_term_round_count(r) for r in range(8)] == [1, 1, 4, 9, 22, 48, 90, 148]
    for bad in ((2, -1), (-1, 0)):
        with pytest.raises(ValueError):
            one_term_count(*bad)
        with pytest.raises(ValueError):
            one_term_sequences(*bad)
    with pytest.raises(ValueError):
        two_term_count(3, 0)
    with pytest.raises(ValueError):
        two_term_round_count(-1)
    three = three_term_counts(4)
    assert three[(0, 0)] == 1 and three[(1, 0)] == 1 and three[(3, 0)] == 1
    assert dict(listing_counts(3, 3)) == three_term_counts(3)
    within = counts_within(2, 3)
    assert within == {"0/0/0": 1, "1/0/0": 1, "1/0/1": 2, "1/0/2": 2, "1/1/0": 1, "1/1/1": 2, "2/0/0": 1, "2/0/1": 4, "2/1/0": 1}
    assert counts_within(4, 5)["4/1/0"] == 1
    assert layer_counts(4) == [1, 1, 4, 10, 28]
