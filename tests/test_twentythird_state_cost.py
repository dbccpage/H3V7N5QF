"""Raising, the results, the sums, the cost and the states asserting the fewest (twenty-third seed)."""

from __future__ import annotations

import random

import pytest

from twentythird.cost import (
    cost,
    cost_closed,
    descend,
    fewest,
    fewest_states,
    least_tables,
    lower_bound,
    masks,
    raise_set,
    record,
    search_box,
    search_fewest,
    set_moves_least,
    single_moves_least,
    table_weight,
    together_free_of_opposites,
)
from twentythird.state import (
    DState,
    align,
    around,
    canonical,
    excess_table,
    forget_keys,
    is_nothing,
    normal_table,
    nothing_certificate,
    nothing_key,
    plain_of,
    raise_term,
    raise_terms,
    result_key,
    rewrite,
    same,
    shifted,
    sum_profile,
    swap,
    total_excess,
    two_way,
)

TWO = DState(2, (0,) * 4, (0,) * 4)


def test_raising_moves_the_excess() -> None:
    raised = raise_term(TWO, 0)
    assert raised == DState.of(2, [(0, 1)], [(1, 0)])
    assert excess_table(raised) == (0, 1, -1, 0)
    three = raise_terms(DState(3, (0,) * 9, (0,) * 9), [2, 0, 1])
    assert excess_table(three) == shifted(3, (0,) * 9, [2, 0, 1])
    with pytest.raises(ValueError):
        raise_term(TWO, 2)
    with pytest.raises(ValueError):
        raise_terms(TWO, [1])
    with pytest.raises(ValueError):
        raise_terms(TWO, [-1, 0])


def test_the_same_result() -> None:
    raised = raise_term(TWO, 0)
    assert same(raised, TWO) and result_key(raised) == nothing_key(2)
    assert not same(DState.of(2, [(0, 1)], []), TWO)
    assert not same(TWO, DState(1, (0,), (0,)))
    # arb arb and arb bra: one result
    assert same(DState.of(2, [(0, 1), (0, 1)]), DState.of(2, [(0, 1), (1, 0)]))
    # a rewriting is the same result
    s = DState.of(3, [(0, 1), (2, 2)], [(1, 2)])
    assert same(s, rewrite(s, (2, 0, 1)))
    assert normal_table(0, ()) == ()
    assert forget_keys() > 0
    assert result_key(s) == result_key(rewrite(s, (1, 2, 0)))


def test_align() -> None:
    s = DState.of(2, [(0, 0), (0, 1)])
    t = raise_term(rewrite(s, (1, 0)), 0)
    a = align(t, s)
    assert normal_table(2, excess_table(a)) == normal_table(2, excess_table(s))
    with pytest.raises(ValueError):
        align(DState.of(2, [(0, 1)]), TWO)


def test_plain_of() -> None:
    assert plain_of(2, (1, -2, 0, 0)) == DState.of(2, [(0, 0)], [(0, 1), (0, 1)])
    with pytest.raises(ValueError):
        plain_of(2, (0,))


def test_nothing_certificate() -> None:
    assert nothing_certificate(TWO) is None and is_nothing(raise_term(TWO, 1))
    assert nothing_certificate(DState.of(1, [(0, 0)])) == ("loop", (0,), 1)
    assert nothing_certificate(DState.of(2, [(0, 1)])) == ("two-way", (0, 1), 1)
    three = DState.of(3, [(0, 1)], [(1, 0)])
    assert nothing_certificate(three) == ("around", (0, 1, 2), 1)
    t = excess_table(three)
    assert two_way(3, t, 0, 1) == 0 and around(3, t, 0, 2, 1) == -1
    assert total_excess(three) == 0
    assert sum_profile(three) == sum_profile(raise_term(three, 2))


def test_cost_and_closed_forms() -> None:
    rng = random.Random(3)
    for n in (1, 2, 3):
        for _ in range(60):
            table = tuple(rng.randint(-2, 2) for _ in range(n * n))
            s = plain_of(n, table)
            assert fewest(s) == search_fewest(s)
            assert cost(s) == cost_closed(s)
            assert lower_bound(s) <= cost(s)
    assert cost_closed(DState(4, (0,) * 16, (0,) * 16)) is None
    assert search_fewest(DState(0, (), ())) == 0
    tri = DState.of(3, [(0, 1), (0, 1), (1, 2), (1, 2), (2, 0), (2, 0)], [(1, 0), (2, 1), (0, 2)])
    assert (lower_bound(tri), cost(tri)) == (6, 12)
    assert search_box(2, (0, 3, -1, 0)) == 3


def test_record_and_masks() -> None:
    s = DState.of(2, [(0, 1), (0, 1)])
    assert record(s) == (2, 2, 0)
    assert record(raise_term(swap(s), 1)) == (2, 0, 2)
    assert list(masks(1)) == [] and list(masks(3)) == [1, 2, 3, 4, 5, 6]
    assert raise_set(2, (0,) * 4, 1) == (0, 1, -1, 0)


def test_states_asserting_the_fewest() -> None:
    s = DState.of(2, [(0, 1), (0, 1)])
    tables = least_tables(2, excess_table(s))
    assert tables == [(0, 0, 2, 0), (0, 1, 1, 0), (0, 2, 0, 0)]
    assert {canonical(f) for f in fewest_states(s)} == {canonical(s), canonical(DState.of(2, [(0, 1), (1, 0)]))}
    raised = excess_table(raise_term(TWO, 0))
    assert not set_moves_least(2, raised) and not together_free_of_opposites(2, raised)
    assert descend(2, raised) == (0,) * 4 and table_weight(raised) == 2


def test_single_terms_do_not_suffice_with_four() -> None:
    # 0r1 0r2 1s0 1s3 2s3: raising the set {0, 3} lowers it, no single term does
    w = DState.of(4, [(0, 1), (0, 2)], [(1, 0), (1, 3), (2, 3)])
    t = excess_table(w)
    assert single_moves_least(4, t) and not set_moves_least(4, t)
    assert fewest(w) == 3
    for n in (2, 3):
        rng = random.Random(n)
        for _ in range(40):
            table = tuple(rng.randint(-2, 2) for _ in range(n * n))
            assert single_moves_least(n, table) == set_moves_least(n, table)
