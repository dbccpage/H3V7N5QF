from __future__ import annotations

from math import factorial

import pytest

from xry.cost import has_two_way
from xry.orbits import (
    NAMED_KINDS,
    _averaged,
    class_size,
    count_free,
    count_named,
    count_one_way,
    count_states,
    expand,
    layer_counts,
    pair_cycles,
    partitions,
)
from xry.state import Sameness, State, canonical


def test_partitions_and_class_sizes() -> None:
    assert [len(list(partitions(n))) for n in range(7)] == [1, 1, 2, 3, 5, 7, 11]
    assert list(partitions(3)) == [(3,), (2, 1), (1, 1, 1)]
    for n in range(1, 7):
        assert sum(class_size(p) for p in partitions(n)) == factorial(n)
    assert class_size((2, 2, 1)) == 15


def test_pair_cycles_cover_every_pair() -> None:
    for n in range(1, 7):
        for parts in partitions(n):
            both = pair_cycles(parts, False)
            assert sum(length * count for length, count in both.items()) == n * (n - 1)
    assert pair_cycles((2,), True) == {}  # the one pair is turned around
    assert pair_cycles((3,), True) == {3: 1}
    assert pair_cycles((2, 1), True) == {2: 1}


def test_expand() -> None:
    assert expand({}, 1, 3) == [1, 0, 0, 0]
    assert expand({1: 2}, 1, 3) == [1, 2, 1, 0]
    assert expand({2: 2}, 2, 5) == [1, 0, 4, 0, 4, 0]
    assert expand({1: 3, 2: 1}, 1, 2) == [1, 3, 4]
    assert expand({1: 0}, 1, 1) == [1, 0]


def test_totals() -> None:
    assert [sum(count_free(n)) for n in range(1, 6)] == [1, 3, 16, 218, 9608]
    assert [sum(count_one_way(n)) for n in range(1, 6)] == [1, 2, 7, 42, 582]
    assert [sum(count_states(Sameness.ANCHORED, n)) for n in range(1, 5)] == [1, 8, 100, 2864]
    assert count_states(Sameness.FREE, 3) == count_free(3) == [1, 1, 4, 4, 4, 1, 1]
    assert count_free(4, degree=3) == count_free(4)[:4]
    with pytest.raises(ArithmeticError):
        _averaged([1], 2)


def brute(n: int, named: bool) -> dict[tuple[str, int], int]:
    """Count states by listing every writing and keeping the least ones."""
    out: dict[tuple[str, int], int] = {}
    placements: list[tuple[int, int] | None] = [None]
    if named:
        placements = [(a, b) for a in range(n) for b in range(n)]
    for mask in range(1 << (n * n)):
        for names in placements:
            state = State(n, mask, names)
            if not state.legal or canonical(state) != state:
                continue
            if names is None:
                kind = "one way" if not has_two_way(state) else "some both ways"
            elif names[0] == names[1]:
                kind = NAMED_KINDS[0]
            else:
                ab, ba = state.has(*names), state.has(names[1], names[0])
                kind = NAMED_KINDS[1 + ab + 2 * ba]
            out[kind, state.m] = out.get((kind, state.m), 0) + 1
    return out


@pytest.mark.parametrize("n", [1, 2, 3])
def test_counts_agree_with_listing(n: int) -> None:
    free = brute(n, named=False)
    one_way = count_one_way(n)
    every = count_free(n)
    for m in range(n * (n - 1) + 1):
        assert free.get(("one way", m), 0) == one_way[m]
        assert free.get(("some both ways", m), 0) == every[m] - one_way[m]
    named = brute(n, named=True)
    counted = count_named(n)
    for kind in NAMED_KINDS:
        for m in range(n * (n - 1) + 1):
            assert named.get((kind, m), 0) == counted[kind][m]


def test_layer_counts_start_with_what_is_given() -> None:
    assert layer_counts(Sameness.FREE, False, 3) == [1, 3, 7, 11]
    assert layer_counts(Sameness.FREE, True, 3) == [1, 2, 5, 14]
    assert layer_counts(Sameness.ANCHORED, False, 3) == [1, 3, 9, 24]
    assert layer_counts(Sameness.ANCHORED, True, 3) == [1, 3, 8, 24]
    assert layer_counts(Sameness.FREE, False, 0) == [1]
