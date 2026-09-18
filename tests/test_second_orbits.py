from __future__ import annotations

import pytest

from second.cost import contains_given
from second.explore import explore
from second.orbits import count_results, layer_counts
from xry.cost import has_two_way
from xry.state import Sameness, State, canonical, given

COMBOS = [(s, bra) for s in Sameness for bra in (False, True)]


def brute(sameness: Sameness, bra: bool, n: int) -> list[int]:
    """Count results by listing every writing and keeping the least ones."""
    out = [0] * (n * (n - 1) + 1)
    placements: list[tuple[int, int] | None] = [None]
    if sameness is Sameness.ANCHORED:
        placements = [(a, b) for a in range(n) for b in range(n)]
    for mask in range(1 << (n * n)):
        for names in placements:
            state = State(n, mask, names)
            if not state.legal or canonical(state) != state:
                continue
            if names is None:
                keep = has_two_way(state) if bra else state.m > 0
            else:
                keep = contains_given(state, bra)
            out[state.m] += keep
    return out


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
@pytest.mark.parametrize("n", [1, 2, 3])
def test_counts_agree_with_listing(sameness: Sameness, bra: bool, n: int) -> None:
    assert count_results(sameness, bra, n) == brute(sameness, bra, n)


def test_totals() -> None:
    assert [sum(count_results(Sameness.ANCHORED, False, n)) for n in range(1, 5)] == [0, 2, 32, 1056]
    assert [sum(count_results(Sameness.ANCHORED, True, n)) for n in range(1, 5)] == [0, 1, 16, 528]
    assert [sum(count_results(Sameness.FREE, False, n)) for n in range(1, 6)] == [0, 2, 15, 217, 9607]
    assert [sum(count_results(Sameness.FREE, True, n)) for n in range(1, 6)] == [0, 1, 9, 176, 9026]
    assert count_results(Sameness.FREE, False, 4, degree=2) == count_results(Sameness.FREE, False, 4)[:3]
    assert count_results(Sameness.ANCHORED, True, 3, degree=2) == [0, 0, 1]


def test_layer_counts_start_with_what_is_given() -> None:
    assert layer_counts(Sameness.ANCHORED, False, 2) == [1, 2, 6]
    assert layer_counts(Sameness.FREE, False, 2) == [1, 2, 5]
    assert layer_counts(Sameness.ANCHORED, True, 1) == [1, 1]
    assert layer_counts(Sameness.FREE, True, 0) == [1]


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_layer_counts_agree_with_an_exploration(sameness: Sameness, bra: bool) -> None:
    bound = 4
    expl = explore(given(bra, sameness), bound, rounds=bound)
    assert layer_counts(sameness, bra, bound - 2) == expl.new_per_round[: bound - 1]
