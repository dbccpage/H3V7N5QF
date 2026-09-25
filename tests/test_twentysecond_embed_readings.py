"""The seventh's states in, the map back, the ninth's merged, the unchosen readings, the statements."""

from __future__ import annotations

from seventh.explore import explore as explore_seventh
from seventh.state import empty as empty_seventh
from twentysecond.embed import embed, ninth_image, read_back, smallest_none
from twentysecond.explore import explore
from twentysecond.follows import verdicts
from twentysecond.readings import (
    cost_j2,
    cost_j3,
    count_j3,
    explore_j2,
    explore_j3,
    key_j2,
    padding_witness,
    reduce_j3,
    rep_j2,
    round_count_j2,
)
from twentysecond.state import DState, MState, empty, same


def test_embed_and_read_back() -> None:
    seventh = explore_seventh(empty_seventh(), 2, 4)
    images = {embed(m) for m in seventh.depth}
    assert len(images) == len(seventh.depth)
    assert all(read_back(embed(m)) == m for m in seventh.depth)
    assert read_back(DState.of(1, [], [(0, 0)])) is None
    assert read_back(DState.of(1, [(0, 0)], [(0, 0)])) == MState(1, (0,), None)


def test_smallest_none() -> None:
    assert smallest_none(explore(empty(), 2, 3)) == DState.of(1, [], [(0, 0)])
    assert smallest_none(explore(empty(), 2, 1)) is None


def test_ninth_image() -> None:
    assert ninth_image(DState.of(1, [(0, 0)], [(0, 0)])) == DState.of(1, [], [])


def test_reading_j2() -> None:
    assert key_j2(DState.of(2, [(0, 1)], [(1, 0), (1, 1)])) == (2, -1)
    assert rep_j2(0, 0) == DState(0, (), ())
    assert key_j2(rep_j2(2, -3)) == (2, -3) and key_j2(rep_j2(1, 2)) == (1, 2)
    depth = explore_j2(2, 5)
    assert all(cost_j2(k) == r for k, r in depth.items())
    assert [sum(1 for r in depth.values() if r == k) for k in range(6)] == [round_count_j2(k, 2) for k in range(6)]


def test_reading_j3() -> None:
    g = DState.of(2, [(0, 1), (0, 0)], [(0, 1), (0, 0)])
    assert reduce_j3(g) == DState.of(2, [(0, 0)], [(0, 0)]) and cost_j3(g) == 4
    depth = explore_j3(2, 5)
    assert all(cost_j3(s) == r for s, r in depth.items())
    explored: dict[tuple[int, int], int] = {}
    for s in depth:
        key = (s.n, cost_j3(s) - s.n)
        explored[key] = explored.get(key, 0) + 1
    assert explored == {(n, t): c for n in range(3) for t, c in enumerate(count_j3(n, 5 - n)) if c}
    padded, result, c = padding_witness(2)
    assert same(padded, DState.of(2, [], [])) and result == DState.of(1, [(0, 0)] * 2, [(0, 0)] * 2) and c == 5


def test_verdicts_on_plain_states() -> None:
    found = {v.statement: v for v in verdicts(explore(empty(), 2, 4))}
    both = found["some_pair_in_both"]
    assert both.in_no_result and not both.independent and not both.in_every_result
    assert found["nothing_at_all"].independent
