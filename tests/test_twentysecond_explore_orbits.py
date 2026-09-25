"""The exploration of results, the orbit counts and closed forms, reachability."""

from __future__ import annotations

from itertools import permutations, product

import pytest

from twentysecond.changes import Kind
from twentysecond.explore import count_shortest_sequences, explore, performed
from twentysecond.orbits import (
    all_pair_cycles,
    count_results,
    counts_within,
    layer_counts,
    one_term_count,
    two_term_count,
    two_term_count_by_parts,
    two_term_round_count,
)
from twentysecond.reach import reach_graph, reachable, reachable_in_graph
from twentysecond.state import DState, cost, empty


def test_explore_small() -> None:
    expl = explore(empty(), 2, 3, keep_log=True)
    assert expl.new_per_round == [1, 1, 3, 6]
    assert expl.last_new_round == 3
    assert all(cost(s) == r for s, r in expl.depth.items())
    assert len(expl.awaiting) == 6
    assert expl.frontier and all(e.change.kind is Kind.ADD_TERM and e.state.n == 2 for e in expl.frontier)
    assert expl.log and any(rec.beyond for rec in expl.log) and any(rec.outcome is not None for rec in expl.log)
    assert expl.attempts_per_round[1] == 1


def test_explore_rejects() -> None:
    with pytest.raises(ValueError):
        explore(DState.of(2, [], [], (0, 1)), 2, 1)
    with pytest.raises(ValueError):
        explore(DState.of(3, [], []), 2, 1)
    with pytest.raises(ValueError):
        explore(empty(), 0, 1)
    with pytest.raises(ValueError):
        explore(empty(), 1, -1)


def test_sequences_and_performed() -> None:
    expl = explore(empty(), 2, 5)
    seq = count_shortest_sequences(expl)
    assert seq[empty()] == 1
    assert all(seq[s] == 1 for s in expl.depth if s.n == 1)
    assert sum(1 for _ in performed(expl)) > 0
    assert max(seq.values()) > 1


def test_counts_against_listing() -> None:
    def brute(n: int, t: int) -> int:
        seen = set()
        for e in product(range(-t, t + 1), repeat=n * n):
            if sum(abs(v) for v in e) == t:
                seen.add(min(tuple(e[p[x] * n + p[y]] for x in range(n) for y in range(n)) for p in permutations(range(n))))
        return len(seen)

    assert count_results(2, 4) == [brute(2, t) for t in range(5)]
    assert count_results(3, 2) == [brute(3, t) for t in range(3)]
    assert count_results(0, 2) == [1, 0, 0]
    assert count_results(1, 3) == [1, 2, 2, 2]


def test_closed_forms() -> None:
    assert [two_term_count(t) for t in range(9)] == count_results(2, 8)
    assert all(two_term_count(t) == two_term_count_by_parts(t) for t in range(30))
    assert [two_term_round_count(r) for r in range(8)] == [1, 1, 3, 6, 20, 46, 102, 182]
    assert [one_term_count(t) for t in range(3)] == [1, 2, 2]
    assert layer_counts(5) == [1, 1, 3, 7, 25, 83]
    assert counts_within(1, 2) == {"0/0": 1, "1/0": 1, "1/1": 2}
    assert all_pair_cycles((2,)) == {2: 2} and all_pair_cycles((1, 1)) == {1: 4}


@pytest.mark.parametrize("fn", [one_term_count, two_term_count, two_term_count_by_parts, two_term_round_count])
def test_closed_forms_reject_negatives(fn: object) -> None:
    assert callable(fn)
    with pytest.raises(ValueError):
        fn(-1)


def test_count_rejects_negatives() -> None:
    with pytest.raises(ValueError):
        count_results(-1, 2)


def test_count_refuses_a_fraction(monkeypatch: pytest.MonkeyPatch) -> None:
    import twentysecond.orbits as orbits

    monkeypatch.setattr(orbits, "class_size", lambda _parts: 1)
    with pytest.raises(ArithmeticError):
        count_results(3, 0)


def test_reach() -> None:
    expl = explore(empty(), 2, 4)
    graph = reach_graph(expl)
    for s in expl.depth:
        found = reachable_in_graph(graph, s)
        for t in expl.depth:
            assert reachable(s, t) == (t in found)
