from __future__ import annotations

import pytest

from ninth.changes import Change, Kind, attempt_counts, is_addition
from ninth.cost import cost
from ninth.explore import Exploration, attempt, count_shortest_sequences, cycle, explore, order, performed, sequences_exact
from ninth.orbits import layer_counts, one_term_sequences, two_term_round_count
from ninth.state import DState, canonical, empty


def test_explore_starts_from_the_empty_state_and_refuses_what_it_should() -> None:
    with pytest.raises(ValueError):
        explore(DState.of(2, [(0, 1)], [], (0, 1)), 3)
    with pytest.raises(ValueError):
        explore(DState.of(3, [], []), 2)
    with pytest.raises(ValueError):
        explore(empty(), 0)
    with pytest.raises(ValueError):
        explore(empty(), 3, rounds=-1)
    none = explore(empty(), 3, rounds=0)
    assert len(none.depth) == 1 and none.awaiting == [none.start] and none.last_new_round == 0
    one = explore(empty(), 3, rounds=1)
    assert one.new_per_round == [1, 1] and one.depth[DState.of(1, [], [])] == 1
    assert one.attempts_per_round == [0, 1] and one.xrx_per_round == [0, 0] and one.xsx_per_round == [0, 0]
    later = explore(DState.of(1, [(0, 0)], []), 2, rounds=1)
    assert len(later.depth) >= 2


def test_every_result_is_reached_at_its_size_and_the_counts_are_the_closed_forms() -> None:
    bound, rounds = 3, 6
    expl = explore(empty(), bound, rounds)
    assert all(state.names is None and canonical(state) == state for state in expl.depth)
    assert all(cost(state) == r for state, r in expl.depth.items())
    assert expl.depth[expl.start] == 0 and expl.start == empty()
    assert sum(expl.new_per_round) == len(expl.depth) == 518
    assert expl.last_new_round == rounds
    assert {s for s in expl.awaiting} == {s for s, r in expl.depth.items() if r == rounds}
    assert expl.awaiting == sorted(expl.awaiting, key=order)
    assert any(not state.legal_r for state in expl.depth) and any(not state.legal_s for state in expl.depth)
    assert expl.new_per_round[: bound + 1] == layer_counts(bound)
    assert expl.new_per_round == [1, 1, 3, 8, 28, 99, 378]
    two = explore(empty(), 2, 8)
    assert two.new_per_round == [two_term_round_count(r) for r in range(9)]
    assert all(rec.change.kind is Kind.ADD_TERM for rec in two.frontier)
    assert {leave.state for leave in two.frontier} == {s for s, r in two.depth.items() if s.n == 2 and r < 8}


def test_the_log_records_every_attempt_and_the_first_change() -> None:
    expl = explore(empty(), 2, 2, keep_log=True)
    assert expl.log[0].change == Change(Kind.ADD_TERM) and expl.log[0].outcome == DState.of(1, [], [])
    assert expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s, r in expl.depth.items() if r < 2)
    rec = attempt(DState.of(2, [], []), Change(Kind.ADD_TERM), 2)
    assert rec.beyond and rec.outcome is None and not rec.xrx and not rec.xsx
    loop = attempt(DState.of(1, [], []), Change(Kind.ADD_ASSERTION, "r", 0, 0), 2)
    assert loop.xrx and not loop.xsx and loop.outcome == DState.of(1, [(0, 0)], [])
    loop_s = attempt(DState.of(1, [], []), Change(Kind.ADD_ASSERTION, "s", 0, 0), 2)
    assert loop_s.xsx and not loop_s.xrx


def test_shortest_sequences_are_additions_only_and_exact() -> None:
    expl = explore(empty(), 3, 5)
    sequences = count_shortest_sequences(expl)
    assert sequences[expl.start] == 1 and sequences[DState.of(1, [], [])] == 1
    ara = DState.of(1, [(0, 0)], [])
    asa = DState.of(1, [], [(0, 0)])
    both = DState.of(1, [(0, 0)], [(0, 0)])
    assert sequences[ara] == sequences[asa] == 1
    assert sequences[both] == one_term_sequences(1, 1) == 2
    assert all(sequences[s] == one_term_sequences(s.r[0], s.s[0]) for s in expl.depth if s.n == 1)
    assert all(sequences[s] >= 1 for s in expl.depth)
    assert all(sequences_exact(expl, s) for s in expl.depth)
    assert not sequences_exact(expl, DState.of(expl.bound + 1, [], []))
    for state, change, out in performed(expl):
        assert expl.depth[out] <= expl.depth[state] + 1
        assert (expl.depth[out] == expl.depth[state] + 1) == is_addition(change)
    assert all(expl.depth[s] < 5 for s, _c, _o in performed(expl))


def test_count_shortest_sequences_checks_the_rounds() -> None:
    expl = explore(empty(), 2, 3)
    expl.depth[DState.of(1, [], [])] = 3
    with pytest.raises(ValueError, match="more than one"):
        count_shortest_sequences(expl)
    expl = explore(empty(), 2, 3)
    two = canonical(DState.of(2, [], []))
    expl.depth[two] = 0
    expl.depth[DState.of(1, [], [])] = 1
    with pytest.raises(ValueError, match="no addition"):
        count_shortest_sequences(expl)


def test_cycles_and_hollow_explorations() -> None:
    assert cycle(empty()) is None
    assert cycle(DState.of(1, [], [])) is not None and cycle(DState.of(2, [(0, 0)], [])) is not None
    hollow = Exploration(
        start=empty(),
        bound=2,
        rounds=3,
        depth={empty(): 0},
        new_per_round=[1],
        attempts_per_round=[0],
        xrx_per_round=[0],
        xsx_per_round=[0],
    )
    assert hollow.awaiting == [] and hollow.last_new_round == 0
