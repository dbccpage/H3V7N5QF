from __future__ import annotations

import pytest

from seventh.changes import Change, Kind, attempt_counts, is_addition
from seventh.cost import cost
from seventh.explore import Exploration, attempt, count_shortest_sequences, cycle, explore, order, performed, sequences_exact
from seventh.orbits import layer_counts, two_term_round_count
from seventh.state import MState, canonical, empty


def test_explore_starts_from_the_empty_state_and_refuses_what_it_should() -> None:
    with pytest.raises(ValueError):
        explore(MState.of(2, [(0, 1)], (0, 1)), 3)
    with pytest.raises(ValueError):
        explore(MState.of(3, []), 2)
    with pytest.raises(ValueError):
        explore(empty(), 0)
    with pytest.raises(ValueError):
        explore(empty(), 3, rounds=-1)
    none = explore(empty(), 3, rounds=0)
    assert len(none.depth) == 1 and none.awaiting == [none.start] and none.last_new_round == 0
    one = explore(empty(), 3, rounds=1)
    assert one.new_per_round == [1, 1] and one.depth[MState.of(1, [])] == 1
    assert one.attempts_per_round == [0, 1] and one.xrx_per_round == [0, 0]
    later = explore(MState.of(1, [(0, 0)]), 2, rounds=1)  # any well-formed state without names may start
    assert len(later.depth) == 4


def test_every_result_is_reached_at_its_size_and_the_counts_are_the_closed_forms() -> None:
    bound, rounds = 3, 6
    expl = explore(empty(), bound, rounds)
    assert all(state.names is None and canonical(state) == state for state in expl.depth)
    assert all(cost(state) == r for state, r in expl.depth.items())
    assert expl.depth[expl.start] == 0 and expl.start == empty()
    assert sum(expl.new_per_round) == len(expl.depth) == 89
    assert expl.last_new_round == rounds
    assert {s for s in expl.awaiting} == {s for s, r in expl.depth.items() if r == rounds}
    assert expl.awaiting == sorted(expl.awaiting, key=order)
    assert any(not state.legal for state in expl.depth) and any(state.n == 1 and not state.legal for state in expl.depth)
    # A result of round r has at most r terms: rounds 0 .. N are complete within N terms.
    assert expl.new_per_round[: bound + 1] == layer_counts(bound)
    assert expl.new_per_round == [1, 1, 2, 4, 9, 21, 51]  # round 4 lacks the four-term empty state
    two = explore(empty(), 2, 8)
    assert two.new_per_round == [two_term_round_count(r) for r in range(9)]
    assert all(rec.change.kind is Kind.ADD_TERM for rec in two.frontier)
    assert {leave.state for leave in two.frontier} == {s for s, r in two.depth.items() if s.n == 2 and r < 8}


def test_the_log_records_every_attempt_and_the_first_change() -> None:
    expl = explore(empty(), 2, 2, keep_log=True)
    assert len(expl.log) == 1 + 2 and expl.log[0].change == Change(Kind.ADD_TERM) and expl.log[0].outcome == MState.of(1, [])
    assert expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s, r in expl.depth.items() if r < 2)
    rec = attempt(MState.of(2, []), Change(Kind.ADD_TERM), 2)
    assert rec.beyond and rec.outcome is None and not rec.xrx
    loop = attempt(MState.of(1, []), Change(Kind.ADD_ASSERTION, 0, 0), 2)
    assert loop.xrx and loop.outcome == MState.of(1, [(0, 0)])


def test_shortest_sequences_are_additions_only_and_exact() -> None:
    expl = explore(empty(), 3, 5)
    sequences = count_shortest_sequences(expl)
    assert sequences[expl.start] == 1 and sequences[MState.of(1, [])] == 1
    assert all(sequences[s] == 1 for s in expl.depth if s.n == 1)
    assert sequences[canonical(MState.of(2, [(0, 1)]))] == 2  # add arb, or add bra, on the two-term empty state
    assert sequences[canonical(MState.of(2, [(0, 1), (1, 0)]))] == 2
    assert all(sequences[s] >= 1 for s in expl.depth)
    assert all(sequences_exact(expl, s) for s in expl.depth)
    for state, change, out in performed(expl):
        assert expl.depth[out] <= expl.depth[state] + 1
        assert (expl.depth[out] == expl.depth[state] + 1) == is_addition(change)
    assert all(expl.depth[s] < 5 for s, _c, _o in performed(expl))


def test_count_shortest_sequences_checks_the_rounds() -> None:
    expl = explore(empty(), 2, 3)
    expl.depth[MState.of(1, [])] = 3  # the round of the one-term state is one, not three
    with pytest.raises(ValueError, match="more than one"):
        count_shortest_sequences(expl)
    expl = explore(empty(), 2, 3)
    two = canonical(MState.of(2, []))
    expl.depth[two] = 0
    expl.depth[MState.of(1, [])] = 1  # identify on the two-term state now "raises" the round: no addition
    with pytest.raises(ValueError, match="no addition"):
        count_shortest_sequences(expl)


def test_cycles_and_hollow_explorations() -> None:
    assert cycle(empty()) is None
    assert cycle(MState.of(1, [])) is not None and cycle(MState.of(2, [(0, 0)])) is not None
    hollow = Exploration(start=empty(), bound=2, rounds=3, depth={empty(): 0}, new_per_round=[1], attempts_per_round=[0], xrx_per_round=[0])
    assert hollow.awaiting == [] and hollow.last_new_round == 0
