from __future__ import annotations

from math import factorial

import pytest

from fifth.explore import count_shortest_sequences as count_shortest_sequences_fifth
from fifth.explore import explore as explore_fifth
from sixth.changes import Change, Kind, attempt_counts, changes
from sixth.cost import cost, merged_optimal
from sixth.evidence import two_term_round_count
from sixth.explore import Exploration, attempt, count_shortest_sequences, cycle, explore, order, performed, sequences_exact
from sixth.orbits import layer_counts
from sixth.state import MState, canonical, given, names_one_term
from xry.state import Sameness

COMBOS = [(s, bra) for s in Sameness for bra in (False, True)]


def test_explore_needs_a_start_with_a_term_within_the_bound() -> None:
    with pytest.raises(ValueError):
        explore(MState(0, ()), 3)
    with pytest.raises(ValueError):
        explore(given(False, Sameness.FREE), 1)
    with pytest.raises(ValueError):
        explore(given(False, Sameness.FREE), 3, rounds=-1)
    none = explore(given(False, Sameness.FREE), 3, rounds=0)
    assert len(none.depth) == 1 and none.awaiting == [none.start] and none.last_new_round == 0
    loop = explore(MState.of(1, [(0, 0)]), 2, rounds=1)  # any well-formed state may start
    assert len(loop.depth) == 4


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_every_result_is_reached_at_its_cost(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 3, 5
    expl = explore(given(bra, sameness), bound, rounds)
    assert all(state.n >= 1 and canonical(state) == state for state in expl.depth)
    assert all(cost(state, bra) == r for state, r in expl.depth.items())
    assert expl.depth[expl.start] == 0
    assert sum(expl.new_per_round) == len(expl.depth)
    assert expl.last_new_round == rounds
    assert {s for s in expl.awaiting} == {s for s, r in expl.depth.items() if r == rounds}
    assert expl.awaiting == sorted(expl.awaiting, key=order)
    assert any(not state.legal for state in expl.depth)
    assert any(state.n == 1 and not state.legal for state in expl.depth)
    if sameness is Sameness.ANCHORED:
        assert any(state.names == (0, 0) for state in expl.depth)
        assert expl.depth[canonical(MState.of(1, [], (0, 0)))] == 2 + int(bra)
        assert expl.depth[canonical(MState.of(1, [(0, 0)] * (1 + int(bra)), (0, 0)))] == 1
    assert expl.new_per_round[: bound - 1] == layer_counts(sameness, bra, bound - 2)


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_the_results_asserting_no_xrx_are_the_fifth_derivations(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 3, 5
    ours = explore(given(bra, sameness), bound, rounds)
    theirs = explore_fifth(given(bra, sameness), bound, rounds)
    legal = {s: r for s, r in ours.depth.items() if s.legal}
    assert legal == theirs.depth
    sequences = count_shortest_sequences(ours)
    their_sequences = count_shortest_sequences_fifth(theirs)
    for s in legal:
        apart = (not names_one_term(s)) if s.names is not None else s.n >= 2
        if apart:
            assert sequences[s] == their_sequences[s], s.written()
        else:
            assert sequences[s] > their_sequences[s], s.written()
    assert len(ours.depth) > 3 * len(theirs.depth)


def test_two_terms_all_rounds() -> None:
    for bra in (False, True):
        rounds = 12
        expl = explore(given(bra, Sameness.ANCHORED), 2, rounds=rounds)
        assert expl.new_per_round == [two_term_round_count(bra, r) for r in range(rounds + 1)]
        assert expl.new_per_round[:8] == ([1, 7, 20, 41, 73, 120, 183, 264] if bra else [1, 6, 16, 32, 59, 98, 151, 220])
        assert len(expl.frontier) == sum(1 for s, r in expl.depth.items() if s.n == 2 and r < rounds)
        sequences = count_shortest_sequences(expl)
        for state, count in sequences.items():
            if state.n == 2 and not names_one_term(state):
                a, b = (0, 1)
                items = []
                for x, y, is_given in ((a, b, True), (b, a, bra)):
                    k = state.mult_of(x, y)
                    items.append(k - 1 if is_given and k >= 1 else (1 if is_given else k))
                items += [state.mult_of(a, a), state.mult_of(b, b)]
                expected = factorial(sum(items))
                for k in items:
                    expected //= factorial(k)
                assert count == expected, state.written()
            assert sequences_exact(expl, state, bra) == (state.n < 2 or state.names != (0, 0))
        assert sequences[canonical(MState.of(1, [], (0, 0)))] == (5 if bra else 2)  # remove the givens then identify; identify between; identify first then remove crc
        assert sequences[canonical(MState.of(1, [(0, 0)] * (1 + int(bra)), (0, 0)))] == 1
    free = explore(given(False, Sameness.FREE), 2, rounds=6)
    assert free.new_per_round[:4] == [1, 6, 11, 19]
    assert not sequences_exact(free, canonical(MState.of(2, [(0, 0)])), False)  # `c d; crc`: a merged placement is optimal
    assert sequences_exact(free, canonical(MState.of(2, [(0, 1)])), False)
    assert merged_optimal(MState.of(2, [(0, 0)]), False) and not merged_optimal(MState.of(2, [(0, 1)]), False)


def test_attempts_are_counted_round_by_round_and_logged() -> None:
    expl = explore(given(True, Sameness.FREE), 3, rounds=4, keep_log=True)
    assert expl.attempts_per_round[0] == 0 and expl.xrx_per_round[0] == 0
    assert expl.attempts_per_round[1] == len(changes(expl.start)) == 8
    assert expl.xrx_per_round[1] == 3
    assert expl.attempts_per_round == sorted(expl.attempts_per_round)
    assert len(expl.log) == expl.attempts_per_round[-1]
    tried = [s for s, r in expl.depth.items() if r < 4]
    assert expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s in tried)
    assert expl.xrx_per_round[-1] == sum(attempt_counts(s)[1] for s in tried)
    first = expl.log[0]
    assert first.change == Change(Kind.IDENTIFY, 0, 1) and first.xrx and first.outcome == canonical(MState.of(1, [(0, 0), (0, 0)]))
    beyond = [rec for rec in expl.log if rec.beyond]
    assert beyond and all(rec.change.kind is Kind.ADD_TERM for rec in beyond)
    assert all(rec.outcome is not None or rec.beyond for rec in expl.log)


def test_one_attempt() -> None:
    s = given(False, Sameness.ANCHORED)
    assert attempt(s, Change(Kind.ADD_TERM), 2).beyond
    ok = attempt(s, Change(Kind.REMOVE, 0, 1), 3)
    assert ok.outcome == canonical(MState.of(2, [], (0, 1))) and not ok.xrx and not ok.beyond
    loop = attempt(s, Change(Kind.ADD_ASSERTION, 1, 1), 3)
    assert loop.xrx and loop.outcome == canonical(MState.of(2, [(0, 1), (1, 1)], (0, 1)))
    merged = attempt(s, Change(Kind.IDENTIFY, 0, 1), 3)
    assert merged.xrx and merged.outcome == MState.of(1, [(0, 0)], (0, 0))


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_changes_move_the_round_by_an_odd_amount(sameness: Sameness, bra: bool) -> None:
    rounds = 5
    expl = explore(given(bra, sameness), 3, rounds)
    edges = list(performed(expl))
    steps = {expl.depth[out] - expl.depth[state] for state, _, out in edges}
    assert {-1, 1} <= steps <= {-5, -3, -1, 1}
    assert all(step % 2 == 1 for step in steps)
    if sameness is Sameness.ANCHORED:
        assert -3 in steps
    tried = [s for s, r in expl.depth.items() if r < rounds]
    assert len(edges) == sum(attempt_counts(s)[0] - int(s.n == 3) for s in tried)


def test_shortest_sequences_and_their_exactness() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, rounds=5)
    seqs = count_shortest_sequences(expl)
    assert seqs[expl.start] == 1
    assert seqs[canonical(MState.of(2, [(0, 1), (1, 0)], (0, 1)))] == 1
    assert seqs[canonical(MState.of(2, [(0, 1), (0, 0)], (0, 1)))] == 1  # add ara
    assert seqs[canonical(MState.of(1, [(0, 0)], (0, 0)))] == 1  # identify a and b
    assert seqs[canonical(MState.of(2, [], (0, 1)))] == 1  # remove arb
    assert seqs[canonical(MState.of(1, [], (0, 0)))] == 2  # remove arb, identify; or identify, remove ara
    assert seqs[canonical(MState.of(3, [], (0, 1)))] == 2
    assert seqs[canonical(MState.of(2, [], (0, 0)))] == 6  # the fifth's 3, and 3 more through `ara`
    assert all(count >= 1 for count in seqs.values())
    assert sequences_exact(expl, canonical(MState.of(2, [], (0, 0))), False)
    assert not sequences_exact(expl, canonical(MState.of(3, [], (0, 0))), False)
    assert sequences_exact(expl, canonical(MState.of(3, [], (0, 1))), False)
    free = explore(given(False, Sameness.FREE), 3, rounds=5)
    assert any(not sequences_exact(free, s, False) for s in free.depth if s.n == 3)
    assert all(sequences_exact(free, s, False) for s in free.depth if s.n < 3)


def test_sequence_count_refuses_a_change_that_raises_the_round_by_more_than_one() -> None:
    expl = explore(given(False, Sameness.FREE), 3, rounds=4)
    expl.depth[canonical(MState.of(3, [(0, 1)]))] = 3
    with pytest.raises(ValueError, match="more than one"):
        count_shortest_sequences(expl)
    short = explore(given(False, Sameness.FREE), 3, rounds=2)
    del short.depth[canonical(MState.of(3, [(0, 1)]))]
    with pytest.raises(ValueError, match="more than one"):
        count_shortest_sequences(short)


def test_every_result_has_a_two_change_cycle() -> None:
    assert cycle(MState(0, ())) is None
    expl = explore(given(False, Sameness.ANCHORED), 3, rounds=4)
    assert all(cycle(s) is not None for s in expl.depth)
    hollow = Exploration(
        start=expl.start, bound=3, rounds=4, depth={expl.start: 0}, new_per_round=[1],
        attempts_per_round=[0], xrx_per_round=[0],
    )  # fmt: skip
    assert hollow.awaiting == [] and hollow.frontier == [] and hollow.log == []


def test_bound_three_anchored_six_rounds() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, rounds=6)
    assert len(expl.depth) == 3001
    assert expl.new_per_round == [1, 7, 26, 86, 266, 742, 1873]
    assert all(cost(state, False) == r for state, r in expl.depth.items())
