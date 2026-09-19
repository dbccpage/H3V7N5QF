from __future__ import annotations

from math import comb

import pytest

from fifth import explore as module
from fifth.changes import Answer, AnswerKind, Change, Kind, attempt_counts, changes
from fifth.cost import cost, lost
from fifth.explore import (
    Exploration,
    attempt,
    check_answers,
    count_shortest_sequences,
    cycle,
    explore,
    order,
    performed,
    removal_answers,
    sequences_exact,
)
from fifth.orbits import layer_counts
from fifth.state import MState, canonical, given
from fourth.explore import count_sequences as count_sequences_fourth
from fourth.explore import explore as explore_fourth
from xry.state import Sameness

COMBOS = [(s, bra) for s in Sameness for bra in (False, True)]


def test_explore_needs_a_legal_start_within_the_bound() -> None:
    with pytest.raises(ValueError):
        explore(MState.of(1, [(0, 0)]), 3)
    with pytest.raises(ValueError):
        explore(given(False, Sameness.FREE), 1)
    with pytest.raises(ValueError):
        explore(given(False, Sameness.FREE), 3, rounds=-1)
    none = explore(given(False, Sameness.FREE), 3, rounds=0)
    assert len(none.depth) == 1 and none.awaiting == [none.start] and none.last_new_round == 0


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_every_result_is_reached_at_its_cost(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 3, 6
    expl = explore(given(bra, sameness), bound, rounds)
    assert all(state.legal and state.n >= 1 and canonical(state) == state for state in expl.depth)
    assert all(cost(state, bra) == r for state, r in expl.depth.items())
    assert expl.depth[expl.start] == 0
    assert sum(expl.new_per_round) == len(expl.depth)
    assert expl.last_new_round == rounds
    assert {s for s in expl.awaiting} == {s for s, r in expl.depth.items() if r == rounds}
    assert expl.awaiting == sorted(expl.awaiting, key=order)
    assert any(state.n == 1 for state in expl.depth)
    assert any(state.m == 0 for state in expl.depth)
    if sameness is Sameness.ANCHORED:
        assert any(state.names == (0, 0) for state in expl.depth)
        assert expl.depth[canonical(MState.of(1, [], (0, 0)))] == 2 + int(bra)
    assert expl.new_per_round == layer_counts(sameness, bra, bound - 2)[: bound - 1] + expl.new_per_round[bound - 1 :]


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_the_results_containing_what_is_given_are_the_fourth_derivations(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 3, 6
    ours = explore(given(bra, sameness), bound, rounds)
    theirs = explore_fourth(given(bra, sameness), bound, rounds)
    size0 = 3 + int(bra)
    kept = {s: r for s, r in ours.depth.items() if r == s.size - size0}
    assert kept == theirs.depth
    sequences = count_shortest_sequences(ours)
    their_sequences = count_sequences_fourth(theirs)
    assert all(sequences[s] == their_sequences[s] for s in kept)
    assert len(ours.depth) > len(theirs.depth)


def test_two_terms_all_rounds() -> None:
    for bra in (False, True):
        expl = explore(given(bra, Sameness.ANCHORED), 2, rounds=30)
        head = [1, 4, 6, 7] if bra else [1, 3, 5]
        assert expl.new_per_round == head + [2 * r for r in range(len(head), 31)]
        assert len(expl.frontier) == sum(1 + 2 * 2 for s, r in expl.depth.items() if s.n == 2 and r < 30)
        sequences = count_shortest_sequences(expl)
        for state, count in sequences.items():
            if state.n == 2 and lost(state, bra) == 0:
                a, b = state.names if state.names is not None else (0, 1)
                i, j = state.mult_of(a, b) - 1, state.mult_of(b, a) - int(bra)
                assert count == comb(i + j, i)
            assert sequences_exact(expl, state) == (state.n < 2 or state.names != (0, 0))
        assert sequences[canonical(MState.of(2, [], (0, 1)))] == 1 + int(bra)  # remove arb, remove bra: either order
        assert sequences[canonical(MState.of(1, [], (0, 0)))] == 1 + int(bra)
    free = explore(given(False, Sameness.FREE), 2, rounds=30)
    assert free.new_per_round[:7] == [1, 3, 3, 3, 3, 4, 4]


def test_attempts_are_counted_round_by_round_and_logged() -> None:
    expl = explore(given(True, Sameness.FREE), 3, rounds=4, keep_log=True)
    assert expl.attempts_per_round[0] == 0
    assert expl.attempts_per_round[1] == len(changes(expl.start)) == 8
    assert expl.obstructed_per_round[1] == 3
    assert expl.attempts_per_round == sorted(expl.attempts_per_round)
    assert len(expl.log) == expl.attempts_per_round[-1]
    tried = [s for s, r in expl.depth.items() if r < 4]
    assert len(expl.log) == sum(len(changes(s)) for s in tried)
    assert expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s in tried)
    assert expl.obstructed_per_round[-1] == sum(attempt_counts(s)[1] for s in tried)
    first = expl.log[0]
    assert first.change == Change(Kind.IDENTIFY, 0, 1) and first.obstruction and first.outcome is None
    assert [a.kind for a in first.answers] == [AnswerKind.REFUSE, AnswerKind.REMOVE_OBSTRUCTION, AnswerKind.BUILD]
    beyond = [rec for rec in expl.log if rec.beyond]
    assert beyond and all(rec.change.kind is Kind.ADD_TERM for rec in beyond)
    assert removal_answers(expl) > 0


def test_one_attempt() -> None:
    s = given(False, Sameness.FREE)
    assert attempt(s, Change(Kind.ADD_TERM), 2).beyond
    ok = attempt(s, Change(Kind.REMOVE, 0, 1), 3)
    assert ok.outcome == canonical(MState.of(2, [])) and not ok.answers and not ok.beyond
    blocked = attempt(s, Change(Kind.IDENTIFY, 0, 1), 3)
    assert blocked.obstruction == ((0, 1),) and len(blocked.answers) == 3
    assert blocked.answers[1].result == MState.of(1, [])


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_answers_reach_nothing_new(sameness: Sameness, bra: bool) -> None:
    expl = explore(given(bra, sameness), 3, rounds=6)
    check = check_answers(expl)
    assert check.failures == ()
    assert check.obstructed > 0 and check.answers_within > 0 and check.answers_beyond > 0


def test_check_answers_reports_what_is_missing() -> None:
    start = canonical(given(False, Sameness.FREE))
    hollow = Exploration(
        start=start, bound=3, rounds=3, depth={start: 0}, new_per_round=[1],
        attempts_per_round=[0], obstructed_per_round=[0], frontier=[],
    )  # fmt: skip
    check = check_answers(hollow)
    assert check.failures and all("/" in f for f in check.failures)
    late = explore(start, 3, rounds=6)
    late.depth[canonical(MState.of(3, [(0, 1), (0, 2)]))] = 99
    assert any("build structure" in f for f in check_answers(late).failures)
    late.depth[canonical(MState.of(1, []))] = 99
    assert any("remove the obstruction" in f for f in check_answers(late).failures)


def test_removal_answers_are_counted(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(given(False, Sameness.FREE), 2, rounds=3)
    assert removal_answers(expl) == sum(
        1 for s in expl.depth for c in changes(s) if c.kind is Kind.IDENTIFY and s.related(c.x, c.y)
    )

    def fake(state: MState, change: Change) -> tuple[Answer, ...]:
        return (Answer(AnswerKind.REFUSE, (), False, state),)

    monkeypatch.setattr(module, "answers", fake)
    assert removal_answers(expl) == 0


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_changes_move_the_round_by_an_odd_amount(sameness: Sameness, bra: bool) -> None:
    rounds = 6
    expl = explore(given(bra, sameness), 3, rounds)
    edges = list(performed(expl))
    steps = {expl.depth[out] - expl.depth[state] for state, _, out in edges}
    assert {-1, 1} <= steps <= {-5, -3, -1, 1}
    assert all(step % 2 == 1 for step in steps)  # the cost changes by an odd amount: no change keeps the round
    if sameness is Sameness.ANCHORED:
        assert -3 in steps  # an identification that makes a given asserted again
    tried = [s for s, r in expl.depth.items() if r < rounds]
    assert len(edges) == sum(attempt_counts(s)[0] - attempt_counts(s)[1] - int(s.n == 3) for s in tried)


def test_shortest_sequences_and_their_exactness() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, rounds=6)
    seqs = count_shortest_sequences(expl)
    assert seqs[expl.start] == 1
    assert seqs[canonical(MState.of(2, [(0, 1), (1, 0)], (0, 1)))] == 1
    assert seqs[canonical(MState.of(2, [(0, 1), (0, 1), (1, 0)], (0, 1)))] == 2
    assert seqs[canonical(MState.of(3, [(0, 1), (1, 0)], (0, 1)))] == 2
    assert seqs[canonical(MState.of(2, [], (0, 1)))] == 1  # remove arb
    assert seqs[canonical(MState.of(3, [], (0, 1)))] == 2  # remove then add a term, or the reverse
    assert seqs[canonical(MState.of(1, [], (0, 0)))] == 1  # remove arb, identify
    assert seqs[canonical(MState.of(2, [], (0, 0)))] == 3  # a term before, between, or after
    assert all(count >= 1 for count in seqs.values())
    assert sequences_exact(expl, canonical(MState.of(2, [], (0, 0))))
    assert not sequences_exact(expl, canonical(MState.of(3, [], (0, 0))))
    assert sequences_exact(expl, canonical(MState.of(3, [], (0, 1))))
    free = explore(given(False, Sameness.FREE), 3, rounds=6)
    assert all(sequences_exact(free, s) for s in free.depth)


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
    one = cycle(MState.of(1, [], (0, 0)))
    assert one is not None and one[0].kind is Kind.ADD_TERM and one[1].kind is Kind.IDENTIFY
    two = cycle(given(True, Sameness.FREE))
    assert two is not None and two[0].kind is Kind.ADD_ASSERTION and two[1].kind is Kind.REMOVE
    expl = explore(given(False, Sameness.ANCHORED), 3, rounds=5)
    assert all(cycle(s) is not None for s in expl.depth)


def test_bound_four_anchored_eight_rounds() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 4, rounds=8)
    assert len(expl.depth) == 14061
    assert expl.new_per_round == [1, 4, 13, 40, 129, 400, 1195, 3370, 8909]
    assert all(cost(state, False) == r for state, r in expl.depth.items())
