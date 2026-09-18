from __future__ import annotations

from math import comb

import pytest

from fourth import explore as module
from fourth.changes import Answer, AnswerKind, Change, Kind, attempt_counts, changes
from fourth.cost import contains_given, cost
from fourth.explore import (
    Exploration,
    attempt,
    check_answers,
    count_sequences,
    explore,
    order,
    performed,
    removal_answers,
)
from fourth.orbits import counts_upto, layer_counts
from fourth.state import MState, canonical, given, support
from third.explore import count_sequences as count_sequences_third
from third.explore import explore as explore_third
from xry.state import Sameness
from xry.state import canonical as canonical_support
from xry.state import given as given_third

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
def test_everything_within_the_bound_is_reached_at_its_cost(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 3, 7
    expl = explore(given(bra, sameness), bound, rounds)
    size0 = 3 + int(bra)
    for n in range(1, bound + 1):
        exact = counts_upto(sameness, bra, n, size0 + rounds - n)
        for t, count in enumerate(exact):
            if n + t - size0 <= rounds:
                assert sum(1 for s in expl.depth if s.n == n and s.m == t) == count
    assert all(state.legal and canonical(state) == state for state in expl.depth)
    assert all(cost(state, bra) == r for state, r in expl.depth.items())
    assert all(r == state.size - size0 for state, r in expl.depth.items())
    if sameness is Sameness.ANCHORED:
        assert all(contains_given(state, bra) for state in expl.depth)
    assert all(state.n >= 2 and state.m >= 1 for state in expl.depth)
    assert expl.depth[expl.start] == 0
    assert sum(expl.new_per_round) == len(expl.depth)
    assert expl.last_new_round == rounds
    assert {s for s in expl.awaiting} == {s for s, r in expl.depth.items() if r == rounds}
    assert expl.awaiting == sorted(expl.awaiting, key=order)


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_the_results_asserting_nothing_twice_are_the_third_derivations(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 3, 7
    ours = explore(given(bra, sameness), bound, rounds)
    theirs = explore_third(given_third(bra, sameness), bound, rounds)
    simple = {canonical_support(support(s)): r for s, r in ours.depth.items() if s.simple}
    assert simple == theirs.depth
    sequences = count_sequences(ours)
    their_sequences = count_sequences_third(theirs)
    assert all(sequences[s] == their_sequences[canonical_support(support(s))] for s in ours.depth if s.simple)
    assert ours.attempts_per_round[1] == theirs.attempts_per_round[1] + ours.start.distinct
    assert len(ours.depth) > len(theirs.depth)


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_early_rounds_agree_with_the_count_without_bound(sameness: Sameness, bra: bool) -> None:
    bound = 4
    expl = explore(given(bra, sameness), bound, rounds=bound)
    exact = layer_counts(sameness, bra, bound)
    assert expl.new_per_round[: bound - 1] == exact[: bound - 1]
    assert expl.new_per_round[bound - 1] < exact[bound - 1]


def test_the_frontier_is_exactly_the_attempts_that_leave_the_bound_on_terms() -> None:
    bound, rounds = 3, 5
    expl = explore(given(False, Sameness.ANCHORED), bound, rounds)
    full = [s for s, r in expl.depth.items() if s.n == bound and r < rounds]
    assert {leave.state for leave in expl.frontier} == set(full)
    assert len(expl.frontier) == len(full) * (1 + 2 * bound)
    by_change = [leave for leave in expl.frontier if leave.by == "the change"]
    assert all(leave.change.kind is Kind.ADD_TERM for leave in by_change)
    assert len(by_change) == len(full)


def test_two_terms_all_rounds() -> None:
    for bra in (False, True):
        expl = explore(given(bra, Sameness.ANCHORED), 2, rounds=100)
        assert expl.new_per_round == [r + 1 for r in range(101)] and len(expl.depth) == 5151
        assert expl.attempts_per_round[-1] == 5 * (5151 - 101)
        assert expl.obstructed_per_round[-1] == 2 * (5151 - 101)
        assert len(expl.frontier) == 5 * (5151 - 101)
        sequences = count_sequences(expl)
        for state, count in sequences.items():
            a, b = state.names if state.names is not None else (0, 1)
            i, j = state.mult_of(a, b) - 1, state.mult_of(b, a) - int(bra)
            assert count == comb(i + j, i)
        assert sum(sequences.values()) == 2**101 - 1
    free = explore(given(False, Sameness.FREE), 2, rounds=100)
    assert free.new_per_round == [(r + 1) // 2 + 1 for r in range(101)]
    free_bra = explore(given(True, Sameness.FREE), 2, rounds=100)
    assert free_bra.new_per_round == [r // 2 + 1 for r in range(101)]


def test_attempts_are_counted_round_by_round_and_logged() -> None:
    expl = explore(given(True, Sameness.FREE), 3, rounds=4, keep_log=True)
    assert expl.attempts_per_round[0] == 0
    assert expl.attempts_per_round[1] == len(changes(expl.start)) == 5
    assert expl.obstructed_per_round[1] == 2
    assert expl.attempts_per_round == sorted(expl.attempts_per_round)
    assert len(expl.log) == expl.attempts_per_round[-1]
    tried = [s for s, r in expl.depth.items() if r < 4]
    assert len(expl.log) == sum(len(changes(s)) for s in tried)
    assert expl.attempts_per_round[-1] == sum(attempt_counts(s)[0] for s in tried)
    assert expl.obstructed_per_round[-1] == sum(attempt_counts(s)[1] for s in tried)
    first = expl.log[0]
    assert first.change == Change(Kind.ADD_TERM) and first.outcome is not None
    blocked = next(rec for rec in expl.log if rec.obstruction)
    assert [a.kind for a in blocked.answers] == [AnswerKind.REFUSE, AnswerKind.BUILD, AnswerKind.BUILD]
    beyond = [rec for rec in expl.log if rec.beyond]
    assert beyond and all(rec.change.kind is Kind.ADD_TERM for rec in beyond)


def test_one_attempt() -> None:
    s = given(False, Sameness.FREE)
    assert attempt(s, Change(Kind.ADD_TERM), 2).beyond
    ok = attempt(s, Change(Kind.ADD_TERM), 3)
    assert ok.outcome == canonical(MState.of(3, [(0, 1)])) and not ok.answers
    again = attempt(s, Change(Kind.ADD_ASSERTION, 0, 1), 3)
    assert again.outcome == canonical(MState.of(2, [(0, 1), (0, 1)])) and not again.beyond
    blocked = attempt(s, Change(Kind.ADD_ASSERTION, 1, 1), 3)
    assert blocked.obstruction == ((1, 1),) and len(blocked.answers) == 3


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_answers_reach_nothing_new(sameness: Sameness, bra: bool) -> None:
    expl = explore(given(bra, sameness), 3, rounds=6)
    check = check_answers(expl)
    assert check.failures == ()
    assert check.obstructed > 0 and check.answers_within > 0 and check.answers_beyond > 0
    assert removal_answers(expl) == 0


def test_check_answers_reports_what_is_missing() -> None:
    start = canonical(given(False, Sameness.FREE))
    hollow = Exploration(
        start=start,
        bound=3,
        rounds=3,
        depth={start: 0},
        new_per_round=[1],
        attempts_per_round=[0],
        obstructed_per_round=[0],
        frontier=[],
    )
    check = check_answers(hollow)
    assert check.failures and all("/" in f for f in check.failures)
    late = explore(start, 3, rounds=6)
    late.depth[canonical(MState.of(3, [(0, 1), (0, 2)]))] = 99
    assert any("build structure" in f for f in check_answers(late).failures)
    short = explore(start, 3, rounds=1)
    assert check_answers(short).answers_within == 2 and check_answers(short).answers_beyond == 4  # refusals within


def test_removal_answers_would_be_counted(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(given(False, Sameness.FREE), 2, rounds=3)

    def fake(state: MState, change: Change) -> tuple[Answer, ...]:
        return (Answer(AnswerKind.REMOVE_OBSTRUCTION, (), True, state),)

    monkeypatch.setattr(module, "answers", fake)
    assert removal_answers(expl) > 0


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_every_change_raises_the_round_by_one(sameness: Sameness, bra: bool) -> None:
    rounds = 5
    expl = explore(given(bra, sameness), 3, rounds)
    edges = list(performed(expl))
    assert edges
    assert all(expl.depth[out] == expl.depth[state] + 1 for state, _, out in edges)
    assert all(out.size == state.size + 1 for state, _, out in edges)
    tried = [s for s, r in expl.depth.items() if r < rounds]
    assert len(edges) == sum(attempt_counts(s)[0] - attempt_counts(s)[1] - int(s.n == 3) for s in tried)


def test_sequences_are_counted_and_the_witnesses_differ() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, rounds=6)
    seqs = count_sequences(expl)
    assert seqs[expl.start] == 1
    both = canonical(MState.of(2, [(0, 1), (1, 0)], (0, 1)))
    assert seqs[both] == 1
    twice = canonical(MState.of(2, [(0, 1), (0, 1)], (0, 1)))
    assert seqs[twice] == 1
    twice_and_back = canonical(MState.of(2, [(0, 1), (0, 1), (1, 0)], (0, 1)))
    assert seqs[twice_and_back] == 2  # `arb` then `bra`, or `bra` then `arb`
    three = canonical(MState.of(3, [(0, 1), (1, 0)], (0, 1)))
    assert seqs[three] == 2  # add the term then `bra`, or `bra` then the term
    star = canonical(MState.of(3, [(0, 1), (0, 2)], (0, 1)))
    assert seqs[star] == 1  # the term must come before `arc`
    assert all(count >= 1 for count in seqs.values())
    simple = sum(c for s, c in seqs.items() if s.simple)
    assert simple == 393  # the third derivation's total at bound 3 (all its results have round at most 6)
    free = count_sequences(explore(given(False, Sameness.FREE), 3, rounds=6))
    assert sum(free.values()) == sum(seqs.values())
    with_bra = count_sequences(explore(given(True, Sameness.ANCHORED), 3, rounds=5))
    assert sum(c for s, c in with_bra.items() if s.simple) == 66


def test_sequence_count_refuses_a_change_that_does_not_raise_the_round() -> None:
    expl = explore(given(False, Sameness.FREE), 3, rounds=4)
    expl.depth[canonical(MState.of(3, [(0, 1)]))] = 3
    with pytest.raises(ValueError, match="does not raise the round by one"):
        count_sequences(expl)


def test_bound_four_anchored_eight_rounds() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 4, rounds=8)
    by_terms = {n: sum(1 for s in expl.depth if s.n == n) for n in (2, 3, 4)}
    assert by_terms[2] == sum(r + 1 for r in range(9))
    assert by_terms[3] == sum(comb(r + 4, 5) for r in range(1, 9))
    assert by_terms[4] == sum(counts_upto(Sameness.ANCHORED, False, 4, 7)[t] for t in range(8))
    assert all(cost(state, False) == r for state, r in expl.depth.items())
