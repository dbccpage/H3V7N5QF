from __future__ import annotations

import pytest

from xry.changes import Change, Kind, changes
from xry.cost import cost
from xry.explore import Exploration, attempt, check_answers, explore, order, rigid
from xry.orbits import count_states, layer_counts
from xry.state import Sameness, State, canonical, given

COMBOS = [(s, bra) for s in Sameness for bra in (False, True)]


def test_explore_needs_a_legal_start_within_the_bound() -> None:
    with pytest.raises(ValueError):
        explore(State.of(1, [(0, 0)]), 3)
    with pytest.raises(ValueError):
        explore(given(False, Sameness.FREE), 1)


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_everything_within_the_bound_is_reached_at_its_cost(sameness: Sameness, bra: bool) -> None:
    bound = 3
    expl = explore(given(bra, sameness), bound, rounds=30)
    for n in range(1, bound + 1):
        explored = [0] * (n * (n - 1) + 1)
        for state in expl.depth:
            if state.n == n:
                explored[state.m] += 1
        assert explored == count_states(sameness, n)
    assert all(state.legal and canonical(state) == state for state in expl.depth)
    assert all(cost(state, bra) == r for state, r in expl.depth.items())
    assert expl.depth[expl.start] == 0
    assert sum(expl.new_per_round) == len(expl.depth)
    assert expl.new_per_round[expl.last_new_round] > 0
    assert not any(expl.new_per_round[expl.last_new_round + 1 :])


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_early_rounds_agree_with_the_count_without_bound(sameness: Sameness, bra: bool) -> None:
    bound = 4 if sameness is Sameness.FREE else 3
    expl = explore(given(bra, sameness), bound, rounds=bound)
    exact = layer_counts(sameness, bra, bound)
    assert expl.new_per_round[: bound - 1] == exact[: bound - 1]
    assert expl.new_per_round[bound - 1] < exact[bound - 1]


def test_the_frontier_is_exactly_the_attempts_that_leave_the_bound() -> None:
    bound = 3
    expl = explore(given(False, Sameness.ANCHORED), bound, rounds=30)
    full = [s for s in expl.depth if s.n == bound]
    assert {leave.state for leave in expl.frontier} == set(full)
    assert len(expl.frontier) == len(full) * (1 + 2 * bound)
    by_change = [leave for leave in expl.frontier if leave.by == "the change"]
    assert all(leave.change.kind is Kind.ADD_TERM for leave in by_change)
    assert len(by_change) == len(full)


def test_attempts_are_counted_round_by_round_and_logged() -> None:
    expl = explore(given(True, Sameness.FREE), 3, rounds=20, keep_log=True)
    assert expl.attempts_per_round[0] == 0
    assert expl.attempts_per_round[1] == len(changes(expl.start)) == 6
    assert expl.obstructed_per_round[1] == 3
    assert expl.attempts_per_round == sorted(expl.attempts_per_round)
    assert len(expl.log) == expl.attempts_per_round[-1]
    assert len(expl.log) == sum(len(changes(s)) for s in expl.depth)
    first = expl.log[0]
    assert first.change == Change(Kind.IDENTIFY, 0, 1) and first.answers and first.outcome is None
    beyond = [rec for rec in expl.log if rec.beyond]
    assert beyond and all(rec.change.kind is Kind.ADD_TERM for rec in beyond)


def test_one_attempt() -> None:
    s = given(False, Sameness.FREE)
    assert attempt(s, Change(Kind.ADD_TERM), 2).beyond
    ok = attempt(s, Change(Kind.ADD_TERM), 3)
    assert ok.outcome == canonical(State.of(3, [(0, 1)])) and not ok.answers
    blocked = attempt(s, Change(Kind.ADD_ASSERTION, 1, 1), 3)
    assert blocked.obstruction == ((1, 1),) and len(blocked.answers) == 3


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_answers_reach_nothing_new(sameness: Sameness, bra: bool) -> None:
    expl = explore(given(bra, sameness), 3, rounds=30)
    check = check_answers(expl)
    assert check.failures == ()
    assert check.obstructed > 0 and check.answers_within > 0 and check.answers_beyond > 0


def test_check_answers_reports_what_is_missing() -> None:
    start = canonical(given(False, Sameness.FREE))
    hollow = Exploration(
        start=start,
        bound=3,
        rounds=0,
        depth={start: 0},
        new_per_round=[1],
        attempts_per_round=[0],
        obstructed_per_round=[0],
        frontier=[],
    )
    check = check_answers(hollow)
    assert check.failures and all("/" in f for f in check.failures)
    late = explore(start, 3, rounds=30)
    late.depth[canonical(State.of(1, []))] = 99
    assert any("remove the obstruction" in f for f in check_answers(late).failures)


def test_bound_four_anchored() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 4)
    assert len(expl.depth) == 1 + 8 + 100 + 2864
    assert expl.last_new_round == 17
    assert all(cost(state, False) == r for state, r in expl.depth.items())


def test_rigid_means_every_identification_is_obstructed() -> None:
    assert rigid(given(False, Sameness.FREE)) and rigid(given(True, Sameness.FREE))
    assert not rigid(State.of(1, []))
    assert not rigid(State.of(2, []))
    assert not rigid(State.of(3, [(0, 1), (1, 2)]))
    assert rigid(State.of(3, [(0, 1), (1, 2), (2, 0)]))


def test_order_is_total_on_states() -> None:
    assert order(State.of(2, [])) < order(State.of(2, [(0, 1)])) < order(State.of(3, []))
    assert order(State(2, 0, (0, 1))) != order(State(2, 0, (1, 0)))
