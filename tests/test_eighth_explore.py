from __future__ import annotations

import pytest

from eighth.changes import Change, Kind, attempt_counts
from eighth.cost import cost
from eighth.explore import Exploration, attempt, count_shortest_sequences, cycle, explore, order, performed, sequences_exact
from eighth.orbits import layer_counts, two_term_round_count
from eighth.state import DState, canonical, given
from sixth.explore import count_shortest_sequences as count_shortest_sequences_sixth
from sixth.explore import explore as explore_sixth
from sixth.state import given as given_sixth
from xry.state import Sameness

COMBOS = [(s, bra) for s in Sameness for bra in (False, True)]


def test_explore_needs_a_start_with_a_term_within_the_bound() -> None:
    with pytest.raises(ValueError):
        explore(DState(0, (), ()), 3)
    with pytest.raises(ValueError):
        explore(given(False, Sameness.FREE), 1)
    with pytest.raises(ValueError):
        explore(given(False, Sameness.FREE), 3, rounds=-1)
    none = explore(given(False, Sameness.FREE), 3, rounds=0)
    assert len(none.depth) == 1 and none.awaiting == [none.start] and none.last_new_round == 0
    one = explore(given(False, Sameness.ANCHORED), 3, rounds=1, keep_log=True)
    assert one.new_per_round == [1, 11] and one.attempts_per_round == [0, 11]
    assert one.xrx_per_round == [0, 3] and one.xsx_per_round == [0, 2] and len(one.log) == 11


@pytest.mark.parametrize(("sameness", "bra"), COMBOS)
def test_every_result_is_reached_at_its_cost_and_the_sixths_are_those_with_nothing_in_s(sameness: Sameness, bra: bool) -> None:
    bound, rounds = 3, 4
    expl = explore(given(bra, sameness), bound, rounds)
    assert all(state.n >= 1 and canonical(state) == state for state in expl.depth)
    assert all(cost(state, bra) == r for state, r in expl.depth.items())
    assert sum(expl.new_per_round) == len(expl.depth) and expl.last_new_round == rounds
    assert expl.awaiting == sorted(expl.awaiting, key=order)
    assert expl.new_per_round[: bound - 1] == layer_counts(sameness, bra, bound - 2)
    assert any(not state.nothing_in_s for state in expl.depth) and any(not state.legal_s for state in expl.depth)
    sixth = explore_sixth(given_sixth(bra, sameness), bound, rounds)
    assert {s.r_part(): r for s, r in expl.depth.items() if s.nothing_in_s} == sixth.depth
    sequences = count_shortest_sequences(expl)
    sixth_sequences = count_shortest_sequences_sixth(sixth)
    assert all(sequences[s] == sixth_sequences[s.r_part()] for s in expl.depth if s.nothing_in_s)
    assert all(sequences_exact(expl, s, bra) for s in expl.depth if s.n < bound)
    for state, change, out in performed(expl):
        assert expl.depth[out] <= expl.depth[state] + 1
    assert all(cycle(s) is not None for s in expl.depth)


def test_two_terms_all_rounds() -> None:
    for bra in (False, True):
        two = explore(given(bra, Sameness.ANCHORED), 2, 7)
        assert two.new_per_round == [two_term_round_count(bra, r) for r in range(8)]
    assert [two_term_round_count(False, r) for r in range(6)] == [1, 10, 47, 161, 462, 1156]
    assert [two_term_round_count(True, r) for r in range(6)] == [1, 11, 55, 196, 569, 1430]
    with pytest.raises(ValueError):
        two_term_round_count(False, -1)


def test_attempts_and_sequence_checks() -> None:
    s = given(False, Sameness.ANCHORED)
    rec = attempt(s, Change(Kind.ADD_TERM), 2)
    assert rec.beyond and rec.outcome is None and not rec.xrx and not rec.xsx
    loop = attempt(s, Change(Kind.ADD_ASSERTION, "s", 0, 0), 2)
    assert loop.xsx and not loop.xrx and loop.outcome == DState.of(2, [(0, 1)], [(0, 0)], (0, 1))
    expl = explore(s, 2, 3)
    expl.depth[DState.of(2, [(0, 1)], [(0, 1)], (0, 1))] = 3
    with pytest.raises(ValueError, match="more than one"):
        count_shortest_sequences(expl)
    assert cycle(DState(0, (), ())) is None and cycle(DState.of(1, [], [])) is not None
    free = explore(given(False, Sameness.FREE), 2, 3)
    assert all(sequences_exact(free, st, False) for st in free.depth if st.n < 2)
    assert any(not sequences_exact(free, st, False) for st in free.depth)  # a merged placement can be optimal
    hollow = Exploration(
        start=s, bound=2, rounds=3, depth={s: 0}, new_per_round=[1], attempts_per_round=[0], xrx_per_round=[0], xsx_per_round=[0]
    )
    assert hollow.awaiting == [] and hollow.last_new_round == 0
    assert attempt_counts(s)[0] == 11
