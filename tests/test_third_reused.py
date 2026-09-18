"""The modules that re-export second-derivation functions still describe the third seed."""

from __future__ import annotations

from second import cost as cost_second
from second import follows as follows_second
from second import orbits as orbits_second
from third import cost, follows, orbits
from third.explore import explore
from xry.state import Sameness, State, given


def test_cost_is_the_second_derivations_closed_form() -> None:
    assert cost.cost is cost_second.cost and cost.cost_free is cost_second.cost_free
    for sameness in Sameness:
        for bra in (False, True):
            assert cost.cost(given(bra, sameness), bra) == 0
    assert cost.cost_anchored(State.of(3, [(0, 1), (0, 2)], (0, 1)), False) == 2
    assert cost.cost_free(State.of(3, []), False) is None
    assert cost.given_size(True) == 4 and cost.has_two_way(State.of(2, [(0, 1), (1, 0)]))
    assert cost.contains_given(State.of(2, [(0, 1)], (0, 1)), False)
    assert cost.cost_free_by_placement(State.of(2, [(0, 1)]), False) == 0


def test_counts_are_the_second_derivations() -> None:
    assert orbits.count_results is orbits_second.count_results
    assert orbits.layer_counts is orbits_second.layer_counts
    assert [sum(orbits.count_results(Sameness.ANCHORED, False, n)) for n in range(1, 5)] == [0, 2, 32, 1056]
    assert orbits.layer_counts(Sameness.FREE, False, 2) == [1, 2, 5]


def test_statements_are_the_second_derivations_and_hold_again() -> None:
    assert follows.verdicts is follows_second.verdicts
    assert follows.EXTRA == (follows.at_least_two_terms,)
    for bra in (False, True):
        expl = explore(given(bra, Sameness.ANCHORED), 3, rounds=30)
        found = {v.statement: v for v in follows.verdicts(expl)}
        for name in ("arb_asserted", "names_apart", "something_asserted", "at_least_two_terms", "no_xrx"):
            assert found[name].follows_within_bound and not found[name].independent
        assert found["bra_asserted"].follows_within_bound == bra
        for name in ("exactly_two_terms", "any_two_related", "every_term_mentioned"):
            assert found[name].independent
        assert found["passes_on"].independent == (not bra)
    free = {v.statement: v for v in follows.verdicts(explore(given(True, Sameness.FREE), 3, rounds=30))}
    assert "bra_asserted" not in free and free["both_ways_never"].holds_at is None
