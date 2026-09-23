from __future__ import annotations

from sixteenth.changes import Change16, Kind
from sixteenth.cost import GIVEN_POTENTIAL, cost16, cost_ninth, diag_mass, lowers_by_one, mass, potential, raises_by_one
from sixteenth.explore import explore16
from sixteenth.reach import (
    carries,
    carrying_maps,
    mass_ok,
    mutual16,
    reach_graph16,
    reachable16,
    reachable_by_search16,
    reachable_in_graph16,
    reachable_ninth,
)
from sixteenth.state import RState, empty16


def test_cost_is_the_potential() -> None:
    assert GIVEN_POTENTIAL == 0 and cost16(empty16()) == 0
    ara = RState.of(1, [(0, 0)])
    left = RState.of(1, [], [], [(0, 0)])
    assert cost16(ara) == 2 == cost_ninth(ara) and cost16(left) == 3 and cost_ninth(left) == 1
    assert potential(left) == 3 and mass(left) == 1 == mass(ara) and diag_mass(left) == 1
    off = RState.of(2, [(0, 1)], [], [(1, 0)])
    assert mass(off) == 2 and diag_mass(off) == 0
    remove = Change16(Kind.REMOVE, "r", 0, 0)
    admit = Change16(Kind.ADD_ASSERTION, "r", 0, 0, True)
    assert raises_by_one(ara, remove) and not lowers_by_one(ara, remove)
    assert lowers_by_one(left, admit) and not raises_by_one(left, admit)
    assert lowers_by_one(off, Change16(Kind.IDENTIFY, "", 0, 1)) and raises_by_one(off, Change16(Kind.ADD_TERM))


def test_criterion_on_the_headline_witnesses() -> None:
    one = RState.of(1, [])
    ara = RState.of(1, [(0, 0)])
    left = RState.of(1, [], [], [(0, 0)])
    assert reachable16(empty16(), one) and reachable16(empty16(), left) and not reachable16(one, empty16())
    assert reachable16(one, ara) and not reachable16(ara, one) and reachable_ninth(ara, one)
    assert reachable16(ara, left) and reachable16(left, ara) and mutual16(ara, left) and not mutual16(one, ara)
    assert mass_ok(one, ara) and not mass_ok(ara, one)
    assert carrying_maps(empty16(), one) == [()] and carrying_maps(ara, one) == []
    assert carrying_maps(one, ara) == [(0,)]
    # mass can only merge: an off-diagonal unit cannot become a diagonal one and back
    across = RState.of(2, [(0, 1)], [])
    diagonal = RState.of(2, [(0, 0)], [])
    assert reachable16(across, diagonal) and not reachable16(diagonal, across)
    # the two invariants hold and the criterion still refuses
    s = RState.of(2, [(0, 0), (0, 1)], [])
    t = RState.of(2, [(0, 0), (1, 1)], [])
    assert mass_ok(s, t) and not carries(s, t)


def test_criterion_agrees_with_search_on_a_small_bound() -> None:
    expl = explore16(empty16(), 2, 4)
    wide = explore16(empty16(), 2, 6)
    graph = reach_graph16(wide)
    states = list(expl.depth)
    for s in states:
        found = reachable_in_graph16(graph, s) & set(states)
        for t in states:
            assert reachable16(s, t) == (t in found)
            assert not reachable16(s, t) or reachable_ninth(s, t)
    seen = reachable_by_search16(RState.of(1, [(0, 0)]), 2, 3)
    assert RState.of(1, []) not in seen and RState.of(1, [], [(0, 0)]) in seen
