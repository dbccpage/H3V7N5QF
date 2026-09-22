from __future__ import annotations

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from eleventh.cost import cost, labeled_cost
from eleventh.explore import explore, explore_labeled, labeled_determines, labeled_order, writings_of
from eleventh.reach import labeled_reachable
from eleventh.state import Labeled


def test_explore_matches_the_ninth() -> None:
    eleventh = explore(empty(), 2, 4)
    ninth = explore_ninth(empty(), 2, 4)
    assert eleventh.depth == ninth.depth
    assert eleventh.new_per_round == ninth.new_per_round
    assert eleventh.last_new_round == 4
    with_log = explore(empty(), 2, 4, keep_log=True)
    assert with_log.log
    assert with_log.awaiting
    assert writings_of(DState.of(2, [], [])) == ((0, 0), (0, 1))


def test_labeled_has_more_results_and_cost_is_the_size() -> None:
    expl = explore_labeled(2, 4)
    ninth = explore_ninth(empty(), 2, 4)
    assert len(expl.depth) > len(ninth.depth)
    two = DState.of(2, [], [])
    apart = Labeled(two, (0, 1))
    collide = Labeled(two, (0, 0))
    assert labeled_cost(expl, apart) == cost(two) == 2
    assert labeled_cost(expl, collide) == 2
    assert labeled_reachable(expl, expl.start, collide)
    assert labeled_order(apart)[-1] == (0, 1)
    assert labeled_determines(apart) and not labeled_determines(Labeled(DState.of(2, [(0, 1)], []), (0, 0)))
    with pytest.raises(ValueError, match="at least one term"):
        explore_labeled(0, 1)
    with pytest.raises(ValueError, match="not negative"):
        explore_labeled(2, -1)
