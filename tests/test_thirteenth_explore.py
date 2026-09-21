from __future__ import annotations

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from thirteenth.cost import coarse_cost, cost
from thirteenth.explore import coarse_performed, explore, explore_coarse
from thirteenth.reach import coarse_reachable
from thirteenth.coarse import coarse


def test_explore_matches_the_ninth() -> None:
    thirteenth = explore(empty(), 2, 4)
    ninth = explore_ninth(empty(), 2, 4)
    assert thirteenth.depth == ninth.depth
    assert thirteenth.new_per_round == ninth.new_per_round
    assert thirteenth.last_new_round == 4
    with_log = explore(empty(), 2, 4, keep_log=True)
    assert with_log.log
    assert with_log.awaiting
    assert any(rec.coarser is not None for rec in with_log.log)


def test_coarse_has_fewer_results_and_cost_is_the_size() -> None:
    expl = explore_coarse(2, 5)
    ninth = explore_ninth(empty(), 2, 5)
    assert len(expl.depth) < len(ninth.depth)
    one = coarse(DState.of(1, [], []))
    assert coarse_cost(expl, one) == cost(DState.of(1, [], [])) == 1
    assert coarse_reachable(expl, expl.start, one)
    with pytest.raises(ValueError, match="at least one term"):
        explore_coarse(0, 1)
    with pytest.raises(ValueError, match="not negative"):
        explore_coarse(2, -1)
    small = explore_coarse(2, 2)
    steps = list(coarse_performed(small))
    assert steps
    beyond = list(coarse_performed(explore_coarse(2, 3)))
    assert beyond
