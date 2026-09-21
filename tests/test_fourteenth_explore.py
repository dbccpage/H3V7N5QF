from __future__ import annotations

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from fourteenth.cost import cost, tagged_cost
from fourteenth.explore import explore, explore_tagged, leftover_performed, tagged_order, tagged_performed
from fourteenth.leftover import leftover_nothing, leftover_pair
from fourteenth.reach import tagged_reachable
from fourteenth.state import Tagged


def test_explore_matches_the_ninth() -> None:
    fourteenth = explore(empty(), 2, 4)
    ninth = explore_ninth(empty(), 2, 4)
    assert fourteenth.depth == ninth.depth
    assert fourteenth.new_per_round == ninth.new_per_round
    assert fourteenth.last_new_round == 4
    kinds = {writing.kind for _s, _c, _o, writing in leftover_performed(fourteenth)}
    assert kinds == {"nothing", "pair", "merge"}
    with_log = explore(empty(), 2, 4, keep_log=True)
    assert with_log.log and with_log.log[0].leftover == leftover_nothing()
    assert with_log.leftover_per_round[1]["nothing"] >= 1
    assert with_log.leftover_per_round[3]["pair"] + with_log.leftover_per_round[4]["pair"] >= 1
    assert with_log.leftover_per_round[4]["merge"] >= 1
    assert with_log.awaiting


def test_tagged_has_more_results_and_a_cost_that_is_not_the_size() -> None:
    expl = explore_tagged(2, 4)
    ninth = explore_ninth(empty(), 2, 4)
    assert len(expl.depth) > len(ninth.depth)
    one = DState.of(1, [], [])
    nothing = Tagged(one, leftover_nothing())
    pair = Tagged(one, leftover_pair(0, 0))
    assert tagged_cost(expl, nothing) == cost(one) == 1
    found = tagged_cost(expl, pair)
    assert found is not None and found > 1
    assert tagged_reachable(expl, expl.start, pair)
    assert tagged_cost(expl, Tagged(one, leftover_pair(0, 1))) is None
    assert tagged_order(nothing)[-1] == "nothing"
    steps = list(tagged_performed(expl))
    assert steps and steps[0][0] == expl.start
    with pytest.raises(ValueError, match="at least one term"):
        explore_tagged(0, 1)
    with pytest.raises(ValueError, match="not negative"):
        explore_tagged(2, -1)
