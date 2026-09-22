from __future__ import annotations

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from tenth.cost import cost, tagged_cost
from tenth.explore import explore, explore_tagged, leftover_performed, tagged_order, tagged_performed
from tenth.leftover import LeftOver
from tenth.reach import tagged_reachable
from tenth.state import Tagged


def test_explore_matches_the_ninth() -> None:
    tenth = explore(empty(), 2, 4)
    ninth = explore_ninth(empty(), 2, 4)
    assert tenth.depth == ninth.depth
    assert tenth.new_per_round == ninth.new_per_round
    assert tenth.last_new_round == 4
    leftovers = {LeftOver.NOTHING_LEFT, LeftOver.CLEARABLE, LeftOver.UNCLEARED}
    seen = {leftover for _s, _c, _o, leftover in leftover_performed(tenth)}
    assert leftovers <= seen
    with_log = explore(empty(), 2, 4, keep_log=True)
    assert with_log.log and with_log.log[0].leftover is LeftOver.NOTHING_LEFT
    assert with_log.leftover_per_round[1]["nothing left"] >= 1
    assert with_log.leftover_per_round[3]["clearable"] + with_log.leftover_per_round[4]["clearable"] >= 1
    assert with_log.leftover_per_round[4]["uncleared"] >= 1
    assert with_log.awaiting


def test_tagged_has_more_results_and_a_cost_that_is_not_the_size() -> None:
    expl = explore_tagged(2, 4)
    ninth = explore_ninth(empty(), 2, 4)
    assert len(expl.depth) > len(ninth.depth)
    one = DState.of(1, [], [])
    nothing = Tagged(one, LeftOver.NOTHING_LEFT)
    clearable = Tagged(one, LeftOver.CLEARABLE)
    assert tagged_cost(expl, nothing) == cost(one) == 1
    found = tagged_cost(expl, clearable)
    assert found is not None and found > 1
    assert tagged_reachable(expl, expl.start, clearable)
    assert tagged_cost(expl, Tagged(one, LeftOver.UNCLEARED)) is None
    assert tagged_order(nothing)[-1] == LeftOver.NOTHING_LEFT.value
    steps = list(tagged_performed(expl))
    assert steps and steps[0][0] == expl.start
    with pytest.raises(ValueError, match="at least one term"):
        explore_tagged(0, 1)
    with pytest.raises(ValueError, match="not negative"):
        explore_tagged(2, -1)
