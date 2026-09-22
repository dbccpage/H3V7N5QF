from __future__ import annotations

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from twelfth.cost import cost, recorded_cost
from twelfth.explore import explore, explore_recorded, recorded_order
from twelfth.reach import recorded_reachable
from twelfth.record import record_of
from twelfth.state import Recorded


def test_explore_matches_the_ninth() -> None:
    twelfth = explore(empty(), 2, 4)
    ninth = explore_ninth(empty(), 2, 4)
    assert twelfth.depth == ninth.depth
    assert twelfth.new_per_round == ninth.new_per_round
    assert twelfth.last_new_round == 4
    with_log = explore(empty(), 2, 4, keep_log=True)
    assert with_log.log
    assert with_log.awaiting
    assert any(rec.record is not None for rec in with_log.log)
    assert with_log.identifications_per_round[3] >= 1


def test_recorded_has_more_results_and_cost_is_not_always_the_size() -> None:
    expl = explore_recorded(2, 5)
    ninth = explore_ninth(empty(), 2, 5)
    assert len(expl.depth) > len(ninth.depth)
    one = DState.of(1, [], [])
    plain = Recorded(one, None)
    tagged = Recorded(one, record_of(DState.of(2, [], []), 0, 1))
    assert recorded_cost(expl, plain) == cost(one) == 1
    ident_cost = recorded_cost(expl, tagged)
    assert ident_cost is not None and ident_cost == 3
    assert recorded_reachable(expl, expl.start, tagged)
    assert recorded_order(plain)[-2] is False
    with pytest.raises(ValueError, match="at least one term"):
        explore_recorded(0, 1)
    with pytest.raises(ValueError, match="not negative"):
        explore_recorded(2, -1)
    from twelfth.explore import recorded_performed

    small = explore_recorded(2, 2)
    steps = list(recorded_performed(small))
    assert steps
    beyond = list(recorded_performed(explore_recorded(2, 3)))
    assert beyond

