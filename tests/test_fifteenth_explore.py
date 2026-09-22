from __future__ import annotations

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from fifteenth.admission import admitted_record, not_admitted_record
from fifteenth.cost import cost, tagged_cost
from fifteenth.explore import explore, explore_tagged, admission_performed, tagged_order, tagged_performed
from fifteenth.reach import tagged_reachable
from fifteenth.state import Tagged


def test_explore_matches_the_ninth() -> None:
    fifteenth = explore(empty(), 2, 4)
    ninth = explore_ninth(empty(), 2, 4)
    assert fifteenth.depth == ninth.depth
    assert fifteenth.new_per_round == ninth.new_per_round
    assert fifteenth.last_new_round == 4
    records = {record.written() for _s, _c, _o, record in admission_performed(fifteenth)}
    assert records == {"not-admitted"}
    with_log = explore(empty(), 2, 4, keep_log=True)
    assert with_log.log and with_log.log[0].admission == not_admitted_record()
    assert with_log.admission_per_round[1]["not-admitted"] >= 1
    assert with_log.admission_per_round[1]["admitted"] == 0
    assert with_log.awaiting


def test_tagged_has_more_results_and_a_cost_that_is_not_the_size() -> None:
    expl = explore_tagged(2, 4)
    ninth = explore_ninth(empty(), 2, 4)
    assert len(expl.depth) > len(ninth.depth)
    one = DState.of(1, [], [])
    nothing = Tagged(one, not_admitted_record())
    admitted = Tagged(one, admitted_record())
    assert tagged_cost(expl, nothing) == cost(one) == 1
    found = tagged_cost(expl, admitted)
    assert found is not None and found > 1
    assert tagged_reachable(expl, expl.start, admitted)
    assert tagged_order(nothing)[-1] == "not-admitted"
    steps = list(tagged_performed(expl))
    assert steps and steps[0][0] == expl.start
    with pytest.raises(ValueError, match="at least one term"):
        explore_tagged(0, 1)
    with pytest.raises(ValueError, match="not negative"):
        explore_tagged(2, -1)
