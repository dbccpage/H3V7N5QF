from __future__ import annotations

from ninth.state import DState, empty
from thirteenth.explore import explore
from thirteenth.follows import (
    both_relations,
    coarse_verdicts,
    determines_finer,
    unique_split,
    swap_same_coarse,
    verdicts,
)


def test_coarse_statements_do_not_follow() -> None:
    expl = explore(empty(), 2, 4)
    found = coarse_verdicts(expl)
    names = {v.name for v in found}
    assert names == {"determines_finer", "unique_split", "swap_same_coarse", "both_relations"}
    by_name = {v.name: v for v in found}
    assert by_name["determines_finer"].holds_at is not None and by_name["determines_finer"].fails_at is not None
    assert by_name["swap_same_coarse"].holds_at is not None
    assert not by_name["determines_finer"].follows
    two = DState.of(2, [], [])
    between = DState.of(2, [(0, 1)], [])
    both = DState.of(2, [(0, 1)], [(0, 1)])
    assert determines_finer(two) and unique_split(two)
    assert not determines_finer(between)
    assert swap_same_coarse(between)
    assert both_relations(both)
    state_v = verdicts(expl)
    assert state_v and any(not v.follows_within_bound for v in state_v)
