from __future__ import annotations

from ninth.state import empty
from fourteenth.explore import explore
from fourteenth.follows import (
    is_assertion_writing,
    leaves_merge,
    leaves_nothing,
    leaves_pair,
    leftover_verdicts,
    verdicts,
)
from fourteenth.leftover import leftover_merge, leftover_nothing, leftover_pair


def test_leftover_statements_do_not_follow() -> None:
    expl = explore(empty(), 2, 4)
    found = leftover_verdicts(expl)
    names = {v.name for v in found}
    assert names == {"leaves_nothing", "leaves_pair", "leaves_merge", "is_assertion_writing"}
    by_name = {v.name: v for v in found}
    assert all(not v.follows for v in found)
    assert by_name["leaves_nothing"].holds_at is not None and by_name["leaves_nothing"].fails_at is not None
    assert by_name["leaves_pair"].holds_at is not None and by_name["leaves_pair"].fails_at is not None
    assert by_name["leaves_merge"].holds_at is not None and by_name["leaves_merge"].fails_at is not None
    assert by_name["is_assertion_writing"].holds_at is None and by_name["is_assertion_writing"].fails_at is not None
    assert leaves_nothing(leftover_nothing()) and not leaves_nothing(leftover_pair(0, 0))
    assert leaves_pair(leftover_pair(0, 1)) and leaves_merge(leftover_merge(0, 1))
    assert not is_assertion_writing(leftover_pair(0, 1))
    state_v = verdicts(expl)
    assert state_v and any(not v.follows_within_bound for v in state_v)
