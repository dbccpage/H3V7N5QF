from __future__ import annotations

from ninth.state import empty
from tenth.explore import explore
from tenth.follows import leftover_verdicts, leaves_clearable, leaves_nothing, leaves_uncleared, verdicts
from tenth.leftover import LeftOver


def test_leftover_statements_do_not_follow() -> None:
    expl = explore(empty(), 2, 4)
    found = leftover_verdicts(expl)
    names = {v.name for v in found}
    assert names == {"leaves_nothing", "leaves_clearable", "leaves_uncleared"}
    assert all(v.holds_at is not None and v.fails_at is not None and not v.follows for v in found)
    assert leaves_nothing(LeftOver.NOTHING_LEFT) and not leaves_nothing(LeftOver.CLEARABLE)
    assert leaves_clearable(LeftOver.CLEARABLE) and leaves_uncleared(LeftOver.UNCLEARED)
    state_v = verdicts(expl)
    assert state_v and any(not v.follows_within_bound for v in state_v)
