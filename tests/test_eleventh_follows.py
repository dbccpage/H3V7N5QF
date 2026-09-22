from __future__ import annotations

from ninth.state import DState, empty
from eleventh.explore import explore
from eleventh.follows import (
    collides,
    collides_r_only,
    determines_both,
    is_injective,
    verdicts,
    writing_verdicts,
)


def test_writing_statements_do_not_follow() -> None:
    expl = explore(empty(), 2, 4)
    found = writing_verdicts(expl)
    names = {v.name for v in found}
    assert names == {"injective", "determines", "collides", "collides_r_only"}
    assert all(v.holds_at is not None and v.fails_at is not None and not v.follows for v in found)
    between = DState.of(2, [(0, 1)], [])
    assert is_injective((0, 1)) and not is_injective((0, 0))
    assert determines_both(between, (0, 1)) and collides(between, (0, 0))
    assert collides_r_only(between, (0, 0))
    state_v = verdicts(expl)
    assert state_v and any(not v.follows_within_bound for v in state_v)
