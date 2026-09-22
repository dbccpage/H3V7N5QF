from __future__ import annotations

from ninth.changes import Change, Kind
from ninth.state import DState, empty
from twelfth.explore import explore
from twelfth.follows import (
    differs,
    empty_record,
    nonempty_record,
    record_of_ident,
    record_verdicts,
    verdicts,
)
from twelfth.record import record_of


def test_record_statements_do_not_follow() -> None:
    expl = explore(empty(), 2, 4)
    found = record_verdicts(expl)
    names = {v.name for v in found}
    assert names == {"empty_record", "nonempty_record", "differs", "r_became_one", "restored", "determined"}
    by_name = {v.name: v for v in found}
    assert by_name["empty_record"].holds_at is not None and by_name["empty_record"].fails_at is not None
    assert by_name["nonempty_record"].holds_at is not None and by_name["nonempty_record"].fails_at is not None
    assert by_name["differs"].holds_at is not None and by_name["differs"].fails_at is not None
    assert not by_name["empty_record"].follows
    two = DState.of(2, [], [])
    between = DState.of(2, [(0, 1)], [])
    ident = Change(Kind.IDENTIFY, "", 0, 1)
    assert empty_record(two, ident, record_of(two, 0, 1))
    assert nonempty_record(between, ident, record_of(between, 0, 1))
    assert differs(between, ident, record_of(between, 0, 1))
    assert record_of_ident(between, ident) == record_of(between, 0, 1)
    state_v = verdicts(expl)
    assert state_v and any(not v.follows_within_bound for v in state_v)
