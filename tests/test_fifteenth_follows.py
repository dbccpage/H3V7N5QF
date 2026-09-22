from __future__ import annotations

from ninth.state import empty
from fifteenth.admission import admitted_record, not_admitted_record
from fifteenth.explore import explore
from fifteenth.follows import (
    can_be_admitted,
    is_admitted,
    is_assertion_record,
    is_not_admitted,
    admission_verdicts,
    verdicts,
)


def test_admission_statements() -> None:
    expl = explore(empty(), 2, 4)
    found = admission_verdicts(expl)
    names = {v.name for v in found}
    assert names == {"is_not_admitted", "is_admitted", "is_assertion_record", "can_be_admitted"}
    by_name = {v.name: v for v in found}
    assert by_name["is_not_admitted"].follows and by_name["can_be_admitted"].follows
    assert not by_name["is_admitted"].follows and not by_name["is_assertion_record"].follows
    assert by_name["is_admitted"].holds_at is None and by_name["is_admitted"].fails_at is not None
    assert by_name["is_assertion_record"].holds_at is None and by_name["is_assertion_record"].fails_at is not None
    assert is_not_admitted(not_admitted_record()) and not is_not_admitted(admitted_record())
    assert is_admitted(admitted_record()) and not is_admitted(not_admitted_record())
    assert not is_assertion_record(not_admitted_record()) and can_be_admitted(admitted_record())
    state_v = verdicts(expl)
    assert state_v and any(not v.follows_within_bound for v in state_v)
