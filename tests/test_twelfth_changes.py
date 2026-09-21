from __future__ import annotations

import pytest

from ninth.changes import Change, Kind, first_changes
from ninth.state import DState, empty
from twelfth.changes import record_of_change, recorded_perform
from twelfth.record import record_of
from twelfth.state import Recorded, added, has_term, recorded_start, written


def test_empty_has_one_change_and_no_record() -> None:
    assert first_changes() == (Change(Kind.ADD_TERM),)
    assert not has_term(empty()) and added(empty()) == (0, 0)
    assert written(empty()) == "no terms; asserted nothing"
    assert recorded_start() == Recorded(empty(), None)
    assert record_of_change(empty(), Change(Kind.ADD_TERM)) is None


def test_identify_attaches_a_record_other_kinds_keep_it() -> None:
    two = DState.of(2, [(0, 1)], [])
    ident = Change(Kind.IDENTIFY, "", 0, 1)
    rec = record_of(two, 0, 1)
    assert record_of_change(two, ident) == rec
    start = Recorded(two, None)
    after = recorded_perform(start, ident)
    assert after.n == 1 and after.record == rec and after.size == after.state.size
    kept = recorded_perform(after, Change(Kind.ADD_TERM))
    assert kept.n == 2 and kept.record == rec
    with pytest.raises(TypeError, match="two-relation"):
        record_of_change("no", ident)
