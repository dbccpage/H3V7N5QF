from __future__ import annotations

from ninth.changes import Change, Kind, changes
from ninth.state import DState, empty
from fifteenth.changes import admission_counts, admission_of_outcome, tagged_admit, tagged_perform
from fifteenth.admission import admitted_record, not_admitted_record
from fifteenth.state import Tagged, added, has_term, tagged_start, written


def test_empty_has_one_change_that_does_not_admit() -> None:
    total, admitted, refused = admission_counts(empty())
    assert total == 1 == refused and admitted == 0
    assert not has_term(empty()) and added(empty()) == (0, 0)
    assert written(empty()) == "no terms; asserted nothing"
    assert tagged_start() == Tagged(empty(), not_admitted_record())


def test_admission_counts_never_admit() -> None:
    between = DState.of(2, [(0, 1)], [])
    total, admitted, refused = admission_counts(between)
    assert total == admitted + refused and admitted == 0 and refused == total
    writing = admission_of_outcome(between, Change(Kind.IDENTIFY, "", 0, 1))
    assert writing == not_admitted_record()


def test_tagged_perform_does_not_admit_and_admit_is_not_a_change() -> None:
    start = tagged_start()
    nxt = tagged_perform(start, Change(Kind.ADD_TERM))
    assert nxt.state == DState.of(1, [], []) and nxt.admission == not_admitted_record()
    admitted = tagged_admit(nxt)
    assert admitted.state == nxt.state and admitted.admission == admitted_record()
    two = Tagged(DState.of(2, [(0, 1)], []), admitted_record())
    merged = tagged_perform(two, Change(Kind.IDENTIFY, "", 0, 1))
    assert merged.admission == not_admitted_record() and merged.state.n == 1
    assert any(c.kind is Kind.IDENTIFY for c in changes(DState.of(2, [], [])))
