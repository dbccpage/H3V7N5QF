from __future__ import annotations

import pytest

from ninth.changes import Change, Kind, first_changes
from ninth.state import DState, empty
from fifteenth.admission import (
    Admission,
    admission_is_a_kind,
    admission_of_reaching,
    admitted_record,
    can_admit,
    not_admitted_record,
    other_relation,
)


def test_reaching_does_not_admit_and_is_neither_xry_nor_xsy() -> None:
    first = first_changes()[0]
    record = admission_of_reaching(empty())
    assert record == not_admitted_record() and str(record) == "not-admitted"
    assert not record.is_assertion() and not record.is_change()
    assert not record.is_xry() and not record.is_xsy()
    assert not record.is_of_relation("r") and not record.is_of_relation("s")
    assert can_admit(empty()) and can_admit(DState.of(1, [], []))
    assert not admission_is_a_kind(record)
    admitted = admitted_record()
    assert admitted.written() == "admitted"
    assert not admitted.is_xry() and not admitted.is_xsy() and not admitted.is_assertion()
    assert Admission(True).admitted and not Admission(False).admitted
    del first


def test_other_relation() -> None:
    assert other_relation("r") == "s" and other_relation("s") == "r"
    with pytest.raises(ValueError, match="r or with s"):
        other_relation("t")


def test_r_and_s_results_share_the_admission_record() -> None:
    r_only = DState.of(2, [(0, 1)], [])
    s_only = DState.of(2, [], [(0, 1)])
    assert admission_of_reaching(r_only) == admission_of_reaching(s_only) == not_admitted_record()
    ident = Change(Kind.IDENTIFY, "", 0, 1)
    del ident
