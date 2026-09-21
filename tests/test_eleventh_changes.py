from __future__ import annotations

import pytest

from ninth.changes import Change, Kind, first_changes
from ninth.state import DState, empty
from eleventh.changes import labeled_of, perform
from eleventh.state import Labeled, added, has_term, labeled_start, written
from eleventh.writing import terms_after_writing


def test_empty_has_one_change_and_one_writing() -> None:
    assert first_changes() == (Change(Kind.ADD_TERM),)
    assert not has_term(empty()) and added(empty()) == (0, 0)
    assert written(empty()) == "no terms; asserted nothing"
    assert labeled_start() == Labeled(empty(), ())
    assert labeled_of(empty()) == (Labeled(empty(), ()),)


def test_identify_drops_a_term_writing_does_not() -> None:
    between = DState.of(2, [(0, 1)], [])
    merged = perform(between, Change(Kind.IDENTIFY, "", 0, 1))
    assert merged.n == 1
    assert terms_after_writing(between, (0, 0)) == 2
    labs = labeled_of(DState.of(2, [], []))
    assert {lab.writing for lab in labs} == {(0, 0), (0, 1)}
    assert labs[0].n == 2 and labs[0].size == 2
    with pytest.raises(ValueError, match="every term"):
        Labeled(between, (0,))
