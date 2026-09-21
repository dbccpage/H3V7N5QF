from __future__ import annotations

from ninth.changes import Change, Kind, first_changes
from ninth.state import DState, empty
from thirteenth.changes import coarse_of_outcome
from thirteenth.coarse import coarse
from thirteenth.state import added, has_term, written


def test_empty_has_one_change() -> None:
    assert first_changes() == (Change(Kind.ADD_TERM),)
    assert not has_term(empty()) and added(empty()) == (0, 0)
    assert written(empty()) == "no terms; asserted nothing"
    assert coarse_of_outcome(empty(), Change(Kind.ADD_TERM)) == coarse(DState.of(1, [], []))


def test_add_assertion_coarser_ignores_the_relation() -> None:
    two = DState.of(2, [], [])
    add_r = Change(Kind.ADD_ASSERTION, "r", 0, 1)
    add_s = Change(Kind.ADD_ASSERTION, "s", 0, 1)
    assert coarse_of_outcome(two, add_r) == coarse_of_outcome(two, add_s)
