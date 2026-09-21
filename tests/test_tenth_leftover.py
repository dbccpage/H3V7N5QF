from __future__ import annotations

import pytest

from ninth.changes import Change, Kind, changes, first_changes, perform
from ninth.state import DState, empty, same
from tenth.leftover import LeftOver, clearing_change, leftover_of, other_relation, restores_in_one


def test_three_outcomes_inhabited() -> None:
    first = first_changes()[0]
    assert leftover_of(empty(), first) is LeftOver.NOTHING_LEFT
    ara = DState.of(1, [(0, 0)], [])
    remove = Change(Kind.REMOVE, "r", 0, 0)
    assert leftover_of(ara, remove) is LeftOver.CLEARABLE
    later = clearing_change(remove)
    assert later is not None and same(perform(perform(ara, remove), later), ara)
    two = DState.of(2, [], [])
    ident = Change(Kind.IDENTIFY, "", 0, 1)
    assert leftover_of(two, ident) is LeftOver.CLEARABLE and restores_in_one(two, ident)
    between = DState.of(2, [(0, 1)], [])
    assert leftover_of(between, ident) is LeftOver.UNCLEARED and not restores_in_one(between, ident)
    assert str(LeftOver.NOTHING_LEFT) == "nothing left"
    assert clearing_change(first) is None


def test_additions_leave_nothing() -> None:
    one = DState.of(1, [], [])
    for change in changes(one):
        if change.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION):
            assert leftover_of(one, change) is LeftOver.NOTHING_LEFT


def test_other_relation() -> None:
    assert other_relation("r") == "s" and other_relation("s") == "r"
    with pytest.raises(ValueError, match="r or with s"):
        other_relation("t")
