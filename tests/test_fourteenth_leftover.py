from __future__ import annotations

import pytest

from ninth.changes import Change, Kind, changes, first_changes
from ninth.state import DState, empty
from fourteenth.leftover import (
    LeftWriting,
    clearing_is_a_kind,
    leftover_merge,
    leftover_nothing,
    leftover_of,
    leftover_pair,
    other_relation,
)


def test_writings_are_neither_xry_nor_xsy() -> None:
    first = first_changes()[0]
    nothing = leftover_of(empty(), first)
    assert nothing == leftover_nothing() and str(nothing) == "nothing"
    assert not nothing.is_assertion() and not nothing.is_answer()
    assert not nothing.is_xry() and not nothing.is_xsy()
    ara = DState.of(1, [(0, 0)], [])
    remove_r = Change(Kind.REMOVE, "r", 0, 0)
    remove_s = Change(Kind.REMOVE, "s", 0, 0)
    pair_r = leftover_of(ara, remove_r)
    pair_s = leftover_of(DState.of(1, [], [(0, 0)]), remove_s)
    assert pair_r == leftover_pair(0, 0) == pair_s
    assert pair_r.written() == "0ℓ0"
    assert not pair_r.is_assertion() and not pair_r.is_xry() and not pair_r.is_xsy()
    two = DState.of(2, [], [])
    ident = Change(Kind.IDENTIFY, "", 0, 1)
    merge = leftover_of(two, ident)
    assert merge == leftover_merge(0, 1) and merge.written() == "0∼1"
    assert not merge.is_assertion() and not clearing_is_a_kind(merge)


def test_additions_leave_nothing() -> None:
    one = DState.of(1, [], [])
    for change in changes(one):
        if change.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION):
            writing = leftover_of(one, change)
            assert writing.kind == "nothing"
            assert not writing.is_xry() and not writing.is_xsy()


def test_other_relation() -> None:
    assert other_relation("r") == "s" and other_relation("s") == "r"
    with pytest.raises(ValueError, match="r or with s"):
        other_relation("t")


def test_pair_is_xry_false_on_pair_kind() -> None:
    pair = leftover_pair(1, 2)
    assert pair.kind == "pair" and "r" not in pair.written() and "s" not in pair.written()
    assert LeftWriting("nothing").written() == "nothing"
