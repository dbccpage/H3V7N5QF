from __future__ import annotations

import pytest

from ninth.changes import Change, Kind, perform
from ninth.state import DState, empty, same
from twelfth.record import (
    IdentRecord,
    RelRecord,
    became_one,
    empty_rel,
    other_relation,
    record_determined_by_rel,
    record_of,
    record_rel,
    restores_listed,
    zero_relation,
)


def test_empty_and_between_records() -> None:
    two = DState.of(2, [], [])
    ident = Change(Kind.IDENTIFY, "", 0, 1)
    rec = record_of(two, 0, 1)
    assert rec.is_empty() and rec.r.is_empty() and rec.s.is_empty()
    assert empty_rel() == rec.r
    assert restores_listed(two, ident)
    assert same(perform(perform(two, ident), Change(Kind.ADD_TERM)), two)
    between = DState.of(2, [(0, 1)], [])
    rec_b = record_of(between, 0, 1)
    assert rec_b.r.loop == ("xy",) and rec_b.s.is_empty()
    assert rec_b.r != rec_b.s
    assert not restores_listed(between, ident)
    assert record_determined_by_rel(between, "r", 0, 1)
    assert record_determined_by_rel(between, "s", 0, 1)
    assert not became_one(rec_b.r) and not became_one(rec.r)
    both = DState.of(2, [(0, 1), (1, 0)], [])
    assert became_one(record_rel(both, "r", 0, 1))
    assert rec.swapped() == rec
    assert rec_b.swapped() == IdentRecord(rec_b.s, rec_b.r)
    js = rec.as_json()["r"]
    assert isinstance(js, dict) and js["loop"] == []


def test_other_term_groups_and_errors() -> None:
    three = DState.of(3, [(0, 2), (1, 2)], [(2, 0)])
    rec = record_of(three, 0, 1)
    assert rec.r.outgoing == ((True, True),)
    assert rec.s.incoming == ((True, False),)
    assert became_one(rec.r)
    assert other_relation("r") == "s" and other_relation("s") == "r"
    with pytest.raises(ValueError, match="r or with s"):
        other_relation("t")
    with pytest.raises(ValueError, match="r or with s"):
        zero_relation(three, "t")
    with pytest.raises(ValueError, match="r or with s"):
        record_rel(three, "t", 0, 1)
    with pytest.raises(ValueError, match="x < y"):
        record_of(three, 1, 0)
    assert restores_listed(empty(), Change(Kind.ADD_TERM)) is False
    z = zero_relation(three, "s")
    assert z.s == (0,) * 9 and z.r == three.r
    zr = zero_relation(three, "r")
    assert zr.r == (0,) * 9 and zr.s == three.s
    RelRecord((), (), ())
