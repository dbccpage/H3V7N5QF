from __future__ import annotations

import pytest

from ninth.changes import Change, Kind, changes
from ninth.state import DState, empty
from tenth.changes import leftover_counts, other_clears, tagged_perform
from tenth.leftover import LeftOver
from tenth.state import Tagged, added, has_term, tagged_start, written


def test_empty_has_one_change_leaving_nothing() -> None:
    total, nothing, clearable, uncleared = leftover_counts(empty())
    assert total == 1 == nothing and clearable == 0 == uncleared
    assert not has_term(empty()) and added(empty()) == (0, 0)
    assert written(empty()) == "no terms; asserted nothing"
    assert tagged_start() == Tagged(empty(), LeftOver.NOTHING_LEFT)


def test_other_clears_a_removal_is_false(monkeypatch: pytest.MonkeyPatch) -> None:
    ara = DState.of(1, [(0, 0)], [])
    remove = Change(Kind.REMOVE, "r", 0, 0)
    assert not other_clears(ara, remove)
    assert not other_clears(empty(), Change(Kind.ADD_TERM))
    both = DState.of(1, [(0, 0)], [(0, 0)])
    assert not other_clears(both, remove)
    monkeypatch.setattr("tenth.changes.same", lambda _a, _b: True)
    assert other_clears(ara, remove)


def test_tagged_perform_records_the_incoming_leftover() -> None:
    start = tagged_start()
    nxt = tagged_perform(start, Change(Kind.ADD_TERM))
    assert nxt.state == DState.of(1, [], []) and nxt.leftover is LeftOver.NOTHING_LEFT
    two = Tagged(DState.of(2, [(0, 1)], []), LeftOver.NOTHING_LEFT)
    merged = tagged_perform(two, Change(Kind.IDENTIFY, "", 0, 1))
    assert merged.leftover is LeftOver.UNCLEARED and merged.state.n == 1
    assert leftover_counts(DState.of(2, [(0, 1)], []))[3] >= 1
    assert any(c.kind is Kind.IDENTIFY for c in changes(DState.of(2, [], [])))
