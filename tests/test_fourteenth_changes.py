from __future__ import annotations

from ninth.changes import Change, Kind, changes
from ninth.state import DState, empty
from fourteenth.changes import leftover_counts, leftover_of_outcome, tagged_perform
from fourteenth.leftover import leftover_merge, leftover_merge_survivor, leftover_nothing
from fourteenth.state import Tagged, added, has_term, tagged_start, written


def test_empty_has_one_change_leaving_nothing() -> None:
    total, nothing, pair, merge = leftover_counts(empty())
    assert total == 1 == nothing and pair == 0 == merge
    assert not has_term(empty()) and added(empty()) == (0, 0)
    assert written(empty()) == "no terms; asserted nothing"
    assert tagged_start() == Tagged(empty(), leftover_nothing())


def test_leftover_counts_split_kinds() -> None:
    between = DState.of(2, [(0, 1)], [])
    total, nothing, pair, merge = leftover_counts(between)
    assert total == nothing + pair + merge and pair >= 1 and merge >= 1 and nothing >= 1
    writing = leftover_of_outcome(between, Change(Kind.IDENTIFY, "", 0, 1))
    assert writing == leftover_merge(0, 1)


def test_tagged_perform_records_the_incoming_leftover() -> None:
    start = tagged_start()
    nxt = tagged_perform(start, Change(Kind.ADD_TERM))
    assert nxt.state == DState.of(1, [], []) and nxt.leftover == leftover_nothing()
    two = Tagged(DState.of(2, [(0, 1)], []), leftover_nothing())
    merged = tagged_perform(two, Change(Kind.IDENTIFY, "", 0, 1))
    # The canonical tag keeps the surviving term alone (the other is gone).
    assert merged.leftover == leftover_merge_survivor(0) and merged.state.n == 1
    assert leftover_counts(DState.of(2, [(0, 1)], []))[3] >= 1
    assert any(c.kind is Kind.IDENTIFY for c in changes(DState.of(2, [], [])))
