"""The twenty-third mapped in, the map back, and what forgetting the filled triples loses.

Derived (paper, D10; `lean4_core/Twentyfifth/Map.lean`, `Rename.lean`)
    * The twenty-third maps one to one: its states read with nothing filled
      (`embed`) are one result here exactly when they are one result there,
      and each of its changes is carried to the same change.  So its results
      within a bound are exactly the results here with nothing filled, at the
      same rounds (`compare_twentythird`).
    * The seventh's pair and the first seed's pair, merged by the twenty-third
      (23:D9), stay merged: the other seeds of the line do not map one to one
      (`seventh_pairs_merged`).
    * The map back (`read_back`): the twenty-third result of a result with
      nothing filled, "none" otherwise.  On a mapped result it returns the
      original; the first result it answers "none" on is `a b c` with one triple
      filled, at round four (`smallest_none`).
    * Forgetting the filled triples maps results here to twenty-third results;
      how many results here each twenty-third result gathers is counted
      (`forget_fibres`).
"""

from __future__ import annotations

from dataclasses import dataclass

from twentythird.embed import first_pair, seventh_pair
from twentythird.explore import Grouped as Grouped23
from twentythird.state import Key, of_r, result_key

from twentyfifth.explore import Grouped
from twentyfifth.state import FState, Mark, embed, result_mark

__all__ = [
    "EmbedReport",
    "compare_twentythird",
    "forget_fibres",
    "read_back",
    "read_back_of_mark",
    "seventh_pairs_merged",
    "smallest_none",
]


def read_back(fs: FState) -> Key | None:
    """The map back: the twenty-third result of a result with nothing filled; `None` ("none") otherwise."""
    if fs.filled:
        return None
    return result_key(fs.state)


def read_back_of_mark(mark: Mark) -> Key | None:
    """The map back read from a result's mark: its excess table when nothing is filled."""
    n, table, filled = mark
    return None if filled else (n, table)


def smallest_none(grouped: Grouped) -> Mark | None:
    """The first result, in round then fixed order, that the map back answers "none" on."""
    for mark in grouped.ordered_marks():
        if read_back(grouped.representative(mark)) is None:
            return mark
    return None


@dataclass(frozen=True)
class EmbedReport:
    """The twenty-third's results against the results here with nothing filled."""

    twentythird_results: int
    results_with_nothing_filled: int
    missing_here: int
    extra_here: int
    rounds_differing: int
    returned_the_original: int


def compare_twentythird(grouped: Grouped, grouped23: Grouped23) -> EmbedReport:
    """The twenty-third's exploration at the same bound, mapped in, against the results with nothing filled."""
    ours: dict[Key, int] = {(m[0], m[1]): r for m, r in grouped.round_of.items() if not m[2]}
    theirs = dict(grouped23.round_of)
    returned = 0
    for key in theirs:
        rep = grouped23.representative(key)
        if read_back_of_mark(result_mark(embed(rep))) == key:
            returned += 1
    return EmbedReport(
        twentythird_results=len(theirs),
        results_with_nothing_filled=len(ours),
        missing_here=len(set(theirs) - set(ours)),
        extra_here=len(set(ours) - set(theirs)),
        rounds_differing=sum(1 for k in set(ours) & set(theirs) if ours[k] != theirs[k]),
        returned_the_original=returned,
    )


def seventh_pairs_merged() -> tuple[bool, bool]:
    """The seventh's pair and the first seed's pair, embedded with nothing filled: one result each?"""
    a, b = seventh_pair()
    c, d = first_pair()
    return (
        result_mark(embed(of_r(a))) == result_mark(embed(of_r(b))),
        result_mark(embed(of_r(c))) == result_mark(embed(of_r(d))),
    )


def forget_fibres(grouped: Grouped) -> dict[Key, int]:
    """For every twenty-third result reached, how many results here forget their filled triples onto it."""
    out: dict[Key, int] = {}
    for mark in grouped.round_of:
        key = result_key(grouped.representative(mark).state)
        out[key] = out.get(key, 0) + 1
    return out
