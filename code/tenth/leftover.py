"""Leftover outcomes of a change of the tenth seed.

Given by the tenth seed
    After every change, record what that change leaves.  A leftover is not
    an assertion.  Nothing left, a leftover that a later change of the four
    kinds can clear, and a leftover that none of them can, are three
    outcomes.  Declare which, for every change.

Chosen here (reading C-L1 of the paper)
    Leftover is recorded on the change, not as a field of the result.  The
    leftover of a change from `S` to `T` is:

    * an addition (a term, or an assertion of either relation): nothing
      left — the added thing is a term or an assertion;
    * a removal: a leftover that adding that same assertion clears;
    * an identification: a leftover that a later change can clear if some
      one change of the four kinds on `T` restores `S` (up to writing), and
      a leftover that none of them can otherwise.

Cited from the ninth derivation (`ninth.changes`, `ninth.state`) and re-checked
    `perform`, `changes`, `Kind` and `same` mention no leftover: they survive
    and are imported.  Leftover is not a third multiplicity beside `r` and
    `s` (the state is the ninth's).
"""

from __future__ import annotations

from enum import Enum

from ninth.changes import Change, Kind, changes, is_addition, perform
from ninth.state import DState, same

__all__ = [
    "LeftOver",
    "clearing_change",
    "leftover_of",
    "other_relation",
    "restores_in_one",
]


class LeftOver(Enum):
    """The three leftover outcomes the seed names, in the seed's order."""

    NOTHING_LEFT = "nothing left"
    CLEARABLE = "a leftover that a later change of the four kinds can clear"
    UNCLEARED = "a leftover that none of them can"

    def __str__(self) -> str:
        return self.value


def other_relation(rel: str) -> str:
    """The other of the two relations."""
    if rel == "r":
        return "s"
    if rel == "s":
        return "r"
    raise ValueError("an assertion is written with r or with s")


def clearing_change(change: Change) -> Change | None:
    """The later change that restores a removal: adding that same assertion.

    `None` when `change` is not a removal.
    """
    if change.kind is Kind.REMOVE:
        return Change(Kind.ADD_ASSERTION, change.rel, change.x, change.y)
    return None


def restores_in_one(state: DState, change: Change) -> bool:
    """Does some one later change of the four kinds restore `state` (up to writing)?"""
    out = perform(state, change)
    return any(same(perform(out, later), state) for later in changes(out))


def leftover_of(state: DState, change: Change) -> LeftOver:
    """Which of the three outcomes `change` on `state` has (C-L1)."""
    if is_addition(change):
        return LeftOver.NOTHING_LEFT
    if change.kind is Kind.REMOVE:
        later = clearing_change(change)
        if later is None:  # pragma: no cover
            raise RuntimeError("a removal has a clearing change")
        if not same(perform(perform(state, change), later), state):  # pragma: no cover
            raise RuntimeError("adding the removed assertion did not restore the state")
        return LeftOver.CLEARABLE
    if change.kind is Kind.IDENTIFY:
        if restores_in_one(state, change):
            return LeftOver.CLEARABLE
        return LeftOver.UNCLEARED
    raise ValueError("nothing else is a change")  # pragma: no cover
