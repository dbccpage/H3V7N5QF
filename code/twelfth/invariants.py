"""Checks that identification records behave as declared.

Derived (paper, `lean4/Twelfth/`)
    The record of one relation is determined by that relation.  The two
    records can differ.  A non-empty record is not restored by any one
    later change; an empty record of two isolated terms is restored by
    adding a term.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ninth.changes import Kind

from twelfth.explore import Exploration, performed
from twelfth.record import (
    became_one,
    record_determined_by_rel,
    record_of,
    restores_listed,
)
from twelfth.state import swap

__all__ = ["RecordCheck", "check_records"]


@dataclass
class RecordCheck:
    """What `check_records` records.  Disagreement lists are empty on correct code."""

    checked: int = 0
    identifications: int = 0
    empty_records: int = 0
    nonempty_records: int = 0
    differs: int = 0
    restored_empty: int = 0
    r_not_s: int = 0
    not_determined_by_rel: list[str] = field(default_factory=list)
    nonempty_restored: list[str] = field(default_factory=list)
    empty_not_restored_isolated: list[str] = field(default_factory=list)
    swap_mismatch: list[str] = field(default_factory=list)


def check_records(expl: Exploration) -> RecordCheck:
    """Classify every identification of every explored result and record disagreements."""
    out = RecordCheck()
    for state, change, _outcome in performed(expl):
        if change.kind is not Kind.IDENTIFY:
            continue
        out.checked += 1
        out.identifications += 1
        rec = record_of(state, change.x, change.y)
        written = f"{state.key()} identify {change.x},{change.y}"
        if rec.is_empty():
            out.empty_records += 1
        else:
            out.nonempty_records += 1
        if rec.r != rec.s:
            out.differs += 1
            out.r_not_s += 1
        if not record_determined_by_rel(state, "r", change.x, change.y):
            out.not_determined_by_rel.append(written)
        if not record_determined_by_rel(state, "s", change.x, change.y):
            out.not_determined_by_rel.append(written + " s")
        restored = restores_listed(state, change)
        if rec.is_empty() and state.n == 2 and state.size == 2:
            if restored:
                out.restored_empty += 1
            else:
                out.empty_not_restored_isolated.append(written)
        merged_or_between = (
            became_one(rec.r)
            or became_one(rec.s)
            or "xy" in rec.r.loop
            or "yx" in rec.r.loop
            or "xy" in rec.s.loop
            or "yx" in rec.s.loop
        )
        if merged_or_between and restored:
            out.nonempty_restored.append(written)
        swapped = record_of(swap(state), change.x, change.y)
        if swapped != rec.swapped():
            out.swap_mismatch.append(written)
    return out
