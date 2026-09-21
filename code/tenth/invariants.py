"""Checks that leftover outcomes split the ninth's changes as declared.

Derived (paper, `lean4/Tenth/`)
    Every performed change has exactly one leftover outcome.  Additions leave
    nothing.  Removals leave a clearable leftover, cleared by adding that
    assertion and not by a change of the other relation.  Identifications
    leave a leftover that is clearable exactly when a later change restores
    the start.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ninth.changes import Kind, is_addition
from ninth.state import same

from tenth.changes import other_clears, perform
from tenth.explore import Exploration, leftover_performed
from tenth.leftover import LeftOver, clearing_change, leftover_of, restores_in_one

__all__ = ["LeftoverCheck", "check_leftovers"]


@dataclass
class LeftoverCheck:
    """What `check_leftovers` records.  Disagreement lists are empty on correct code."""

    checked: int = 0
    nothing_left: int = 0
    clearable: int = 0
    uncleared: int = 0
    additions_not_nothing: list[str] = field(default_factory=list)
    removals_not_clearable: list[str] = field(default_factory=list)
    other_relation_cleared: list[str] = field(default_factory=list)
    identify_disagreements: list[str] = field(default_factory=list)
    clearing_failed: list[str] = field(default_factory=list)


def check_leftovers(expl: Exploration) -> LeftoverCheck:
    """Classify every performed change within the bound and record disagreements."""
    out = LeftoverCheck()
    for state, change, arrived, leftover in leftover_performed(expl):
        del arrived
        out.checked += 1
        written = f"{state.key()} {change.written(state)}"
        if leftover is LeftOver.NOTHING_LEFT:
            out.nothing_left += 1
        elif leftover is LeftOver.CLEARABLE:
            out.clearable += 1
        else:
            out.uncleared += 1
        if is_addition(change) and leftover is not LeftOver.NOTHING_LEFT:
            out.additions_not_nothing.append(written)
        if change.kind is Kind.REMOVE:
            if leftover is not LeftOver.CLEARABLE:
                out.removals_not_clearable.append(written)
            later = clearing_change(change)
            if later is None or not same(perform(perform(state, change), later), state):
                out.clearing_failed.append(written)
            if other_clears(state, change):
                out.other_relation_cleared.append(written)
        if change.kind is Kind.IDENTIFY:
            expected = LeftOver.CLEARABLE if restores_in_one(state, change) else LeftOver.UNCLEARED
            if leftover is not expected:
                out.identify_disagreements.append(written)
            if leftover_of(state, change) is not leftover:
                out.identify_disagreements.append(written)
    return out
