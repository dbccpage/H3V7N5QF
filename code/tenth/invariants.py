"""Checks that leftover outcomes split the ninth's changes as declared.

Derived (paper, `lean4/Tenth/`)
    Every performed change has exactly one leftover outcome.  Additions leave
    nothing.  Removals leave a clearable leftover, cleared by adding that
    assertion and not by a change of the other relation.  Identifications
    leave a leftover that is clearable exactly when a later change restores
    the start.

Derived (paper D8), and checked here independently of `leftover_of`
    An identification is restored by one later change exactly when one of
    the two identified terms is bare: in no assertion of either relation, as
    either term of the pair.  One change back to the start's number of terms
    must add a term, and an added term is bare, so the start must be the
    outcome plus one bare term.  Identifying two terms that are not bare
    keeps the count of bare terms, and adding one raises it, so no one
    change restores the start; identifying a bare term into another leaves
    the other's assertions as they were, and adding a bare term restores the
    start.  `bare_criterion` computes that from the start alone, without
    performing any change, and `check_leftovers` compares it with the
    search `leftover_of` makes.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ninth.changes import Change, Kind, is_addition
from ninth.state import DState, same

from tenth.changes import other_clears, perform
from tenth.explore import Exploration, leftover_performed
from tenth.leftover import LeftOver, clearing_change

__all__ = ["LeftoverCheck", "bare", "bare_criterion", "check_leftovers"]


def bare(state: DState, t: int) -> bool:
    """Is term `t` in no assertion of either relation, as either term of the pair?"""
    n = state.n
    return all(
        mult[t * n + u] == 0 and mult[u * n + t] == 0 for mult in (state.r, state.s) for u in range(n)
    )


def bare_criterion(state: DState, change: Change) -> LeftOver:
    """The leftover of an identification by D8's criterion: clearable iff one of the two terms is bare."""
    if bare(state, change.x) or bare(state, change.y):
        return LeftOver.CLEARABLE
    return LeftOver.UNCLEARED


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
        if change.kind is Kind.IDENTIFY and leftover is not bare_criterion(state, change):
            out.identify_disagreements.append(written)
    return out
