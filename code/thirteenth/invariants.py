"""Checks that coarser writings behave as declared.

Derived (paper, `lean4/Thirteenth/`)
    The coarser writing is the sum of the two relations.  Exchanging the
    relations keeps it.  It determines the finer one exactly when nothing is
    asserted.  Adding in `r` and adding in `s` land on the same coarser
    writing.  The size of the coarser writing equals the size of the finer
    state.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ninth.changes import Change, Kind, perform

from thirteenth.coarse import (
    add_r_or_s_same_coarser,
    coarse,
    determines,
    same_coarser,
    splits,
    swap_keeps_coarse,
)
from ninth.state import same, swap

from thirteenth.explore import Exploration

__all__ = ["CoarseCheck", "check_coarses"]


@dataclass
class CoarseCheck:
    """What `check_coarses` records.  Disagreement lists are empty on correct code."""

    checked: int = 0
    determines_count: int = 0
    not_determines_count: int = 0
    swap_collapses: int = 0
    add_r_s_same: int = 0
    not_sum: list[str] = field(default_factory=list)
    not_size: list[str] = field(default_factory=list)
    not_swap: list[str] = field(default_factory=list)
    determines_when_asserted: list[str] = field(default_factory=list)
    not_determines_when_empty: list[str] = field(default_factory=list)
    splits_mismatch: list[str] = field(default_factory=list)
    add_r_s_fail: list[str] = field(default_factory=list)


def check_coarses(expl: Exploration) -> CoarseCheck:
    """Classify every explored result and record disagreements."""
    out = CoarseCheck()
    for state in expl.depth:
        out.checked += 1
        written = state.key()
        summed = coarse(state)
        expected = tuple(a + b for a, b in zip(state.r, state.s))
        if summed.mult != expected:
            out.not_sum.append(written)
        if summed.size != state.size:
            out.not_size.append(written)
        if not swap_keeps_coarse(state):
            out.not_swap.append(written)
        if determines(state):
            out.determines_count += 1
            if state.m != 0:
                out.determines_when_asserted.append(written)
        else:
            out.not_determines_count += 1
            if state.m == 0:
                out.not_determines_when_empty.append(written)
        if splits(state) != _splits_of(state):
            out.splits_mismatch.append(written)
        if not same(state, swap(state)) and same_coarser(state, swap(state)):
            out.swap_collapses += 1
        if state.n >= 1:
            if add_r_or_s_same_coarser(state, 0, 0):
                out.add_r_s_same += 1
            else:
                added_r = perform(state, Change(Kind.ADD_ASSERTION, "r", 0, 0))
                added_s = perform(state, Change(Kind.ADD_ASSERTION, "s", 0, 0))
                if same_coarser(added_r, added_s) is False:
                    out.add_r_s_fail.append(written)
    return out


def _splits_of(state: object) -> int:
    """Independent product of (N + 1) per pair, for the injection test to disagree."""
    from ninth.state import DState

    if not isinstance(state, DState):
        return -1
    n = 1
    for a, b in zip(state.r, state.s):
        n *= a + b + 1
    return n
