"""Checks that leftover writings behave as declared.

Derived (paper, `lean4/Fourteenth/`)
    Every performed change has a leftover written neither `xry` nor `xsy`.
    Additions leave nothing.  Removals leave a pair with no relation, so
    leftover of a removal in `r` equals leftover of a removal in `s` of the
    same pair.  Identifications leave a merge.  Leftover is not an assertion
    and not an answer.  Clearing leftover is not one of the four kinds.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ninth.changes import Change, Kind, is_addition

from fourteenth.explore import Exploration, leftover_performed
from fourteenth.leftover import clearing_is_a_kind, leftover_of

__all__ = ["LeftoverCheck", "check_leftovers"]


@dataclass
class LeftoverCheck:
    """What `check_leftovers` records.  Disagreement lists are empty on correct code."""

    checked: int = 0
    nothing: int = 0
    pair: int = 0
    merge: int = 0
    additions_not_nothing: list[str] = field(default_factory=list)
    removals_not_pair: list[str] = field(default_factory=list)
    identify_not_merge: list[str] = field(default_factory=list)
    assertion_writings: list[str] = field(default_factory=list)
    answer_writings: list[str] = field(default_factory=list)
    clearing_kind: list[str] = field(default_factory=list)
    cross_relation_disagree: list[str] = field(default_factory=list)


def check_leftovers(expl: Exploration) -> LeftoverCheck:
    """Classify every performed change within the bound and record disagreements."""
    out = LeftoverCheck()
    for state, change, arrived, writing in leftover_performed(expl):
        del arrived
        out.checked += 1
        written = f"{state.key()} {change.written(state)}"
        if writing.kind == "nothing":
            out.nothing += 1
        elif writing.kind == "pair":
            out.pair += 1
        else:
            out.merge += 1
        if is_addition(change) and writing.kind != "nothing":
            out.additions_not_nothing.append(written)
        if change.kind is Kind.REMOVE:
            if writing.kind != "pair" or writing.x != change.x or writing.y != change.y:
                out.removals_not_pair.append(written)
            # D5, checked only where both removals are legal changes: removing
            # the pair in the other relation leaves the same writing (the pair
            # names no relation).  Guarded by `has`, so it compares two real
            # changes rather than a change against a non-change.
            other_rel = "s" if change.rel == "r" else "r"
            if state.has(other_rel, change.x, change.y):
                other = Change(Kind.REMOVE, other_rel, change.x, change.y)
                if leftover_of(state, other) != leftover_of(state, change):
                    out.cross_relation_disagree.append(written)
        if change.kind is Kind.IDENTIFY and (writing.kind != "merge" or leftover_of(state, change) != writing):
            out.identify_not_merge.append(written)
        if writing.is_assertion():
            out.assertion_writings.append(written)
        if writing.is_answer():
            out.answer_writings.append(written)
        if clearing_is_a_kind(writing):
            out.clearing_kind.append(written)
    return out
