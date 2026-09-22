"""Changes of the tenth seed: the ninth's four kinds, each with a leftover outcome.

Given by the tenth seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  After every change, record what that
    change leaves.

Cited from the ninth derivation (`ninth.changes`) and re-checked
    The list of changes, `perform`, `Kind`, `is_addition` and
    `attempt_counts` mention no leftover: they survive and are imported.
    Every change of the ninth is a change of the tenth, and conversely.

Derived (paper, `lean4/Tenth/`)
    The three leftover outcomes split the ninth's changes: additions leave
    nothing; removals leave a clearable leftover; identifications leave a
    leftover that is clearable or uncleared according as a later change
    restores the start.  A leftover of a removal in one relation is not
    cleared by a change of the other.
"""

from __future__ import annotations

from ninth.changes import (
    KINDS,
    Change,
    Kind,
    attempt_counts,
    changes,
    first_changes,
    is_addition,
    is_change,
    makes_some_loop,
    perform,
)

from ninth.state import same

from tenth.leftover import LeftOver, leftover_of, other_relation
from tenth.state import DState, Tagged, canonical

__all__ = [
    "KINDS",
    "Change",
    "Kind",
    "attempt_counts",
    "changes",
    "first_changes",
    "is_addition",
    "is_change",
    "leftover_counts",
    "makes_some_loop",
    "other_clears",
    "perform",
    "tagged_perform",
]


def leftover_counts(state: DState) -> tuple[int, int, int, int]:
    """How many changes `state` has, and how many of each leftover outcome."""
    listed = changes(state)
    nothing = clearable = uncleared = 0
    for change in listed:
        outcome = leftover_of(state, change)
        if outcome is LeftOver.NOTHING_LEFT:
            nothing += 1
        elif outcome is LeftOver.CLEARABLE:
            clearable += 1
        else:
            uncleared += 1
    return len(listed), nothing, clearable, uncleared


def other_clears(state: DState, change: Change) -> bool:
    """Would a change of the other relation restore `state` after this removal?

    `False` when `change` is not a removal, and when no later change of the
    other relation restores `state`.
    """
    if change.kind is not Kind.REMOVE:
        return False
    out = perform(state, change)
    other = other_relation(change.rel)
    for later in changes(out):
        if later.kind is Kind.ADD_ASSERTION and later.rel == other and same(perform(out, later), state):
            return True
    return False


def tagged_perform(tagged: Tagged, change: Change) -> Tagged:
    """Perform `change` on a tagged state: the leftover of this change becomes the tag."""
    out = canonical(perform(tagged.state, change))
    return Tagged(out, leftover_of(tagged.state, change))
