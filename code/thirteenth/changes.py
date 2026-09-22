"""Changes of the thirteenth seed: the ninth's four kinds, each result with a coarser writing.

Given by the thirteenth seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  A coarser writing of an assertion
    forgets whether it was written with `r` or with `s`.

Cited from the ninth derivation (`ninth.changes`) and re-checked
    The list of changes, `perform`, `Kind`, `is_addition` and
    `attempt_counts` mention no coarser writing: they survive and are
    imported.  Every change of the ninth is a change of the thirteenth, and
    conversely.
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

from thirteenth.coarse import coarse

__all__ = [
    "KINDS",
    "Change",
    "Kind",
    "attempt_counts",
    "changes",
    "coarse_of_outcome",
    "first_changes",
    "is_addition",
    "is_change",
    "makes_some_loop",
    "perform",
]


def coarse_of_outcome(state: object, change: Change) -> object:
    """The coarser writing of `perform(state, change)`."""
    from ninth.state import DState

    if not isinstance(state, DState):
        raise TypeError("a coarser writing is of a two-relation state")
    return coarse(perform(state, change))
