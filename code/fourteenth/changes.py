"""Changes of the fourteenth seed: the ninth's four kinds, each with a leftover writing.

Given by the fourteenth seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  After every change, record what that
    change leaves.  A leftover is written neither `xry` nor `xsy`.

Cited from the ninth derivation (`ninth.changes`) and re-checked
    The list of changes, `perform`, `Kind`, `is_addition` and
    `attempt_counts` mention no leftover: they survive and are imported.
    Every change of the ninth is a change of the fourteenth, and conversely.

Derived (paper, `lean4/Fourteenth/`)
    Leftover of a removal ignores the relation: leftover of `xry` removed is
    leftover of `xsy` removed, both written `xℓy`.  Leftover is not an
    assertion and not an answer.  Clearing leftover is not one of the four
    kinds.
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

from fourteenth.leftover import LeftWriting, leftover_of
from fourteenth.state import DState, Tagged, canonical_tagged

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
    "perform",
    "tagged_perform",
]


def leftover_counts(state: DState) -> tuple[int, int, int, int]:
    """How many changes `state` has, and how many of each leftover writing kind."""
    listed = changes(state)
    nothing = pair = merge = 0
    for change in listed:
        writing = leftover_of(state, change)
        if writing.kind == "nothing":
            nothing += 1
        elif writing.kind == "pair":
            pair += 1
        else:
            merge += 1
    return len(listed), nothing, pair, merge


def tagged_perform(tagged: Tagged, change: Change) -> Tagged:
    """Perform `change` on a tagged state: the leftover of this change becomes the tag.

    The result state and the leftover's terms are renumbered together
    (`canonical_tagged`), so the tag names the result's own terms rather than
    the pre-change numbering.
    """
    out = perform(tagged.state, change)
    return canonical_tagged(out, leftover_of(tagged.state, change))


def leftover_of_outcome(state: DState, change: Change) -> LeftWriting:
    """The leftover writing of `change` on `state` (C-F1)."""
    return leftover_of(state, change)
