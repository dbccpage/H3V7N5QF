"""Changes of the eleventh seed: the ninth's four kinds; writing is not a change.

Given by the eleventh seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  A writing of terms may give two
    terms the same letter while they remain two terms — that is not a
    change.

Cited from the ninth derivation (`ninth.changes`) and re-checked
    The list of changes, `perform`, `Kind`, `is_addition` and
    `attempt_counts` mention no writing: they survive and are imported.
    Every change of the ninth is a change of the eleventh, and conversely.
    Identifying two terms drops a term; writing them the same does not.
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

from eleventh.state import DState, Labeled, canonical
from eleventh.writing import writing_orbits

__all__ = [
    "KINDS",
    "Change",
    "Kind",
    "attempt_counts",
    "changes",
    "first_changes",
    "is_addition",
    "is_change",
    "labeled_of",
    "makes_some_loop",
    "perform",
]


def labeled_of(state: DState) -> tuple[Labeled, ...]:
    """Each distinct writing of `state`, as a labeled result (C-W2).

    Writings that an automorphism of the state carries onto each other label
    the same result (they differ only in how the terms are written), so it is
    the orbits of the writings under the state's automorphisms, not every
    restricted-growth string, that count.  At two terms every writing is its
    own orbit, so this agrees with the earlier per-writing reading there.
    """
    c = canonical(state)
    return tuple(Labeled(c, w) for w in writing_orbits(c))
