"""Changes of the fifteenth seed: the ninth's four kinds, each reaching a not-admitted result.

Given by the fifteenth seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  A result of the changes is reached.
    Reaching a result does not make it admitted.

Cited from the ninth derivation (`ninth.changes`) and re-checked
    The list of changes, `perform`, `Kind`, `is_addition` and
    `attempt_counts` mention no admission: they survive and are imported.
    Every change of the ninth is a change of the fifteenth, and conversely.

Derived (paper, `lean4/Fifteenth/`)
    Reaching leaves not-admitted.  Every reached result can be admitted.
    Admission is not an assertion and not a change of the four kinds.
    Admission of one relation does not constrain the other.
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

from fifteenth.admission import Admission, admitted_record, admission_of_reaching, not_admitted_record
from fifteenth.state import DState, Tagged, canonical

__all__ = [
    "KINDS",
    "Change",
    "Kind",
    "attempt_counts",
    "changes",
    "first_changes",
    "is_addition",
    "is_change",
    "admission_counts",
    "makes_some_loop",
    "perform",
    "tagged_admit",
    "tagged_perform",
]


def admission_counts(state: DState) -> tuple[int, int, int]:
    """How many changes `state` has, how many outcomes reaching admits, how many it does not.

    Reaching never admits, so the second figure is 0 and the third is the number of changes.
    """
    listed = changes(state)
    admitted = 0
    refused = 0
    for change in listed:
        del change
        record = admission_of_reaching(state)
        if record.admitted:
            admitted += 1
        else:
            refused += 1
    return len(listed), admitted, refused


def tagged_perform(tagged: Tagged, change: Change) -> Tagged:
    """Perform `change` on a tagged state: reaching leaves the outcome not admitted."""
    out = canonical(perform(tagged.state, change))
    return Tagged(out, not_admitted_record())


def tagged_admit(tagged: Tagged) -> Tagged:
    """Record admission of the same ninth state (C-A2; not a change of the four kinds)."""
    return Tagged(tagged.state, admitted_record())


def admission_of_outcome(state: DState, change: Change) -> Admission:
    """The admission record of the outcome of `change` on `state` (C-A1)."""
    del change
    return admission_of_reaching(state)
