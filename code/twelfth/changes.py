"""Changes of the twelfth seed: the ninth's four kinds, each identification with a record.

Given by the twelfth seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  Identifying two terms records, for
    each relation, which assertions of those two terms become one assertion.

Cited from the ninth derivation (`ninth.changes`) and re-checked
    The list of changes, `perform`, `Kind`, `is_addition` and
    `attempt_counts` mention no record: they survive and are imported.
    Every change of the ninth is a change of the twelfth, and conversely.
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

from twelfth.record import IdentRecord, record_of
from twelfth.state import Recorded, canonical

__all__ = [
    "KINDS",
    "Change",
    "Kind",
    "attempt_counts",
    "changes",
    "first_changes",
    "is_addition",
    "is_change",
    "makes_some_loop",
    "perform",
    "record_of_change",
    "recorded_perform",
]


def record_of_change(state: object, change: Change) -> IdentRecord | None:
    """The identification record of `change` on `state`, or `None` when it is not an identification."""
    from ninth.state import DState

    if change.kind is not Kind.IDENTIFY:
        return None
    if not isinstance(state, DState):
        raise TypeError("a record is of a two-relation state")
    return record_of(state, change.x, change.y)


def recorded_perform(recorded: Recorded, change: Change) -> Recorded:
    """The C-M2 outcome: identifications attach a new record; other kinds keep it."""
    out = canonical(perform(recorded.state, change))
    if change.kind is Kind.IDENTIFY:
        rec = record_of(recorded.state, change.x, change.y)
        return Recorded(out, rec)
    return Recorded(out, recorded.record)
