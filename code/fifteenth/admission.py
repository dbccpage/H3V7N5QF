"""Admission records of a result of the fifteenth seed.

Given by the fifteenth seed
    A result of the changes is reached.  Whether it is admitted is not given
    by the reaching.  Record for every result whether it is admitted.
    Reaching a result does not make it admitted.

Chosen here (reading C-A1 of the paper)
    Admission is recorded with the result as extra data, not as a field of
    the two-relation state.  Reaching leaves the record as not-admitted.
    Every reached result can be admitted by a record that is not a change of
    the four kinds.  Admission names no relation.

Cited from the ninth derivation (`ninth.changes`, `ninth.state`) and re-checked
    `perform`, `changes`, `Kind` and `same` mention no admission: they survive
    and are imported.  Admission is not a third multiplicity beside `r` and
    `s` (the state is the ninth's).
"""

from __future__ import annotations

from dataclasses import dataclass

__all__ = [
    "Admission",
    "admission_is_a_kind",
    "admission_of_reaching",
    "admitted_record",
    "can_admit",
    "not_admitted_record",
    "other_relation",
]


@dataclass(frozen=True)
class Admission:
    """Whether a result is admitted: neither `xry` nor `xsy`."""

    admitted: bool

    def written(self) -> str:
        """The admission record in letters.  Never `xry` and never `xsy`."""
        return "admitted" if self.admitted else "not-admitted"

    def is_xry(self) -> bool:
        """Is this admission written `xry`?  Never: admission uses neither `r` nor `s`."""
        return self.admitted and "r" in self.written()

    def is_xsy(self) -> bool:
        """Is this admission written `xsy`?  Never."""
        return (not self.admitted) and "s" in self.written()

    def is_assertion(self) -> bool:
        """Is admission an assertion?  The seed records it of a result, not as `xry` or `xsy`."""
        return self.is_xry() or self.is_xsy()

    def is_change(self) -> bool:
        """Is admitting one of the four kinds?  The seed says nothing else is a change."""
        return False

    def is_of_relation(self, rel: str) -> bool:
        """Is admission of one relation?  Never: the record names no relation."""
        del rel
        return False

    def __str__(self) -> str:
        return self.written()


def not_admitted_record() -> Admission:
    """The admission record that reaching leaves: not admitted."""
    return Admission(False)


def admitted_record() -> Admission:
    """The admission record that can be assigned independently of reaching."""
    return Admission(True)


def other_relation(rel: str) -> str:
    """The other of the two relations."""
    if rel == "r":
        return "s"
    if rel == "s":
        return "r"
    raise ValueError("an assertion is written with r or with s")


def admission_of_reaching(_state: object) -> Admission:
    """Which admission record reaching leaves (C-A1).  Reaching does not admit."""
    return not_admitted_record()


def can_admit(_state: object) -> bool:
    """Can this reached result be admitted?  Yes: admission is not given by the reaching."""
    return True


def admission_is_a_kind(record: Admission) -> bool:
    """Is admitting an object of one of the four kinds?  Never: admission is not a term and not an assertion."""
    return record.is_change()
