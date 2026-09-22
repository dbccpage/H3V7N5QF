"""Checks that admission records behave as declared.

Derived (paper, `lean4/Fifteenth/`)
    Reaching a result does not admit it.  Every reached result can be
    admitted.  Admission is not an assertion of `r` or of `s` and is not one
    of the four kinds.  Admission of a result with something in `r` only is
    the same record as admission of a result with something in `s` only.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ninth.state import swap

from fifteenth.admission import (
    admission_is_a_kind,
    admission_of_reaching,
    can_admit,
    other_relation,
)
from fifteenth.explore import Exploration, admission_performed

__all__ = ["AdmissionCheck", "check_admissions"]


@dataclass
class AdmissionCheck:
    """What `check_admissions` records.  Disagreement lists are empty on correct code."""

    checked: int = 0
    not_admitted: int = 0
    admitted: int = 0
    reaching_admits: list[str] = field(default_factory=list)
    cannot_admit: list[str] = field(default_factory=list)
    assertion_records: list[str] = field(default_factory=list)
    kind_records: list[str] = field(default_factory=list)
    of_relation: list[str] = field(default_factory=list)
    cross_relation_disagree: list[str] = field(default_factory=list)


def check_admissions(expl: Exploration) -> AdmissionCheck:
    """Classify every reached outcome within the bound and record disagreements."""
    out = AdmissionCheck()
    for state, change, arrived, record in admission_performed(expl):
        out.checked += 1
        written = f"{state.key()} {change.written(state)}"
        if record.admitted:
            out.admitted += 1
            out.reaching_admits.append(written)
        else:
            out.not_admitted += 1
        if not can_admit(arrived):
            out.cannot_admit.append(written)
        if record.is_assertion():
            out.assertion_records.append(written)
        if admission_is_a_kind(record):
            out.kind_records.append(written)
        if record.is_of_relation(change.rel or "r") or record.is_of_relation(other_relation(change.rel) if change.rel else "s"):
            out.of_relation.append(written)
        # D5: admission names no relation, so the record of a result is the
        # record of its r/s exchange.  Comparing the result with its own swap
        # (not a value against a copy of itself) is a real check: a
        # relation-dependent record makes an asymmetric result disagree.
        if admission_of_reaching(arrived) != admission_of_reaching(swap(arrived)):
            out.cross_relation_disagree.append(written)
    return out
