"""Statements about admission records, and witnesses that they do not follow.

Computed.  A statement about a *result* does not follow when some reached
result satisfies it and some reached result violates it.  The ninth's
statements about states are imported and re-checked: admission is not in the
state, so their verdicts are the ninth's.

Cited from the ninth derivation (`ninth.follows`) and re-checked
    Every statement about a two-relation state mentions no admission: the
    verdicts survive.  No tested statement holds in every result (9:D14).
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from ninth.follows import (
    EXTRA_NINTH,
    JOINT,
    ONE_RELATION,
    STATEMENTS,
    Statement,
    Statement8,
    Verdict,
    nothing_at_all,
    unchanged_by_exchange,
    verdict,
)
from ninth.follows import verdicts as verdicts_ninth

from fifteenth.admission import Admission
from fifteenth.explore import Exploration

__all__ = [
    "EXTRA_NINTH",
    "JOINT",
    "ADMISSION_STATEMENTS",
    "ONE_RELATION",
    "STATEMENTS",
    "Statement",
    "Statement8",
    "Verdict",
    "AdmissionVerdict",
    "is_admitted",
    "is_assertion_record",
    "is_not_admitted",
    "can_be_admitted",
    "admission_verdicts",
    "nothing_at_all",
    "unchanged_by_exchange",
    "verdict",
    "verdicts",
]


def is_not_admitted(record: Admission) -> bool:
    """Reaching left the result not admitted."""
    return not record.admitted


def is_admitted(record: Admission) -> bool:
    """The result is admitted."""
    return record.admitted


def is_assertion_record(record: Admission) -> bool:
    """The admission record is an assertion of `r` or of `s`."""
    return record.is_assertion()


def can_be_admitted(record: Admission) -> bool:
    """The reached result can be admitted.  Independent of the record reaching left."""
    del record
    return True


ADMISSION_STATEMENTS: tuple[tuple[str, Callable[[Admission], bool]], ...] = (
    ("is_not_admitted", is_not_admitted),
    ("is_admitted", is_admitted),
    ("is_assertion_record", is_assertion_record),
    ("can_be_admitted", can_be_admitted),
)


@dataclass(frozen=True)
class AdmissionVerdict:
    """Where an admission statement first holds and first fails among reached results."""

    name: str
    holds_at: str | None
    fails_at: str | None

    @property
    def follows(self) -> bool:
        """Does the statement hold of every reached result in the exploration?"""
        return self.fails_at is None and self.holds_at is not None


def verdicts(expl: Exploration) -> tuple[Verdict, ...]:
    """The ninth's state-statements, on this exploration (C-A1: the same results)."""
    from ninth.explore import Exploration as NinthExploration

    ninth = NinthExploration(
        start=expl.start,
        bound=expl.bound,
        rounds=expl.rounds,
        depth=expl.depth,
        new_per_round=expl.new_per_round,
        attempts_per_round=expl.attempts_per_round,
        xrx_per_round=expl.xrx_per_round,
        xsx_per_round=expl.xsx_per_round,
        frontier=expl.frontier,
        log=[],
    )
    return verdicts_ninth(ninth)


def admission_verdicts(expl: Exploration) -> tuple[AdmissionVerdict, ...]:
    """For each admission statement, the earliest result where it holds and where it fails."""
    from fifteenth.admission import admission_of_reaching
    from fifteenth.explore import order

    found: dict[str, list[str | None]] = {name: [None, None] for name, _ in ADMISSION_STATEMENTS}
    for state in sorted(expl.depth, key=order):
        record = admission_of_reaching(state)
        written_state = state.key()
        for name, pred in ADMISSION_STATEMENTS:
            slot = 0 if pred(record) else 1
            if found[name][slot] is None:
                found[name][slot] = written_state
    return tuple(AdmissionVerdict(name, found[name][0], found[name][1]) for name, _ in ADMISSION_STATEMENTS)
