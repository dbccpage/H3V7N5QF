"""Statements about identification records, and witnesses that they do not follow.

Computed.  A statement about a *record of an identification* does not follow
when some identification satisfies it and some identification violates it.
The ninth's statements about states are imported and re-checked: a record
is not in the state, so their verdicts are the ninth's.

Cited from the ninth derivation (`ninth.follows`) and re-checked
    Every statement about a two-relation state mentions no record: the
    verdicts survive.  No tested statement holds in every result (9:D14).
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from ninth.changes import Change, Kind
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

from twelfth.explore import Exploration, performed
from twelfth.record import IdentRecord, became_one, record_determined_by_rel, restores_listed
from twelfth.state import DState

__all__ = [
    "EXTRA_NINTH",
    "JOINT",
    "ONE_RELATION",
    "RECORD_STATEMENTS",
    "STATEMENTS",
    "RecordVerdict",
    "Statement",
    "Statement8",
    "Verdict",
    "differs",
    "empty_record",
    "nonempty_record",
    "nothing_at_all",
    "record_verdicts",
    "unchanged_by_exchange",
    "verdict",
    "verdicts",
]


def empty_record(state: DState, change: Change, rec: IdentRecord) -> bool:
    """The identification recorded nothing asserted among the two terms."""
    del state, change
    return rec.is_empty()


def nonempty_record(state: DState, change: Change, rec: IdentRecord) -> bool:
    """The identification recorded some asserted pair among the two terms."""
    del state, change
    return not rec.is_empty()


def differs(state: DState, change: Change, rec: IdentRecord) -> bool:
    """The two relations' records of this identification differ."""
    del state, change
    return rec.r != rec.s


def r_became_one(state: DState, change: Change, rec: IdentRecord) -> bool:
    """Two or more `r` assertions of the two terms became one pair."""
    del state, change
    return became_one(rec.r)


def restored(state: DState, change: Change, rec: IdentRecord) -> bool:
    """Some one later change restores the start (what the record lists)."""
    del rec
    return restores_listed(state, change)


def determined(state: DState, change: Change, rec: IdentRecord) -> bool:
    """The `r` record is determined by the `r` projection."""
    del rec
    return record_determined_by_rel(state, "r", change.x, change.y)


RECORD_STATEMENTS: tuple[tuple[str, Callable[[DState, Change, IdentRecord], bool]], ...] = (
    ("empty_record", empty_record),
    ("nonempty_record", nonempty_record),
    ("differs", differs),
    ("r_became_one", r_became_one),
    ("restored", restored),
    ("determined", determined),
)


@dataclass(frozen=True)
class RecordVerdict:
    """Where a record statement first holds and first fails among identifications."""

    name: str
    holds_at: str | None
    fails_at: str | None

    @property
    def follows(self) -> bool:
        """Does the statement hold of every identification of every explored result?"""
        return self.fails_at is None and self.holds_at is not None


def verdicts(expl: Exploration) -> tuple[Verdict, ...]:
    """The ninth's state-statements, on this exploration (C-M1: the same results)."""
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


def record_verdicts(expl: Exploration) -> tuple[RecordVerdict, ...]:
    """For each record statement, the earliest identification where it holds and where it fails."""
    found: dict[str, list[str | None]] = {name: [None, None] for name, _ in RECORD_STATEMENTS}
    idents = [
        (state, change, record_of_ident(state, change))
        for state, change, _out in performed(expl)
        if change.kind is Kind.IDENTIFY
    ]
    idents.sort(key=lambda t: (expl.depth[t[0]], t[0].n, t[0].key(), t[1].x, t[1].y))
    for state, change, rec in idents:
        written = f"{state.key()} identify {change.x},{change.y}"
        for name, pred in RECORD_STATEMENTS:
            slot = 0 if pred(state, change, rec) else 1
            if found[name][slot] is None:
                found[name][slot] = written
    return tuple(RecordVerdict(name, found[name][0], found[name][1]) for name, _ in RECORD_STATEMENTS)


def record_of_ident(state: DState, change: Change) -> IdentRecord:
    """The record of an identification change."""
    from twelfth.record import record_of

    return record_of(state, change.x, change.y)
