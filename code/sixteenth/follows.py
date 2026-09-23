"""Statements about a state with a record, and about a change, with witnesses that they do not follow.

Computed.  A statement about a *state* does not follow when some result
satisfies it and some result violates it; a statement about a *change* when
some performed change satisfies it and some violates it.

Cited from the ninth derivation (`ninth.follows`) and re-checked
    Every statement about a two-relation state mentions no record; each is
    read on the state part of a sixteenth state and its verdict is found
    again on the sixteenth's results.  `Verdict` is written again for states
    with a record.  No tested statement about the asserting holds in every
    result (9:D14): the empty state fails "at least one term" and every other
    fails somewhere.

Cited from the fourteenth derivation (`fourteenth.follows`) and re-checked
    The leftover statements about a change (leaves nothing; leaves a pair;
    leaves a merge; is an assertion writing) survive as statements, with the
    admission a fifth kind of performed change; new: "is an admission",
    "leaves an admissible writing".

Defined here
    Statements about the record: nothing recorded; something recorded; some
    recorded pair asserted too; every recorded pair unasserted.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from fourteenth.follows import is_assertion_writing, leaves_merge, leaves_nothing, leaves_pair
from fourteenth.leftover import LeftWriting
from ninth.follows import STATEMENTS, Statement8

from sixteenth.changes import Change16, perform16
from sixteenth.explore import Exploration16, order16, performed16
from sixteenth.leftover import admissible, leftover_of16
from sixteenth.state import RState

__all__ = [
    "CHANGE_STATEMENTS",
    "RECORD_STATEMENTS",
    "STATEMENTS16",
    "Statement16",
    "ChangeVerdict",
    "Verdict16",
    "change_verdicts",
    "every_recorded_pair_unasserted",
    "is_admission",
    "leaves_admissible",
    "nothing_recorded",
    "on_state",
    "some_recorded_pair_asserted",
    "something_recorded",
    "verdicts16",
]

Statement16 = Callable[[RState], bool]


def on_state(statement: Statement8) -> Statement16:
    """A ninth statement read on the state part of a sixteenth state."""

    def read(rs: RState) -> bool:
        return statement(rs.state)

    read.__name__ = statement.__name__
    read.__doc__ = statement.__doc__
    return read


def nothing_recorded(rs: RState) -> bool:
    """Nothing is recorded: the state is a ninth state."""
    return rs.record_empty


def something_recorded(rs: RState) -> bool:
    """Some leftover is recorded and not admitted."""
    return not rs.record_empty


def some_recorded_pair_asserted(rs: RState) -> bool:
    """Some recorded pair is also asserted, in `r` or in `s`."""
    return any(rs.state.has("r", x, y) or rs.state.has("s", x, y) for x, y in rs.recorded_pairs)


def every_recorded_pair_unasserted(rs: RState) -> bool:
    """No recorded pair is asserted in either relation (true when nothing is recorded)."""
    return not some_recorded_pair_asserted(rs)


#: Statements about the record, new to this seed.
RECORD_STATEMENTS: tuple[Statement16, ...] = (
    nothing_recorded,
    something_recorded,
    some_recorded_pair_asserted,
    every_recorded_pair_unasserted,
)

#: Every statement tested on a state: the ninth's on the state part, then the record's.
STATEMENTS16: tuple[Statement16, ...] = tuple(on_state(s) for s in STATEMENTS) + RECORD_STATEMENTS


@dataclass(frozen=True)
class Verdict16:
    """Where a statement first holds and first fails in an exploration."""

    statement: str
    wording: str
    in_given: bool
    holds_at: RState | None
    holds_round: int | None
    fails_at: RState | None
    fails_round: int | None

    @property
    def follows_within_bound(self) -> bool:
        """The statement held in every explored result."""
        return self.fails_at is None

    @property
    def independent(self) -> bool:
        """Some explored result satisfies it and some violates it."""
        return self.holds_at is not None and self.fails_at is not None


def verdicts16(expl: Exploration16) -> tuple[Verdict16, ...]:
    """Verdicts for every statement tested on a state."""
    found: list[Verdict16] = []
    ordered = sorted(expl.depth, key=lambda s: (expl.depth[s], order16(s)))
    for statement in STATEMENTS16:
        holds: RState | None = None
        fails: RState | None = None
        for rs in ordered:
            if statement(rs):
                holds = holds if holds is not None else rs
            else:
                fails = fails if fails is not None else rs
        found.append(
            Verdict16(
                statement=statement.__name__,
                wording=(statement.__doc__ or "").strip(),
                in_given=statement(expl.start),
                holds_at=holds,
                holds_round=None if holds is None else expl.depth[holds],
                fails_at=fails,
                fails_round=None if fails is None else expl.depth[fails],
            )
        )
    return tuple(found)


def is_admission(rs: RState, change: Change16, writing: LeftWriting) -> bool:
    """The change admits a recorded leftover."""
    del rs, writing
    return change.admits


def leaves_admissible(rs: RState, change: Change16, writing: LeftWriting) -> bool:
    """The change leaves a writing that may be admitted at once on its outcome (a pair writing, now recorded)."""
    return admissible(writing, perform16(rs, change))


CHANGE_STATEMENTS: tuple[tuple[str, Callable[[RState, Change16, LeftWriting], bool]], ...] = (
    ("leaves_nothing", lambda rs, c, w: leaves_nothing(w)),
    ("leaves_pair", lambda rs, c, w: leaves_pair(w)),
    ("leaves_merge", lambda rs, c, w: leaves_merge(w)),
    ("is_assertion_writing", lambda rs, c, w: is_assertion_writing(w)),
    ("is_admission", is_admission),
    ("leaves_admissible", leaves_admissible),
)


@dataclass(frozen=True)
class ChangeVerdict:
    """Where a statement about a change first holds and first fails among performed changes."""

    name: str
    holds_at: tuple[str, str] | None
    fails_at: tuple[str, str] | None

    @property
    def follows(self) -> bool:
        """Does the statement hold of every performed change in the exploration?"""
        return self.fails_at is None and self.holds_at is not None


def change_verdicts(expl: Exploration16) -> tuple[ChangeVerdict, ...]:
    """For each statement about a change, the earliest change where it holds and where it fails."""
    found: dict[str, list[tuple[str, str] | None]] = {name: [None, None] for name, _ in CHANGE_STATEMENTS}
    for rs, change, _raw, _out in performed16(expl):
        writing = leftover_of16(rs, change)
        for name, pred in CHANGE_STATEMENTS:
            slot = 0 if pred(rs, change, writing) else 1
            if found[name][slot] is None:
                found[name][slot] = (rs.key(), change.written(rs))
    return tuple(ChangeVerdict(name, found[name][0], found[name][1]) for name, _ in CHANGE_STATEMENTS)
