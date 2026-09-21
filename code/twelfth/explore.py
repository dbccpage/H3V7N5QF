"""Attempting every change of the twelfth seed, recording identification records.

Given by the twelfth seed
    Attempt every change, fewest additions first.  Identifying two terms
    records, for each relation, which assertions of those two terms become
    one assertion.

Cited from the ninth derivation (`ninth.explore`) and re-checked
    The protocol, the bound, the frontier and the shortest-sequence counts
    mention no record: they survive and are imported.  Under C-M1 the
    exploration is the ninth's, with the record filled on every
    identification.  `cycle` is imported.  The unchosen recorded reading is
    explored afresh.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field

from ninth.explore import Exit, Exploration as NinthExploration, cycle
from ninth.explore import count_shortest_sequences as count_shortest_sequences_ninth
from ninth.explore import explore as explore_ninth
from ninth.explore import order, performed as performed_ninth, sequences_exact

from twelfth.changes import Change, Kind, changes, recorded_perform
from twelfth.record import IdentRecord, record_of
from twelfth.state import DState, Recorded, recorded_start

__all__ = [
    "Attempt",
    "Exit",
    "Exploration",
    "RecordedExploration",
    "attempt",
    "count_shortest_sequences",
    "count_shortest_sequences_ninth",
    "cycle",
    "explore",
    "explore_recorded",
    "order",
    "performed",
    "recorded_order",
    "recorded_performed",
    "sequences_exact",
]


@dataclass(frozen=True)
class Attempt:
    """One attempted change of the twelfth seed: the ninth's record plus the identification record."""

    state: DState
    change: Change
    outcome: DState | None
    beyond: bool
    xrx: bool
    xsx: bool
    record: IdentRecord | None


def attempt(state: DState, change: Change, bound: int) -> Attempt:
    """Attempt `change` on `state` and record the identification record when there is one."""
    from ninth.explore import attempt as attempt_ninth

    rec = attempt_ninth(state, change, bound)
    ident = record_of(state, change.x, change.y) if change.kind is Kind.IDENTIFY else None
    return Attempt(rec.state, rec.change, rec.outcome, rec.beyond, rec.xrx, rec.xsx, ident)


@dataclass
class Exploration:
    """The ninth's exploration with identification records filled on identifications."""

    start: DState
    bound: int
    rounds: int
    depth: dict[DState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    xrx_per_round: list[int]
    xsx_per_round: list[int]
    identifications_per_round: list[int]
    frontier: list[Exit] = field(default_factory=list)
    log: list[Attempt] = field(default_factory=list)

    @property
    def last_new_round(self) -> int:
        """The last round that produced a new result within the bound."""
        return max(r for r, new in enumerate(self.new_per_round) if new)

    @property
    def awaiting(self) -> list[DState]:
        """The results of the last round, whose changes were not attempted."""
        return sorted((s for s, r in self.depth.items() if r >= self.rounds), key=order)


def explore(start: DState, bound: int, rounds: int = 100, keep_log: bool = False) -> Exploration:
    """The ninth's exploration, identification records on every identification when the log is kept.

    Results, rounds and the frontier are the ninth's (C-M1).
    """
    base = explore_ninth(start, bound, rounds, keep_log=keep_log)
    identifications_per_round = [0 for _ in base.new_per_round]
    log = [attempt(rec.state, rec.change, bound) for rec in base.log] if keep_log else []
    if keep_log:
        for rec in log:
            if rec.record is not None:
                r = base.depth[rec.state] + 1
                identifications_per_round[r] += 1
    return Exploration(
        start=base.start,
        bound=base.bound,
        rounds=base.rounds,
        depth=base.depth,
        new_per_round=base.new_per_round,
        attempts_per_round=base.attempts_per_round,
        xrx_per_round=base.xrx_per_round,
        xsx_per_round=base.xsx_per_round,
        identifications_per_round=identifications_per_round,
        frontier=base.frontier,
        log=log,
    )


def _as_ninth(expl: Exploration) -> NinthExploration:
    """The same exploration as a ninth exploration (identity on states)."""
    return NinthExploration(
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


def performed(expl: Exploration) -> Iterator[tuple[DState, Change, DState]]:
    """Every change within the bound on every result whose changes were attempted."""
    yield from performed_ninth(_as_ninth(expl))


def count_shortest_sequences(expl: Exploration) -> dict[DState, int]:
    """How many shortest sequences reach each explored result from the start."""
    return count_shortest_sequences_ninth(_as_ninth(expl))


@dataclass
class RecordedExploration:
    """Exploration under the unchosen reading C-M2: results carry the identification record."""

    start: Recorded
    bound: int
    rounds: int
    depth: dict[Recorded, int]
    new_per_round: list[int]


def recorded_order(recorded: Recorded) -> tuple[object, ...]:
    """A fixed order on recorded states."""
    rec = recorded.record
    rec_key: object = () if rec is None else (rec.r, rec.s)
    return (*order(recorded.state), rec is not None, rec_key)


def explore_recorded(bound: int, rounds: int = 100) -> RecordedExploration:
    """Breadth-first from the empty beginning, keeping the identification record with the result."""
    if bound < 1:
        raise ValueError("the bound admits at least one term")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")
    root = recorded_start()
    depth = {root: 0}
    wave = [root]
    new_per_round = [1]
    for _r in range(1, rounds + 1):
        found: list[Recorded] = []
        for recorded in wave:
            for change in changes(recorded.state):
                nxt = recorded_perform(recorded, change)
                if nxt.n > bound:
                    continue
                if nxt not in depth:
                    depth[nxt] = _r
                    found.append(nxt)
        wave = sorted(found, key=recorded_order)
        new_per_round.append(len(wave))
    return RecordedExploration(start=root, bound=bound, rounds=rounds, depth=depth, new_per_round=new_per_round)


def recorded_performed(expl: RecordedExploration) -> Iterator[tuple[Recorded, Change, Recorded]]:
    """Every change within the bound on every recorded result whose changes were attempted."""
    for recorded in sorted(expl.depth, key=lambda t: (expl.depth[t], recorded_order(t))):
        if expl.depth[recorded] >= expl.rounds:
            continue
        for change in changes(recorded.state):
            nxt = recorded_perform(recorded, change)
            if nxt.n > expl.bound:
                continue
            yield recorded, change, nxt
