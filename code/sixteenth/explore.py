"""Attempting every change of the sixteenth seed from the empty state, round by round.

Given by the sixteenth seed
    Attempt every change, fewest additions first.  For every result, record
    how many terms and assertions it adds to what is given.  Attempt 100
    changes along each alternative, finishing earlier changes on every
    alternative before later ones.  Do not invent a change to reach 100.  If
    the alternatives exceed what can be completed, declare a finite bound,
    export the exact frontier, and prove what is complete within it.

Cited from the ninth derivation (`ninth.explore`) and re-checked
    The protocol (round `k` attempts every change on every result first
    reached in round `k − 1`; the bound is on terms and on rounds together;
    the frontier is the attempts that leave the bound on terms) mentions no
    record and survives.  What does not survive as code: the ninth's
    `explore` runs on ninth states and lists no admission, so the
    exploration is written again on states with a record, with the leftover
    writing of every attempt recorded (the fourteenth's C-F1, kept) and the
    admissions attempted after the direct additions.  The shortest-sequence
    count follows the changes that raise the round by one — here the direct
    additions *and the removals* — and is exact for every result within the
    bound: a shortest sequence never identifies, so no state along it has
    more terms than the result.

Derived (paper, `lean4/Sixteenth/Cost.lean`)
    The round of a result is its potential.  Every state with a term reaches
    itself in two changes (a term added and identified away); every state
    with an assertion also by a removal and the admission of its leftover
    into the same relation — the ninth's add-then-remove is no longer a
    cycle, since it leaves a leftover.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field

from fourteenth.leftover import LeftWriting
from ninth.changes import Kind

from sixteenth.changes import Change16, changes16, perform16, raises_potential
from sixteenth.leftover import leftover_of16
from sixteenth.state import RState, Reading, canonical16

__all__ = [
    "Attempt16",
    "Exit16",
    "Exploration16",
    "attempt16",
    "count_shortest_sequences16",
    "cycle16",
    "explore16",
    "order16",
    "performed16",
    "returns_in_two",
    "sequences_exact16",
]


def order16(rs: RState) -> tuple[int, tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    """A fixed order on states, for reproducible output."""
    return (rs.n, rs.state.r, rs.state.s, rs.record.mult)


@dataclass(frozen=True)
class Attempt16:
    """One attempted change: the change, its leftover writing, and its outcome (least writing) within the bound."""

    state: RState
    change: Change16
    outcome: RState | None
    beyond: bool
    leftover: LeftWriting


@dataclass(frozen=True)
class Exit16:
    """A frontier entry: an attempt that leaves the bound on terms (always "add a term")."""

    state: RState
    change: Change16


@dataclass
class Exploration16:
    """Everything recorded by `explore16`."""

    start: RState
    bound: int
    rounds: int
    reading: Reading
    depth: dict[RState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    admissions_per_round: list[int]
    frontier: list[Exit16] = field(default_factory=list)
    log: list[Attempt16] = field(default_factory=list)

    @property
    def last_new_round(self) -> int:
        """The last round that produced a new result within the bound."""
        return max(r for r, new in enumerate(self.new_per_round) if new)

    @property
    def awaiting(self) -> list[RState]:
        """The results of the last round, whose changes were not attempted."""
        return sorted((s for s, r in self.depth.items() if r >= self.rounds), key=order16)


def attempt16(rs: RState, change: Change16, bound: int, reading: Reading = Reading.COUNT) -> Attempt16:
    """Attempt `change` on `rs` and record its leftover writing.  Every change is performed."""
    out = perform16(rs, change, reading)
    writing = leftover_of16(rs, change)
    if out.n > bound:
        return Attempt16(rs, change, None, True, writing)
    return Attempt16(rs, change, canonical16(out), False, writing)


def explore16(
    start: RState, bound: int, rounds: int = 100, keep_log: bool = False, reading: Reading = Reading.COUNT
) -> Exploration16:
    """Explore from `start` for `rounds` rounds, keeping every result with at most `bound` terms.

    Round `r` attempts every change on every result first reached in round
    `r − 1`; the results first reached in round `rounds` are kept but their
    changes are not attempted.
    """
    if start.n > bound:
        raise ValueError("the bound is below the start")
    if bound < 1:
        raise ValueError("the bound admits at least one term")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")
    root = canonical16(start)
    depth = {root: 0}
    wave = [root]
    new_per_round = [1]
    attempts_per_round = [0]
    admissions_per_round = [0]
    frontier: list[Exit16] = []
    log: list[Attempt16] = []
    attempts_known = admissions_known = 0
    for r in range(1, rounds + 1):
        found: list[RState] = []
        for rs in wave:
            for change in changes16(rs):
                rec = attempt16(rs, change, bound, reading)
                attempts_known += 1
                admissions_known += change.admits
                if rec.beyond:
                    frontier.append(Exit16(rs, change))
                elif rec.outcome is not None and rec.outcome not in depth:
                    depth[rec.outcome] = r
                    found.append(rec.outcome)
                if keep_log:
                    log.append(rec)
        attempts_per_round.append(attempts_known)
        admissions_per_round.append(admissions_known)
        wave = sorted(found, key=order16)
        new_per_round.append(len(wave))
    return Exploration16(
        start=root,
        bound=bound,
        rounds=rounds,
        reading=reading,
        depth=depth,
        new_per_round=new_per_round,
        attempts_per_round=attempts_per_round,
        admissions_per_round=admissions_per_round,
        frontier=frontier,
        log=log,
    )


def performed16(expl: Exploration16) -> Iterator[tuple[RState, Change16, RState, RState]]:
    """Every change within the bound on every result whose changes were attempted.

    Yields the result, the change, the outcome as performed (in the result's
    writing), and the outcome's least writing; results in the order of their
    round and then the fixed order.  A result first reached in the last round
    has not had its changes attempted and is left out.
    """
    for rs in sorted(expl.depth, key=lambda s: (expl.depth[s], order16(s))):
        if expl.depth[rs] >= expl.rounds:
            continue
        for change in changes16(rs):
            out = perform16(rs, change, expl.reading)
            if out.n > expl.bound:
                continue
            yield rs, change, out, canonical16(out)


def count_shortest_sequences16(expl: Exploration16) -> dict[RState, int]:
    """How many shortest sequences of changes reach each explored result from the start.

    Counted change by change over the changes that raise the round by one;
    every such change must raise the potential (a theorem of the paper), and
    no change may raise the round by more than one.  Both are checked here.
    """
    sequences = {rs: 0 for rs in expl.depth}
    sequences[expl.start] = 1
    for rs, change, _raw, out in performed16(expl):
        if out not in expl.depth or expl.depth[out] > expl.depth[rs] + 1:
            raise ValueError(f"{change.written(rs)} on {rs.key()} raises the round by more than one")
        if expl.depth[out] == expl.depth[rs] + 1:
            if not raises_potential(change):
                raise ValueError(f"{change.written(rs)} on {rs.key()} raises the round and does not raise the potential")
            sequences[out] += sequences[rs]
    return sequences


def sequences_exact16(expl: Exploration16, rs: RState) -> bool:
    """Is the count of shortest sequences to `rs` exact within the bound on terms?

    Always, for a result within the bound: a shortest sequence never
    identifies, so no state along it has more terms than the result.
    """
    return rs.n <= expl.bound


def cycle16(rs: RState) -> tuple[Change16, Change16] | None:
    """The two changes proposed from `rs` back to `rs`, or `None` on the empty state.

    With an assertion: remove it and admit its leftover into the same
    relation.  Otherwise, with a term: add a term and identify it away.
    That they return to `rs` is checked by `returns_in_two`.
    """
    n = rs.n
    for rel in ("r", "s"):
        for x, y in rs.state.part(rel).pairs:
            return Change16(Kind.REMOVE, rel, x, y), Change16(Kind.ADD_ASSERTION, rel, x, y, True)
    if n >= 1:
        return Change16(Kind.ADD_TERM), Change16(Kind.IDENTIFY, "", 0, n)
    return None


def returns_in_two(rs: RState) -> bool:
    """Do the two changes of `cycle16` lead from `rs` back to `rs` (the same result)?"""
    found = cycle16(rs)
    if found is None:
        return False
    out = perform16(perform16(rs, found[0]), found[1])
    return canonical16(out) == canonical16(rs)
