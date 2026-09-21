"""Attempting every change of the fourteenth seed, recording leftover writing, and the unchosen tagged reading.

Given by the fourteenth seed
    Attempt every change, fewest additions first.  After every change, record
    what that change leaves.

Cited from the ninth derivation (`ninth.explore`) and re-checked
    The protocol, the bound, the frontier and the shortest-sequence counts
    mention no leftover: they survive and are imported.  Under C-F1 the
    exploration is the ninth's, with leftover writing filled on every attempt.
    `cycle` is imported.  The unchosen tagged reading is explored afresh.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field

from ninth.explore import Exit, Exploration as NinthExploration, cycle
from ninth.explore import count_shortest_sequences as count_shortest_sequences_ninth
from ninth.explore import explore as explore_ninth
from ninth.explore import order, performed as performed_ninth, sequences_exact

from fourteenth.changes import Change, changes, tagged_perform
from fourteenth.leftover import LeftWriting, leftover_of
from fourteenth.state import DState, Tagged, tagged_start

__all__ = [
    "Attempt",
    "Exit",
    "Exploration",
    "TaggedExploration",
    "attempt",
    "count_shortest_sequences",
    "count_shortest_sequences_ninth",
    "cycle",
    "explore",
    "explore_tagged",
    "leftover_performed",
    "order",
    "performed",
    "sequences_exact",
    "tagged_order",
    "tagged_performed",
]


@dataclass(frozen=True)
class Attempt:
    """One attempted change of the fourteenth seed: the ninth's record plus leftover writing."""

    state: DState
    change: Change
    outcome: DState | None
    beyond: bool
    xrx: bool
    xsx: bool
    leftover: LeftWriting


def attempt(state: DState, change: Change, bound: int) -> Attempt:
    """Attempt `change` on `state` and record leftover writing.  Every change is performed."""
    from ninth.explore import attempt as attempt_ninth

    rec = attempt_ninth(state, change, bound)
    return Attempt(rec.state, rec.change, rec.outcome, rec.beyond, rec.xrx, rec.xsx, leftover_of(state, change))


@dataclass
class Exploration:
    """The ninth's exploration with leftover writing filled on every kept attempt."""

    start: DState
    bound: int
    rounds: int
    depth: dict[DState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    xrx_per_round: list[int]
    xsx_per_round: list[int]
    leftover_per_round: list[dict[str, int]]
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
    """The ninth's exploration, leftover writing recorded on every attempt when the log is kept.

    Results, rounds and the frontier are the ninth's (C-F1).  Leftover of
    every performed change within the bound is available through
    `performed` even when the log is empty.
    """
    base = explore_ninth(start, bound, rounds, keep_log=keep_log)
    leftover_per_round: list[dict[str, int]] = [{"nothing": 0, "pair": 0, "merge": 0} for _ in base.new_per_round]
    log = [attempt(rec.state, rec.change, bound) for rec in base.log] if keep_log else []
    if keep_log:
        by_state_round = base.depth
        for rec in log:
            r = by_state_round[rec.state] + 1
            leftover_per_round[r][rec.leftover.kind] += 1
    return Exploration(
        start=base.start,
        bound=base.bound,
        rounds=base.rounds,
        depth=base.depth,
        new_per_round=base.new_per_round,
        attempts_per_round=base.attempts_per_round,
        xrx_per_round=base.xrx_per_round,
        xsx_per_round=base.xsx_per_round,
        leftover_per_round=leftover_per_round,
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


def leftover_performed(expl: Exploration) -> Iterator[tuple[DState, Change, DState, LeftWriting]]:
    """Every change within the bound, with its leftover writing."""
    for state, change, out in performed(expl):
        yield state, change, out, leftover_of(state, change)


@dataclass
class TaggedExploration:
    """Exploration under the unchosen reading C-F2: results are tagged states."""

    start: Tagged
    bound: int
    rounds: int
    depth: dict[Tagged, int]
    new_per_round: list[int]


def tagged_order(tagged: Tagged) -> tuple[int, tuple[int, ...], tuple[int, ...], str]:
    """A fixed order on tagged states."""
    return (*order(tagged.state), tagged.leftover.written())


def explore_tagged(bound: int, rounds: int = 100) -> TaggedExploration:
    """Breadth-first from the empty beginning, tagging each arrival with leftover writing."""
    if bound < 1:
        raise ValueError("the bound admits at least one term")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")
    root = tagged_start()
    depth = {root: 0}
    wave = [root]
    new_per_round = [1]
    for r in range(1, rounds + 1):
        found: list[Tagged] = []
        for tagged in wave:
            for change in changes(tagged.state):
                nxt = tagged_perform(tagged, change)
                if nxt.n > bound:
                    continue
                if nxt not in depth:
                    depth[nxt] = r
                    found.append(nxt)
        wave = sorted(found, key=tagged_order)
        new_per_round.append(len(wave))
    return TaggedExploration(start=root, bound=bound, rounds=rounds, depth=depth, new_per_round=new_per_round)


def tagged_performed(expl: TaggedExploration) -> Iterator[tuple[Tagged, Change, Tagged]]:
    """Every change within the bound on every tagged result whose changes were attempted."""
    for tagged in sorted(expl.depth, key=lambda t: (expl.depth[t], tagged_order(t))):
        if expl.depth[tagged] >= expl.rounds:
            continue
        for change in changes(tagged.state):
            nxt = tagged_perform(tagged, change)
            if nxt.n > expl.bound:
                continue
            yield tagged, change, nxt
