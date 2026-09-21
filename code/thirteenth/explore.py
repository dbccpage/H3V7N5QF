"""Attempting every change of the thirteenth seed, recording coarser writings.

Given by the thirteenth seed
    Attempt every change, fewest additions first.  For every result, record
    also its coarser writing.

Cited from the ninth derivation (`ninth.explore`) and re-checked
    The protocol, the bound, the frontier and the shortest-sequence counts
    mention no coarser writing: they survive and are imported.  Under C-C1
    the exploration is the ninth's, with the coarser writing filled on
    every result.  `cycle` is imported.  The unchosen coarser reading is
    explored by quotienting the ninth's results.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field

from fourth.state import canonical as canonical_one
from ninth.explore import Exit, Exploration as NinthExploration, cycle
from ninth.explore import count_shortest_sequences as count_shortest_sequences_ninth
from ninth.explore import explore as explore_ninth
from ninth.explore import order, performed as performed_ninth, sequences_exact
from ninth.state import empty

from thirteenth.changes import Change, changes, perform
from thirteenth.coarse import coarse
from thirteenth.state import Coarse, DState

__all__ = [
    "Attempt",
    "CoarseExploration",
    "Exit",
    "Exploration",
    "attempt",
    "coarse_order",
    "count_shortest_sequences",
    "coarse_performed",
    "count_shortest_sequences_ninth",
    "cycle",
    "explore",
    "explore_coarse",
    "order",
    "performed",
    "sequences_exact",
]


@dataclass(frozen=True)
class Attempt:
    """One attempted change of the thirteenth seed: the ninth's record plus the coarser writing of the outcome."""

    state: DState
    change: Change
    outcome: DState | None
    beyond: bool
    xrx: bool
    xsx: bool
    coarser: Coarse | None


def attempt(state: DState, change: Change, bound: int) -> Attempt:
    """Attempt `change` on `state` and record the coarser writing of the outcome when it stays in bound."""
    from ninth.explore import attempt as attempt_ninth

    rec = attempt_ninth(state, change, bound)
    written = coarse(rec.outcome) if rec.outcome is not None else None
    return Attempt(rec.state, rec.change, rec.outcome, rec.beyond, rec.xrx, rec.xsx, written)


@dataclass
class Exploration:
    """The ninth's exploration with coarser writings filled on outcomes."""

    start: DState
    bound: int
    rounds: int
    depth: dict[DState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    xrx_per_round: list[int]
    xsx_per_round: list[int]
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
    """The ninth's exploration, coarser writings on every outcome when the log is kept.

    Results, rounds and the frontier are the ninth's (C-C1).
    """
    base = explore_ninth(start, bound, rounds, keep_log=keep_log)
    log = [attempt(rec.state, rec.change, bound) for rec in base.log] if keep_log else []
    return Exploration(
        start=base.start,
        bound=base.bound,
        rounds=base.rounds,
        depth=base.depth,
        new_per_round=base.new_per_round,
        attempts_per_round=base.attempts_per_round,
        xrx_per_round=base.xrx_per_round,
        xsx_per_round=base.xsx_per_round,
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
class CoarseExploration:
    """Exploration under the unchosen reading C-C2: results are coarser writings."""

    start: Coarse
    bound: int
    rounds: int
    depth: dict[Coarse, int]
    new_per_round: list[int]


def coarse_order(written: Coarse) -> tuple[object, ...]:
    """A fixed order on coarser states."""
    return (written.n, written.mult)


def explore_coarse(bound: int, rounds: int = 100) -> CoarseExploration:
    """The ninth's results quotiented by coarser writing, from the empty beginning."""
    if bound < 1:
        raise ValueError("the bound admits at least one term")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")
    base = explore_ninth(empty(), bound, rounds)
    depth: dict[Coarse, int] = {}
    for state, round_no in base.depth.items():
        written = canonical_one(coarse(state))
        prev = depth.get(written)
        if prev is None or round_no < prev:
            depth[written] = round_no
    new_per_round = [0] * (rounds + 1)
    for round_no in depth.values():
        if round_no <= rounds:
            new_per_round[round_no] += 1
    return CoarseExploration(
        start=canonical_one(coarse(empty())),
        bound=bound,
        rounds=rounds,
        depth=depth,
        new_per_round=new_per_round,
    )


def coarse_performed(expl: CoarseExploration) -> Iterator[tuple[Coarse, Change, Coarse]]:
    """Every change of a coarser result whose ninth preimage was attempted, read on the coarser writing.

    Used only to exercise the C-C2 walk; the depth is already the quotient
    of the ninth exploration.
    """
    from ninth.explore import explore as explore_ninth_local

    ninth = explore_ninth_local(empty(), expl.bound, expl.rounds)
    seen: set[tuple[str, str, str]] = set()
    for state in sorted(ninth.depth, key=order):
        if ninth.depth[state] >= expl.rounds:
            continue
        src = canonical_one(coarse(state))
        for change in changes(state):
            nxt = perform(state, change)
            if nxt.n > expl.bound:
                continue
            dst = canonical_one(coarse(nxt))
            key = (src.key(), change.written(state), dst.key())
            if key in seen:
                continue
            seen.add(key)
            yield src, change, dst
