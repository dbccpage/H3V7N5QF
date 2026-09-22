"""Attempting every change of the eleventh seed, and the unchosen labeled reading.

Given by the eleventh seed
    Attempt every change, fewest additions first.  A writing of terms may
    collide two terms that remain two; that is not a change.

Cited from the ninth derivation (`ninth.explore`) and re-checked
    The protocol, the bound, the frontier and the shortest-sequence counts
    mention no writing: they survive and are imported.  Under C-W1 the
    exploration is the ninth's.  `cycle` is imported.  The unchosen labeled
    reading tags each ninth result with every writing of its terms.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field

from ninth.explore import Exit, Exploration as NinthExploration, cycle
from ninth.explore import count_shortest_sequences as count_shortest_sequences_ninth
from ninth.explore import explore as explore_ninth
from ninth.explore import order, performed as performed_ninth, sequences_exact

from eleventh.changes import Change, labeled_of
from eleventh.state import DState, Labeled, labeled_start
from eleventh.writing import determines, writings

__all__ = [
    "Exit",
    "Exploration",
    "LabeledExploration",
    "count_shortest_sequences",
    "count_shortest_sequences_ninth",
    "cycle",
    "explore",
    "explore_labeled",
    "labeled_determines",
    "labeled_order",
    "order",
    "performed",
    "sequences_exact",
    "writings_of",
]


@dataclass
class Exploration:
    """The ninth's exploration (C-W1: writings are readings, not results)."""

    start: DState
    bound: int
    rounds: int
    depth: dict[DState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    xrx_per_round: list[int]
    xsx_per_round: list[int]
    frontier: list[Exit] = field(default_factory=list)
    log: list[object] = field(default_factory=list)

    @property
    def last_new_round(self) -> int:
        """The last round that produced a new result within the bound."""
        return max(r for r, new in enumerate(self.new_per_round) if new)

    @property
    def awaiting(self) -> list[DState]:
        """The results of the last round, whose changes were not attempted."""
        return sorted((s for s, r in self.depth.items() if r >= self.rounds), key=order)


def explore(start: DState, bound: int, rounds: int = 100, keep_log: bool = False) -> Exploration:
    """The ninth's exploration.  Results, rounds and the frontier are the ninth's (C-W1)."""
    base = explore_ninth(start, bound, rounds, keep_log=keep_log)
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
        log=list(base.log) if keep_log else [],
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


def writings_of(state: DState) -> tuple[tuple[int, ...], ...]:
    """The writings of `state` (up to renaming letters)."""
    return writings(state.n)


@dataclass
class LabeledExploration:
    """Exploration under the unchosen reading C-W2: results are labeled states."""

    start: Labeled
    bound: int
    rounds: int
    depth: dict[Labeled, int]
    new_per_round: list[int]


def labeled_order(labeled: Labeled) -> tuple[int, tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    """A fixed order on labeled states."""
    return (*order(labeled.state), labeled.writing)


def explore_labeled(bound: int, rounds: int = 100) -> LabeledExploration:
    """Each ninth result within the bound, with every writing of its terms.

    A writing is not a change, so the round of a labeled result is the ninth's
    round of its state.  The empty beginning has one writing.
    """
    if bound < 1:
        raise ValueError("the bound admits at least one term")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")
    ninth = explore_ninth(labeled_start().state, bound, rounds)
    depth: dict[Labeled, int] = {}
    new_per_round = [0] * (rounds + 1)
    for state, round_no in ninth.depth.items():
        for labeled in labeled_of(state):
            depth[labeled] = round_no
            new_per_round[round_no] += 1
    return LabeledExploration(
        start=labeled_start(),
        bound=bound,
        rounds=rounds,
        depth=depth,
        new_per_round=new_per_round,
    )


def labeled_determines(labeled: Labeled) -> bool:
    """Does this labeled result's writing determine its assertions?"""
    return determines(labeled.state, labeled.writing)
