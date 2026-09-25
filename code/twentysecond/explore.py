"""Attempting every change of the twenty-second seed on results, round by round, from the empty state.

Given by the seed
    Attempt every change, fewest additions first.  Attempt 100 changes along
    each alternative, finishing earlier changes on every alternative before
    later ones.  Do not invent a change to reach 100.  If the alternatives
    exceed what can be completed, declare a finite bound, export the exact
    frontier, and prove what is complete within it.

Cited from the ninth derivation (`ninth.explore`) and re-checked
    The protocol is the ninth's (reading C6): round `k` attempts every change
    on every result first reached in round `k − 1`; the bound is on terms and
    rounds together; the frontier is the attempts leaving the bound on terms
    (always "add a term") and the results of the last round.  What changes:
    a result is now the least writing of a *plain* state (`result_of`), and
    its changes are those of that plain state (reading C-X, derived to give
    every result one change away).  Written again with those two
    replacements; the record of an attempt keeps the outcome state as
    reached (`raw`) beside its result.

Derived (paper; `lean4_core/Twentysecond/Cost.lean`)
    The round of a result is its cost `n + Σ |excess|`; a shortest sequence
    is additions only and every state along it is plain, so it never has
    more terms than its end: the shortest-sequence counts are exact within
    the bound.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field

from twentysecond.changes import Change, is_addition, perform, result_changes
from twentysecond.state import DState, result_of

__all__ = [
    "Attempt",
    "Exit",
    "Exploration",
    "attempt",
    "count_shortest_sequences",
    "explore",
    "order",
    "performed",
]


def order(state: DState) -> tuple[int, tuple[int, ...], tuple[int, ...]]:
    """A fixed order on states, for reproducible output."""
    return (state.n, state.r, state.s)


@dataclass(frozen=True)
class Attempt:
    """One attempted change on a result: the change, the state it reaches, and that state's result.

    `outcome` is `None` for an outcome beyond the bound on terms (`beyond`).
    """

    state: DState
    change: Change
    raw: DState
    outcome: DState | None
    beyond: bool


@dataclass(frozen=True)
class Exit:
    """A frontier entry: an attempt that leaves the bound on terms (always "add a term")."""

    state: DState
    change: Change


@dataclass
class Exploration:
    """Everything recorded by `explore`."""

    start: DState
    bound: int
    rounds: int
    depth: dict[DState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
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


def attempt(state: DState, change: Change, bound: int) -> Attempt:
    """Attempt `change` on the result `state` and record what happens.  Every change is performed."""
    raw = perform(state, change)
    if raw.n > bound:
        return Attempt(state, change, raw, None, True)
    return Attempt(state, change, raw, result_of(raw), False)


def explore(start: DState, bound: int, rounds: int = 100, keep_log: bool = False) -> Exploration:
    """Explore results from `start` for `rounds` rounds, keeping every result with at most `bound` terms."""
    if start.names is not None:
        raise ValueError("a state of this seed carries no names")
    if start.n > bound:
        raise ValueError("the bound is below the start")
    if bound < 1:
        raise ValueError("the bound admits at least one term")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")
    root = result_of(start)
    depth = {root: 0}
    wave = [root]
    new_per_round = [1]
    attempts_per_round = [0]
    frontier: list[Exit] = []
    log: list[Attempt] = []
    attempts_known = 0
    for r in range(1, rounds + 1):
        found: list[DState] = []
        for state in wave:
            for change in result_changes(state):
                rec = attempt(state, change, bound)
                attempts_known += 1
                if rec.beyond:
                    frontier.append(Exit(state, change))
                elif rec.outcome is not None and rec.outcome not in depth:
                    depth[rec.outcome] = r
                    found.append(rec.outcome)
                if keep_log:
                    log.append(rec)
        attempts_per_round.append(attempts_known)
        wave = sorted(found, key=order)
        new_per_round.append(len(wave))
    return Exploration(
        start=root,
        bound=bound,
        rounds=rounds,
        depth=depth,
        new_per_round=new_per_round,
        attempts_per_round=attempts_per_round,
        frontier=frontier,
        log=log,
    )


def performed(expl: Exploration) -> Iterator[tuple[DState, Change, DState, DState]]:
    """Every change within the bound on every result whose changes were attempted.

    Yields the result, the change, the outcome state, and its result.
    """
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        if expl.depth[state] >= expl.rounds:
            continue
        for change in result_changes(state):
            raw = perform(state, change)
            if raw.n > expl.bound:
                continue
            yield state, change, raw, result_of(raw)


def count_shortest_sequences(expl: Exploration) -> dict[DState, int]:
    """How many shortest sequences of changes reach each explored result from the start.

    A sequence is counted change by change on the results' plain states; only
    additions that raise the round by one are followed (a shortest sequence
    has no other change: `lean4_core/Twentysecond/Cost.lean`,
    `shortest_additions`).  Exact within the bound: every state along a
    shortest sequence is plain and has no more terms than its end.
    """
    sequences = {state: 0 for state in expl.depth}
    sequences[expl.start] = 1
    for state, change, _, out in performed(expl):
        if out in expl.depth and expl.depth[out] == expl.depth[state] + 1 and is_addition(change):
            sequences[out] += sequences[state]
    return sequences
