"""Attempting every change of the eighth seed on every alternative, round by round.

Given by the eighth seed
    Attempt every change, fewest additions first.  Attempt 100 changes along
    each alternative, finishing earlier changes on every alternative before
    later ones.  Do not invent a change to reach 100.  If the alternatives
    exceed what can be completed, declare a finite bound, export the exact
    frontier, and prove what is complete within it.

Cited from the first, fourth, fifth, sixth and seventh derivations and
re-checked
    The protocol is reading C6 of the earlier papers: round `k` attempts
    every change on every result first reached in round `k − 1`; the bound is
    on terms and on rounds together, the frontier in two parts.  The record
    of an attempt says whether the outcome asserts some `xrx` while the state
    asserts none, and likewise for `xsx` (the sixth's flag, once per
    relation).  `count_shortest_sequences` is the sixth's dynamic programme
    written again with the same fields; the exactness rule is the sixth's on
    the `r` part (`sequences_exact`): an `s` addition never adds a term, so
    only the `r` part's names decide whether a shortest sequence passes
    through one more term than the result.  The two-change cycle is written
    again for two relations (`cycle`).

Derived (paper, `lean4/Eighth/`)
    The round of a result is its cost (the sixth's cost of its `r` part plus
    its `s` total): a result is first met by a shortest sequence, whose
    states stay within the bound on terms.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field

from sixth.cost import merged_optimal

from eighth.changes import Change, Kind, changes, makes_some_loop, perform
from eighth.state import DState, canonical, names_one_term

__all__ = [
    "Attempt",
    "Exit",
    "Exploration",
    "attempt",
    "count_shortest_sequences",
    "cycle",
    "explore",
    "order",
    "performed",
    "sequences_exact",
]


def order(state: DState) -> tuple[int, tuple[int, ...], tuple[int, ...], int, int]:
    """A fixed order on states, for reproducible output."""
    a, b = state.names if state.names is not None else (-1, -1)
    return (state.n, state.r, state.s, a, b)


@dataclass(frozen=True)
class Attempt:
    """One attempted change: the change, its outcome, and whether it makes some `xrx` / `xsx` asserted."""

    state: DState
    change: Change
    outcome: DState | None
    beyond: bool
    xrx: bool
    xsx: bool


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


def attempt(state: DState, change: Change, bound: int) -> Attempt:
    """Attempt `change` on `state` and record what happens.  Every change is performed."""
    out = perform(state, change)
    xrx = makes_some_loop(state, change, "r")
    xsx = makes_some_loop(state, change, "s")
    if out.n > bound:
        return Attempt(state, change, None, True, xrx, xsx)
    return Attempt(state, change, canonical(out), False, xrx, xsx)


def explore(start: DState, bound: int, rounds: int = 100, keep_log: bool = False) -> Exploration:
    """Explore from `start` for `rounds` rounds, keeping every result with at most `bound` terms."""
    if start.n < 1:
        raise ValueError("what is given has a term")
    if start.n > bound:
        raise ValueError("the bound is below what is given")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")
    root = canonical(start)
    depth = {root: 0}
    wave = [root]
    new_per_round = [1]
    attempts_per_round = [0]
    xrx_per_round = [0]
    xsx_per_round = [0]
    frontier: list[Exit] = []
    log: list[Attempt] = []
    attempts_known = xrx_known = xsx_known = 0
    for r in range(1, rounds + 1):
        found: list[DState] = []
        for state in wave:
            for change in changes(state):
                rec = attempt(state, change, bound)
                attempts_known += 1
                xrx_known += rec.xrx
                xsx_known += rec.xsx
                if rec.beyond:
                    frontier.append(Exit(state, change))
                elif rec.outcome is not None and rec.outcome not in depth:
                    depth[rec.outcome] = r
                    found.append(rec.outcome)
                if keep_log:
                    log.append(rec)
        attempts_per_round.append(attempts_known)
        xrx_per_round.append(xrx_known)
        xsx_per_round.append(xsx_known)
        wave = sorted(found, key=order)
        new_per_round.append(len(wave))
    return Exploration(
        start=root,
        bound=bound,
        rounds=rounds,
        depth=depth,
        new_per_round=new_per_round,
        attempts_per_round=attempts_per_round,
        xrx_per_round=xrx_per_round,
        xsx_per_round=xsx_per_round,
        frontier=frontier,
        log=log,
    )


def performed(expl: Exploration) -> Iterator[tuple[DState, Change, DState]]:
    """Every change within the bound on every result whose changes were attempted."""
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        if expl.depth[state] >= expl.rounds:
            continue
        for change in changes(state):
            out = perform(state, change)
            if out.n > expl.bound:
                continue
            yield state, change, canonical(out)


def count_shortest_sequences(expl: Exploration) -> dict[DState, int]:
    """How many shortest sequences of changes reach each explored result from what is given.

    Counted change by change on the least writings, following only the
    changes that raise the round by one; exact where `sequences_exact` says.
    Every outcome within the bound must be a result of a round at most one
    higher, which is checked here.
    """
    sequences = {state: 0 for state in expl.depth}
    sequences[expl.start] = 1
    for state, change, out in performed(expl):
        if out not in expl.depth or expl.depth[out] > expl.depth[state] + 1:
            raise ValueError(f"{change.written(state)} on {state.key()} raises the round by more than one")
        if expl.depth[out] == expl.depth[state] + 1:
            sequences[out] += sequences[state]
    return sequences


def sequences_exact(expl: Exploration, state: DState, bra: bool) -> bool:
    """Is the count of shortest sequences to `state` exact within the bound on terms?

    The sixth's rule on the `r` part: names kept, exact unless the names are
    one term and the result has as many terms as the bound; without names,
    unless some optimal placement of the names on the `r` part puts them on
    one term.  An `s` addition never adds a term.
    """
    if state.n < expl.bound:
        return True
    if state.names is not None:
        return not names_one_term(state)
    return not merged_optimal(state.r_part(), bra)


def cycle(state: DState) -> tuple[Change, Change] | None:
    """Two changes that lead from `state` back to itself, if there are (there always are, given a term).

    With two terms `x ≠ y`: add `xry`, remove `xry`.  With one term: add a
    term, identify it with the one there.
    """
    if state.n >= 2:
        first, second = Change(Kind.ADD_ASSERTION, "r", 0, 1), Change(Kind.REMOVE, "r", 0, 1)
    elif state.n == 1:
        first, second = Change(Kind.ADD_TERM), Change(Kind.IDENTIFY, "", 0, 1)
    else:
        return None
    back = perform(perform(state, first), second)
    return (first, second) if back == state else None
