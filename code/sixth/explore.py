"""Attempting every change of the sixth seed on every alternative, round by round.

Given by the sixth seed
    Attempt every change, fewest additions first.  Attempt 100 changes along
    each alternative, finishing earlier changes on every alternative before
    later ones.  Do not invent a change to reach 100.  If the alternatives
    exceed what can be completed, declare a finite bound, export the exact
    frontier, and prove what is complete within it.

Cited from the first, fourth and fifth derivations (`xry.explore`,
`fourth.explore`, `fifth.explore`) and re-checked
    The protocol is reading C6 of the earlier papers: round `k` attempts
    every change on every result first reached in round `k − 1`; the bound is
    on terms and on rounds together (the fourth's C8′), the frontier in two
    parts.  What does not survive: an attempt can no longer be obstructed,
    so the record of an attempt has no obstruction and no answers; instead it
    says whether the outcome asserts some `xrx` while the state does not (what
    the fifth would have obstructed).  The fifth's `count_shortest_sequences`
    (a dynamic programme over the changes that raise the round by one) is
    written again with the same fields; its exactness rule changes under FREE
    (`sequences_exact`).  The two-change cycle at every state
    (`fifth.explore.cycle`: add `xry`, remove it; or add a term, identify it
    back) mentions no legality and is imported.

Derived (paper, `lean4/Sixth/`)
    The round of a result is its cost (size difference plus twice the
    destroyed givens, with the sixth seed's destroyed givens): a result is
    first met by a shortest sequence, whose states stay within the bound on
    terms.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field

from fifth.explore import cycle

from sixth.changes import Change, changes, makes_some_xrx, perform
from sixth.cost import merged_optimal
from sixth.state import MState, canonical, names_one_term

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


def order(state: MState) -> tuple[int, tuple[int, ...], int, int]:
    """A fixed order on states, for reproducible output."""
    a, b = state.names if state.names is not None else (-1, -1)
    return (state.n, state.mult, a, b)


@dataclass(frozen=True)
class Attempt:
    """One attempted change: the change, its outcome, and whether it makes some `xrx` asserted.

    `outcome` is the result (least writing) of the change within the bound;
    it is `None` for an outcome beyond the bound (`beyond`).  `xrx` says
    whether the outcome asserts some `xrx` while the state asserts none.
    """

    state: MState
    change: Change
    outcome: MState | None
    beyond: bool
    xrx: bool


@dataclass(frozen=True)
class Exit:
    """A frontier entry: an attempt that leaves the bound on terms (always "add a term")."""

    state: MState
    change: Change


@dataclass
class Exploration:
    """Everything recorded by `explore`."""

    start: MState
    bound: int
    rounds: int
    depth: dict[MState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    xrx_per_round: list[int]
    frontier: list[Exit] = field(default_factory=list)
    log: list[Attempt] = field(default_factory=list)

    @property
    def last_new_round(self) -> int:
        """The last round that produced a new result within the bound."""
        return max(r for r, new in enumerate(self.new_per_round) if new)

    @property
    def awaiting(self) -> list[MState]:
        """The results of the last round, whose changes were not attempted."""
        return sorted((s for s, r in self.depth.items() if r >= self.rounds), key=order)


def attempt(state: MState, change: Change, bound: int) -> Attempt:
    """Attempt `change` on `state` and record what happens.  Every change is performed."""
    out = perform(state, change)
    xrx = makes_some_xrx(state, change)
    if out.n > bound:
        return Attempt(state, change, None, True, xrx)
    return Attempt(state, change, canonical(out), False, xrx)


def explore(start: MState, bound: int, rounds: int = 100, keep_log: bool = False) -> Exploration:
    """Explore from `start` for `rounds` rounds, keeping every result with at most `bound` terms.

    Round `r` attempts every change on every result first reached in round
    `r − 1`; the results first reached in round `rounds` are kept but their
    changes are not attempted.  Any well-formed state with a term may start.
    """
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
    frontier: list[Exit] = []
    log: list[Attempt] = []
    attempts_known = 0
    xrx_known = 0
    for r in range(1, rounds + 1):
        found: list[MState] = []
        for state in wave:
            for change in changes(state):
                rec = attempt(state, change, bound)
                attempts_known += 1
                xrx_known += rec.xrx
                if rec.beyond:
                    frontier.append(Exit(state, change))
                elif rec.outcome is not None and rec.outcome not in depth:
                    depth[rec.outcome] = r
                    found.append(rec.outcome)
                if keep_log:
                    log.append(rec)
        # Round r attempted every change on every result first reached in round r - 1.
        attempts_per_round.append(attempts_known)
        xrx_per_round.append(xrx_known)
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
        frontier=frontier,
        log=log,
    )


def performed(expl: Exploration) -> Iterator[tuple[MState, Change, MState]]:
    """Every change within the bound on every result whose changes were attempted.

    Yields the result, the change, and the outcome (least writing), results
    in the order of their round and then the fixed order.  A result first
    reached in the last round has not had its changes attempted and is left
    out.  The outcome may be a result of an earlier round, of the same round,
    or of the next.
    """
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        if expl.depth[state] >= expl.rounds:
            continue
        for change in changes(state):
            out = perform(state, change)
            if out.n > expl.bound:
                continue
            yield state, change, canonical(out)


def count_shortest_sequences(expl: Exploration) -> dict[MState, int]:
    """How many shortest sequences of changes reach each explored result from what is given.

    A sequence is counted change by change: two changes on one result that
    differ (as listed) count as two, even when their outcomes are the same
    result.  Only the changes that raise the round by one are followed (a
    shortest sequence has no other); the count is exact for the results
    `sequences_exact` says (a theorem of the paper).  Every outcome within
    the bound must be a result of a round at most one higher (the round of a
    result is its cost, which rises by at most one), which is checked here.
    """
    sequences = {state: 0 for state in expl.depth}
    sequences[expl.start] = 1
    for state, change, out in performed(expl):
        if out not in expl.depth or expl.depth[out] > expl.depth[state] + 1:
            raise ValueError(f"{change.written(state)} on {state.key()} raises the round by more than one")
        if expl.depth[out] == expl.depth[state] + 1:
            sequences[out] += sequences[state]
    return sequences


def sequences_exact(expl: Exploration, state: MState, bra: bool) -> bool:
    """Is the count of shortest sequences to `state` exact within the bound on terms?

    Names kept: a shortest sequence to a result with the names apart never has
    more terms than the result; to a result with the names one term, at most
    one more (built with them apart and merged last).  Without names: at most
    one more term exactly when some optimal placement of the names puts them
    on one term (`merged_optimal`).
    """
    if state.n < expl.bound:
        return True
    if state.names is not None:
        return not names_one_term(state)
    return not merged_optimal(state, bra)
