"""Attempting every change of the fifth seed on every alternative, round by round.

Given by the fifth seed
    Attempt every change, fewest additions first.  Attempt 100 changes along
    each alternative, finishing earlier changes on every alternative before
    later ones.  Do not invent a change to reach 100.  If the alternatives
    exceed what can be completed, declare a finite bound, export the exact
    frontier, and prove what is complete within it.

Cited from the first and fourth derivations (`xry.explore`, `fourth.explore`)
and re-checked
    The protocol is reading C6 of the earlier papers: round `k` attempts
    every change on every result first reached in round `k − 1`; a refused
    change is an attempt of its round that changes nothing; the bound is on
    terms and on rounds together (the fourth's C8′), the frontier in two
    parts.  The records are written again with the same fields.  What does
    not survive: the fourth's `count_sequences` relied on every change
    raising the round by one; here a change can lower the round, so what is
    counted is the number of *shortest* sequences (`count_shortest_sequences`),
    exact within the bound for the results the paper says (`sequences_exact`),
    and every result is reached by sequences of unbounded length (`cycle`).

Derived (paper, `lean4/Fifth/`)
    The round of a result is its cost (size difference plus twice the
    destroyed givens): a result is first met by a shortest sequence, whose
    states stay within the bound on terms.  Every answer is a sequence of
    performed changes, so answers reach nothing the changes do not reach
    (`check_answers`).
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field

from xry.changes import AnswerKind, Kind

from fifth.changes import Answer, Change, answers, changes, obstruction, perform
from fifth.state import MState, Pair, canonical, names_one_term

__all__ = [
    "AnswerCheck",
    "Attempt",
    "Exit",
    "Exploration",
    "attempt",
    "check_answers",
    "count_shortest_sequences",
    "cycle",
    "explore",
    "order",
    "performed",
    "removal_answers",
    "sequences_exact",
]


def order(state: MState) -> tuple[int, tuple[int, ...], int, int]:
    """A fixed order on states, for reproducible output."""
    a, b = state.names if state.names is not None else (-1, -1)
    return (state.n, state.mult, a, b)


@dataclass(frozen=True)
class Attempt:
    """One attempted change: the change, the obstruction, the outcome or answers.

    `outcome` is the result (least writing) of an unobstructed change within
    the bound; it is `None` for an obstructed change and for an outcome
    beyond the bound (`beyond`).
    """

    state: MState
    change: Change
    obstruction: tuple[Pair, ...]
    outcome: MState | None
    beyond: bool
    answers: tuple[Answer, ...]


@dataclass(frozen=True)
class Exit:
    """A frontier entry: an attempt that leaves the bound on terms, and how."""

    state: MState
    change: Change
    by: str


@dataclass
class Exploration:
    """Everything recorded by `explore`."""

    start: MState
    bound: int
    rounds: int
    depth: dict[MState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    obstructed_per_round: list[int]
    frontier: list[Exit]
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
    """Attempt `change` on the legal `state` and record what happens."""
    blocked = obstruction(state, change)
    if blocked:
        return Attempt(state, change, blocked, None, False, answers(state, change))
    out = perform(state, change)
    if out.n > bound:
        return Attempt(state, change, (), None, True, ())
    return Attempt(state, change, (), canonical(out), False, ())


def explore(start: MState, bound: int, rounds: int = 100, keep_log: bool = False) -> Exploration:
    """Explore from `start` for `rounds` rounds, keeping every result with at most `bound` terms.

    Round `r` attempts every change on every result first reached in round
    `r − 1`; the results first reached in round `rounds` are kept but their
    changes are not attempted.
    """
    if not start.legal:
        raise ValueError("what is given asserts no xrx")
    if start.n > bound:
        raise ValueError("the bound is below what is given")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")
    root = canonical(start)
    depth = {root: 0}
    wave = [root]
    new_per_round = [1]
    attempts_per_round = [0]
    obstructed_per_round = [0]
    frontier: list[Exit] = []
    log: list[Attempt] = []
    attempts_known = 0
    obstructed_known = 0
    for r in range(1, rounds + 1):
        found: list[MState] = []
        for state in wave:
            for change in changes(state):
                rec = attempt(state, change, bound)
                attempts_known += 1
                obstructed_known += bool(rec.obstruction)
                if rec.beyond:
                    frontier.append(Exit(state, change, "the change"))
                for ans in rec.answers:
                    if ans.result.n > bound:
                        frontier.append(Exit(state, change, ans.kind.value))
                if rec.outcome is not None and rec.outcome not in depth:
                    depth[rec.outcome] = r
                    found.append(rec.outcome)
                if keep_log:
                    log.append(rec)
        # Round r attempted every change on every result first reached in round r - 1.
        attempts_per_round.append(attempts_known)
        obstructed_per_round.append(obstructed_known)
        wave = sorted(found, key=order)
        new_per_round.append(len(wave))
    return Exploration(
        start=root,
        bound=bound,
        rounds=rounds,
        depth=depth,
        new_per_round=new_per_round,
        attempts_per_round=attempts_per_round,
        obstructed_per_round=obstructed_per_round,
        frontier=frontier,
        log=log,
    )


def performed(expl: Exploration) -> Iterator[tuple[MState, Change, MState]]:
    """Every unobstructed change within the bound on every result whose changes were attempted.

    Yields the result, the change, and the outcome (least writing), results
    in the order of their round and then the fixed order.  A result first
    reached in the last round has not had its changes attempted and is left
    out.  The outcome may be a result of an earlier round (a removal or an
    identification can go back), of the same round, or of the next.
    """
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        if expl.depth[state] >= expl.rounds:
            continue
        for change in changes(state):
            if obstruction(state, change):
                continue
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


def sequences_exact(expl: Exploration, state: MState) -> bool:
    """Is the count of shortest sequences to `state` exact within the bound on terms?

    A shortest sequence never has more terms than its target, except that a
    target with `a` and `b` one term may be built with them apart and merged
    last: one term more.
    """
    return state.n < expl.bound or not names_one_term(state)


def cycle(state: MState) -> tuple[Change, Change] | None:
    """Two changes that lead from `state` back to itself, if there are (there always are).

    With two terms `x ≠ y`: add `xry`, remove `xry`.  With one term: add a
    term, identify it with the one there.
    """
    if state.n >= 2:
        first, second = Change(Kind.ADD_ASSERTION, 0, 1), Change(Kind.REMOVE, 0, 1)
    elif state.n == 1:
        first, second = Change(Kind.ADD_TERM), Change(Kind.IDENTIFY, 0, 1)
    else:
        return None
    back = perform(perform(state, first), second)
    return (first, second) if back == state else None


@dataclass(frozen=True)
class AnswerCheck:
    """Totals of `check_answers`."""

    obstructed: int
    answers_within: int
    answers_beyond: int
    failures: tuple[str, ...]


def check_answers(expl: Exploration) -> AnswerCheck:
    """Check that no answer reaches anything the changes do not.

    For every obstructed attempt on every result whose changes were attempted
    and every answer within the bound (terms and rounds): the answer's result
    is an explored result, reached no later than the round of the state plus
    the changes the answer performs.
    """
    obstructed = within = beyond = 0
    failures: list[str] = []
    for state in sorted(expl.depth, key=order):
        if expl.depth[state] >= expl.rounds:
            continue
        for change in changes(state):
            if not obstruction(state, change):
                continue
            obstructed += 1
            for ans in answers(state, change):
                if ans.result.n > expl.bound or expl.depth[state] + ans.performed > expl.rounds:
                    beyond += 1
                    continue
                within += 1
                got = expl.depth.get(canonical(ans.result))
                if got is None or got > expl.depth[state] + ans.performed:
                    failures.append(f"{state.key()} / {change.written(state)} / {ans.kind.value}")
    return AnswerCheck(obstructed, within, beyond, tuple(failures))


def removal_answers(expl: Exploration) -> int:
    """How many recorded answers remove the obstruction (one per obstructed identification)."""
    return sum(
        1
        for state in expl.depth
        for change in changes(state)
        if obstruction(state, change)
        for ans in answers(state, change)
        if ans.kind is AnswerKind.REMOVE_OBSTRUCTION
    )
