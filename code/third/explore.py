"""Attempting every change of the third seed on every alternative, round by round.

Given by the third seed
    Attempt every change, fewest additions first.  Attempt 100 changes along
    each alternative, finishing earlier changes on every alternative before
    later ones.  Do not invent a change to reach 100.  If the alternatives
    exceed what can be completed, declare a finite bound, export the exact
    frontier, and prove what is complete within it.

Cited from the first derivation (`xry.explore`) and re-checked
    The records (`Attempt`, `Exit`, `Exploration`, `AnswerCheck`) and the
    fixed order on states do not depend on which kinds of change there are.
    The protocol is reading C6 of the earlier papers: round `k` attempts
    every change on every result first reached in round `k - 1`; a refused
    change is an attempt of its round that changes nothing.  The declared
    bound is on the number of terms; the frontier lists every attempt whose
    outcome or whose answer has more terms than the bound.

Cited from the second derivation (`second.explore`) and re-checked
    The second derivation ran its exploration with identifications left out
    as a check; under the third seed that run is the whole exploration.
    `third.evidence` compares the two, result by result and round by round.

Derived (paper, `lean4/Third/`)
    Every change raises the size by exactly one, so every sequence of
    changes from what is given to a result has the same length: a result is
    met in one round only, and the number of sequences reaching it is exact
    within any bound that holds it (`count_sequences`).  Every answer is
    nothing (refusal) or two additions (a build), so answers reach nothing
    that the changes do not reach (`check_answers`).
"""

from __future__ import annotations

from collections.abc import Iterator

from xry.changes import AnswerKind, Change, obstruction
from xry.explore import AnswerCheck, Attempt, Exit, Exploration, order
from xry.state import State, canonical

from third.changes import answers, changes, perform

__all__ = [
    "AnswerCheck",
    "Attempt",
    "Exit",
    "Exploration",
    "attempt",
    "check_answers",
    "count_sequences",
    "explore",
    "order",
    "performed",
    "removal_answers",
]


def attempt(state: State, change: Change, bound: int) -> Attempt:
    """Attempt `change` on the legal `state` and record what happens."""
    blocked = obstruction(state, change)
    if blocked:
        return Attempt(state, change, blocked, None, False, answers(state, change))
    out = perform(state, change)
    if out.n > bound:
        return Attempt(state, change, (), None, True, ())
    return Attempt(state, change, (), canonical(out), False, ())


def explore(start: State, bound: int, rounds: int = 100, keep_log: bool = False) -> Exploration:
    """Explore from `start`, keeping every result with at most `bound` terms."""
    if not start.legal:
        raise ValueError("what is given asserts no xrx")
    if start.n > bound:
        raise ValueError("the bound is below what is given")
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
        found: list[State] = []
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


def performed(expl: Exploration) -> Iterator[tuple[State, Change, State]]:
    """Every unobstructed change within the bound on every result whose changes were attempted.

    Yields the result, the change, and the outcome (least writing), results
    in the order of their round and then the fixed order.  A result first
    reached in the last round has not had its changes attempted (its outcomes
    are not results of the exploration) and is left out; with 100 rounds no
    result is left out.
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


def count_sequences(expl: Exploration) -> dict[State, int]:
    """How many sequences of changes reach each explored result from what is given.

    A sequence is counted change by change: two changes on one result that
    differ (as listed) count as two, even when their outcomes are the same
    result.  The count is exact for every result within the bound, since no
    sequence has more terms than the result it reaches.  It relies on every
    change raising the round by one, which is checked here and is a theorem
    of the paper.
    """
    sequences = {state: 0 for state in expl.depth}
    sequences[expl.start] = 1
    for state, change, out in performed(expl):
        if expl.depth[out] != expl.depth[state] + 1:
            raise ValueError(f"{change.written(state)} on {state.key()} does not raise the round by one")
        sequences[out] += sequences[state]
    return sequences


def check_answers(expl: Exploration) -> AnswerCheck:
    """Check that no answer reaches anything the changes do not.

    For every obstructed attempt on every explored result and every answer
    within the bound: the answer's result is an explored result, reached no
    later than the round of the state plus the changes the answer performs.
    """
    obstructed = within = beyond = 0
    failures: list[str] = []
    for state in sorted(expl.depth, key=order):
        for change in changes(state):
            if not obstruction(state, change):
                continue
            obstructed += 1
            for ans in answers(state, change):
                if ans.result.n > expl.bound:
                    beyond += 1
                    continue
                within += 1
                got = expl.depth.get(canonical(ans.result))
                if got is None or got > expl.depth[state] + ans.performed:
                    failures.append(f"{state.key()} / {change.written(state)} / {ans.kind.value}")
    return AnswerCheck(obstructed, within, beyond, tuple(failures))


def removal_answers(expl: Exploration) -> int:
    """How many recorded answers remove the obstruction (none can, under this seed)."""
    return sum(
        1
        for state in expl.depth
        for change in changes(state)
        if obstruction(state, change)
        for ans in answers(state, change)
        if ans.kind is AnswerKind.REMOVE_OBSTRUCTION
    )
