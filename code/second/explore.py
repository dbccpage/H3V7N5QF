"""Attempting every change of the second seed on every alternative, round by round.

Given by the second seed
    Attempt every change, fewest additions first.  Attempt 100 changes along
    each alternative, finishing earlier changes on every alternative before
    later ones.  Do not invent a change to reach 100.  If the alternatives
    exceed what can be completed, declare a finite bound, export the exact
    frontier, and prove what is complete within it.

Cited from the first derivation (`xry.explore`) and re-checked
    The records (`Attempt`, `Exit`, `Exploration`, `AnswerCheck`), the fixed
    order on states and `rigid` do not depend on which kinds of change there
    are.  The protocol is the first derivation's reading C6: round `k`
    attempts every change on every result first reached in round `k - 1`,
    each result's changes fewest additions first; a refused change is an
    attempt of its round that changes nothing.  The declared bound is on the
    number of terms; the frontier lists every attempt whose outcome or whose
    answer has more terms than the bound.

Derived (paper, `lean4/Second/`)
    Every answer is nothing (refusal) or a sequence of additions (a build), so
    answers reach nothing that unobstructed changes do not reach; and every
    result is reached by additions alone.  The exploration spreads along the
    unobstructed changes and checks the answers afterwards (`check_answers`);
    `explore(..., additions_only=True)` is compared with the full exploration
    in `second.evidence`.
"""

from __future__ import annotations

from xry.changes import AnswerKind, Change, Kind, obstruction
from xry.explore import AnswerCheck, Attempt, Exit, Exploration, order, rigid
from xry.state import State, canonical

from second.changes import answers, changes, perform

__all__ = [
    "AnswerCheck",
    "Attempt",
    "Exit",
    "Exploration",
    "attempt",
    "check_answers",
    "explore",
    "order",
    "removal_answers",
    "rigid",
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


def explore(
    start: State,
    bound: int,
    rounds: int = 100,
    keep_log: bool = False,
    additions_only: bool = False,
) -> Exploration:
    """Explore from `start`, keeping every result with at most `bound` terms.

    With `additions_only` the identifications are not attempted; the result
    is compared with the full exploration as a computed check that
    identifications reach nothing new.
    """
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
                if additions_only and change.kind is Kind.IDENTIFY:
                    continue
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


def check_answers(expl: Exploration) -> AnswerCheck:
    """Check that no answer reaches anything the unobstructed changes do not.

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
