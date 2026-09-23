"""Exploration that does not rewrite a result into another writing.

The changes are the base's. The outcome of an unobstructed change is kept
as `perform` writes it. `canonical` is not applied.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from xry.changes import Change, answers, changes, obstruction, perform
from xry.explore import Exit, order
from xry.state import State


@dataclass(frozen=True)
class WrittenAttempt:
    """One attempted change and the writing it reaches, if it is performed."""

    state: State
    change: Change
    obstructed: bool
    outcome: State | None
    beyond: bool


@dataclass
class WrittenExploration:
    """Results reached as written, and the attempts that leave the term bound."""

    start: State
    bound: int
    rounds: int
    depth: dict[State, int]
    new_per_round: list[int]
    frontier: list[Exit]
    log: list[WrittenAttempt] = field(default_factory=list)


def explore_written(
    start: State, bound: int, rounds: int = 100, keep_log: bool = False
) -> WrittenExploration:
    """Reachable legal states as written, with at most `bound` terms."""
    if not start.legal:
        raise ValueError("what is given asserts no xrx")
    if start.n > bound:
        raise ValueError("the bound is below what is given")
    depth = {start: 0}
    wave = [start]
    new_per_round = [1]
    frontier: list[Exit] = []
    log: list[WrittenAttempt] = []
    for rnd in range(1, rounds + 1):
        found: list[State] = []
        for state in wave:
            for change in changes(state):
                blocked = bool(obstruction(state, change))
                beyond = False
                outcome: State | None = None
                if not blocked:
                    out = perform(state, change)
                    if not out.legal:
                        raise RuntimeError("an unobstructed change asserted xrx")
                    if out.n > bound:
                        beyond = True
                        frontier.append(Exit(state, change, "the change"))
                    else:
                        outcome = out
                        if out not in depth:
                            depth[out] = rnd
                            found.append(out)
                if keep_log:
                    log.append(WrittenAttempt(state, change, blocked, outcome, beyond))
        wave = sorted(found, key=order)
        new_per_round.append(len(wave))
    return WrittenExploration(start, bound, rounds, depth, new_per_round, frontier, log)


def answer_other_writing(expl: WrittenExploration) -> list[str]:
    """Answers whose written result the unobstructed changes have not reached."""
    missing: list[str] = []
    for state in sorted(expl.depth, key=order):
        for change in changes(state):
            if not obstruction(state, change):
                continue
            for ans in answers(state, change):
                if ans.result.n > expl.bound:
                    continue
                if ans.result not in expl.depth:
                    missing.append(f"{state.key()} / {change.written(state)} / {ans.kind.value}")
    return missing
