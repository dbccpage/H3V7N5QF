"""An obstructed change is refused, and a refusal changes nothing.

`explore_refusing` does not use the base's obstruction test or its answers.
It performs every change and refuses the ones whose outcome asserts some
`xrx`, which is what the seed forbids. Comparing its closure with the base's
exploration (which spreads along the changes the base calls unobstructed) is
the computed form of "the reachable set is the base's".
"""

from __future__ import annotations

from dataclasses import dataclass

from xry.changes import changes, perform
from xry.explore import order
from xry.state import State, canonical


def refusal_result(state: State) -> State:
    """A refused change is recorded and changes nothing (given)."""
    return state


def refused(outcome: State) -> bool:
    """The outcome asserts some `xrx`, so the change that wrote it is refused."""
    return not outcome.legal


@dataclass
class RefusingExploration:
    """Results reached when every obstructed change is refused."""

    depth: dict[State, int]
    refusals: int


def explore_refusing(start: State, bound: int, rounds: int = 12) -> RefusingExploration:
    """Breadth-first, one change per round, every change attempted and performed unless refused."""
    if not start.legal:
        raise ValueError("what is given asserts no xrx")
    if start.n > bound:
        raise ValueError("the bound is below what is given")
    root = canonical(start)
    depth = {root: 0}
    wave = [root]
    refusals = 0
    for rnd in range(1, rounds + 1):
        found: list[State] = []
        for state in wave:
            for change in changes(state):
                out = perform(state, change)
                if refused(out):
                    refusals += 1
                    out = refusal_result(state)
                if out.n > bound:
                    continue
                out = canonical(out)
                if out not in depth:
                    depth[out] = rnd
                    found.append(out)
        wave = sorted(found, key=order)
        if not wave:
            break
    return RefusingExploration(depth, refusals)
