"""Reachable states when identification rewrites one assertion."""

from __future__ import annotations

from dataclasses import dataclass, field

from xry.changes import Kind, obstruction, perform
from xry.explore import order
from xry.state import State, canonical

from nineteenth.changes import Partial, obstructed, other_changes, partials, perform_partial


@dataclass
class PartialExploration:
    """Results up to the base sameness, and how many partial steps were obstructed."""

    start: State
    bound: int
    depth: dict[State, int]
    new_per_round: list[int]
    obstructed_partials: int
    performed_partials: int
    min_terms: int
    frontier: int
    log: list[str] = field(default_factory=list)


def explore_partial(
    start: State,
    bound: int,
    rounds: int = 12,
    cooccur_only: bool = False,
    keep_log: bool = False,
) -> PartialExploration:
    """Unobstructed changes only. An obstructed partial identification is refused."""
    if not start.legal:
        raise ValueError("what is given asserts no xrx")
    if start.n > bound:
        raise ValueError("the bound is below what is given")
    root = canonical(start)
    depth = {root: 0}
    wave = [root]
    new_per_round = [1]
    obstructed_partials = 0
    performed_partials = 0
    frontier = 0
    log: list[str] = []
    for rnd in range(1, rounds + 1):
        found: list[State] = []
        for state in wave:
            for change in other_changes(state):
                if change.kind is Kind.ADD_TERM and state.n >= bound:
                    frontier += 1
                    continue
                if obstruction(state, change):
                    continue
                out = canonical(perform(state, change))
                if out not in depth:
                    depth[out] = rnd
                    found.append(out)
            for partial in partials(state, cooccur_only):
                if obstructed(state, partial):
                    obstructed_partials += 1
                    if keep_log:
                        log.append("obstructed " + partial.written(state))
                    continue
                performed_partials += 1
                out = canonical(perform_partial(state, partial))
                if out not in depth:
                    depth[out] = rnd
                    found.append(out)
                if keep_log:
                    log.append(partial.written(state))
        wave = sorted(found, key=order)
        new_per_round.append(len(wave))
        if not wave:
            break
    return PartialExploration(
        root,
        bound,
        depth,
        new_per_round,
        obstructed_partials,
        performed_partials,
        min(state.n for state in depth),
        frontier,
        log,
    )
