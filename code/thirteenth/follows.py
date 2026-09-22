"""Statements about coarser writings, and witnesses that they do not follow.

Computed.  A statement about a *coarser writing of a result* does not follow
when some result satisfies it and some result violates it.  The ninth's
statements about states are imported and re-checked: a coarser writing is
not in the state, so their verdicts are the ninth's.

Cited from the ninth derivation (`ninth.follows`) and re-checked
    Every statement about a two-relation state mentions no coarser writing:
    the verdicts survive.  No tested statement holds in every result (9:D14).
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from ninth.follows import (
    EXTRA_NINTH,
    JOINT,
    ONE_RELATION,
    STATEMENTS,
    Statement,
    Statement8,
    Verdict,
    nothing_at_all,
    unchanged_by_exchange,
    verdict,
)
from ninth.follows import verdicts as verdicts_ninth
from ninth.state import DState, same

from thirteenth.coarse import determines, same_coarser, splits
from thirteenth.explore import Exploration
from thirteenth.state import swap

__all__ = [
    "COARSE_STATEMENTS",
    "EXTRA_NINTH",
    "JOINT",
    "ONE_RELATION",
    "STATEMENTS",
    "CoarseVerdict",
    "Statement",
    "Statement8",
    "Verdict",
    "both_relations",
    "coarse_verdicts",
    "determines_finer",
    "nothing_at_all",
    "swap_same_coarse",
    "unchanged_by_exchange",
    "unique_split",
    "verdict",
    "verdicts",
]


def determines_finer(state: DState) -> bool:
    """The coarser writing determines this finer result."""
    return determines(state)


def unique_split(state: DState) -> bool:
    """This writing of the terms has only one finer split of the coarser writing."""
    return splits(state) == 1


def swap_same_coarse(state: DState) -> bool:
    """Exchanging the relations keeps the coarser writing and is a different finer result.

    "Different finer result" is difference up to writing (`not same`), not a
    difference in the written multiplicity tuples: a state and its exchange can
    have `r != s` yet be the same result up to renaming the terms.
    """
    return same_coarser(state, swap(state)) and not same(state, swap(state))


def both_relations(state: DState) -> bool:
    """Something is asserted in each relation."""
    return state.total_r > 0 and state.total_s > 0


COARSE_STATEMENTS: tuple[tuple[str, Callable[[DState], bool]], ...] = (
    ("determines_finer", determines_finer),
    ("unique_split", unique_split),
    ("swap_same_coarse", swap_same_coarse),
    ("both_relations", both_relations),
)


@dataclass(frozen=True)
class CoarseVerdict:
    """Where a coarser statement first holds and first fails among results."""

    name: str
    holds_at: str | None
    fails_at: str | None

    @property
    def follows(self) -> bool:
        """Does the statement hold of every explored result?"""
        return self.fails_at is None and self.holds_at is not None


def verdicts(expl: Exploration) -> tuple[Verdict, ...]:
    """The ninth's state-statements, on this exploration (C-C1: the same results)."""
    from ninth.explore import Exploration as NinthExploration

    ninth = NinthExploration(
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
    return verdicts_ninth(ninth)


def coarse_verdicts(expl: Exploration) -> tuple[CoarseVerdict, ...]:
    """For each coarser statement, the earliest result where it holds and where it fails."""
    found: dict[str, list[str | None]] = {name: [None, None] for name, _ in COARSE_STATEMENTS}
    results = sorted(expl.depth, key=lambda s: (expl.depth[s], s.n, s.key()))
    for state in results:
        written = state.key()
        for name, pred in COARSE_STATEMENTS:
            slot = 0 if pred(state) else 1
            if found[name][slot] is None:
                found[name][slot] = written
    return tuple(CoarseVerdict(name, found[name][0], found[name][1]) for name, _ in COARSE_STATEMENTS)
