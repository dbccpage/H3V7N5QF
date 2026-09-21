"""Statements about leftover, and witnesses that they do not follow (tenth seed).

Computed.  A statement about a *change* does not follow when some performed
change satisfies it and some performed change violates it.  The ninth's
statements about states are imported and re-checked: leftover is not in the
state, so their verdicts are the ninth's.

Cited from the ninth derivation (`ninth.follows`) and re-checked
    Every statement about a two-relation state mentions no leftover: the
    verdicts survive.  No tested statement holds in every result (9:D14).
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

from tenth.explore import Exploration, leftover_performed
from tenth.leftover import LeftOver

__all__ = [
    "EXTRA_NINTH",
    "JOINT",
    "LEFTOVER_STATEMENTS",
    "ONE_RELATION",
    "STATEMENTS",
    "Statement",
    "Statement8",
    "Verdict",
    "LeftoverVerdict",
    "leaves_clearable",
    "leaves_nothing",
    "leaves_uncleared",
    "leftover_verdicts",
    "nothing_at_all",
    "unchanged_by_exchange",
    "verdict",
    "verdicts",
]


def leaves_nothing(leftover: LeftOver) -> bool:
    """The change left nothing."""
    return leftover is LeftOver.NOTHING_LEFT


def leaves_clearable(leftover: LeftOver) -> bool:
    """The change left a leftover that a later change of the four kinds can clear."""
    return leftover is LeftOver.CLEARABLE


def leaves_uncleared(leftover: LeftOver) -> bool:
    """The change left a leftover that none of the four kinds can clear."""
    return leftover is LeftOver.UNCLEARED


LEFTOVER_STATEMENTS: tuple[tuple[str, Callable[[LeftOver], bool]], ...] = (
    ("leaves_nothing", leaves_nothing),
    ("leaves_clearable", leaves_clearable),
    ("leaves_uncleared", leaves_uncleared),
)


@dataclass(frozen=True)
class LeftoverVerdict:
    """Where a leftover statement first holds and first fails among performed changes."""

    name: str
    holds_at: tuple[str, str] | None
    fails_at: tuple[str, str] | None

    @property
    def follows(self) -> bool:
        """Does the statement hold of every performed change in the exploration?"""
        return self.fails_at is None and self.holds_at is not None


def verdicts(expl: Exploration) -> tuple[Verdict, ...]:
    """The ninth's state-statements, on this exploration (C-L1: the same results)."""
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


def leftover_verdicts(expl: Exploration) -> tuple[LeftoverVerdict, ...]:
    """For each leftover statement, the earliest change where it holds and where it fails."""
    found: dict[str, list[tuple[str, str] | None]] = {name: [None, None] for name, _ in LEFTOVER_STATEMENTS}
    for state, change, _out, leftover in leftover_performed(expl):
        written_state = state.key()
        written_change = change.written(state)
        for name, pred in LEFTOVER_STATEMENTS:
            slot = 0 if pred(leftover) else 1
            if found[name][slot] is None:
                found[name][slot] = (written_state, written_change)
    return tuple(LeftoverVerdict(name, found[name][0], found[name][1]) for name, _ in LEFTOVER_STATEMENTS)
