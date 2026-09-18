"""Statements about a counted state, and witnesses that they do not follow (fourth seed).

Computed.  A statement *does not follow* when some result satisfies it and
some result violates it.  For each statement below the exploration is
searched for the earliest result where it holds and the earliest where it
fails.  A statement found to hold in every explored result is only reported
as such; whether it holds in every result at all needs a proof (paper).

Cited from the first and second derivations (`xry.follows`, `second.follows`)
and re-checked
    The earlier statements are about which `xry` are asserted; each survives
    the counting as a statement about the support of a counted state and is
    tested on it (`lifted`).  `Verdict` and `verdict` are written again for
    counted states with the same fields.  Statements about multiplicity are
    new (`COUNTED`).
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from second.follows import EXTRA as EXTRA_SECOND
from xry.follows import NAMED as NAMED_SUPPORT
from xry.follows import UNNAMED as UNNAMED_SUPPORT
from xry.state import State

from fourth.explore import Exploration, order
from fourth.state import MState, support

__all__ = ["COUNTED", "NAMED", "UNNAMED", "Statement", "Verdict", "lifted", "verdict", "verdicts"]

Statement = Callable[[MState], bool]


def lifted(statement: Callable[[State], bool]) -> Statement:
    """The earlier statement, read on the support of a counted state."""

    def on_support(state: MState) -> bool:
        return statement(support(state))

    on_support.__name__ = statement.__name__
    on_support.__doc__ = statement.__doc__
    return on_support


def nothing_twice(state: MState) -> bool:
    """No assertion is asserted more than once."""
    return state.simple


def something_twice(state: MState) -> bool:
    """Some assertion is asserted at least twice."""
    return not state.simple


def arb_once(state: MState) -> bool:
    """`arb` is asserted exactly once."""
    if state.names is None:
        raise ValueError("this statement mentions a and b; the state has no names")
    a, b = state.names
    return a != b and state.mult_of(a, b) == 1


def same_multiplicity(state: MState) -> bool:
    """Every asserted assertion is asserted equally often."""
    return len({k for _, _, k in state.counted}) <= 1


def both_ways_equal(state: MState) -> bool:
    """Whenever `xry` and `yrx` are both asserted, they are asserted equally often."""
    return all(
        state.mult_of(x, y) == state.mult_of(y, x)
        for x, y, _ in state.counted
        if state.has(y, x)
    )


#: Statements that need the names `a`, `b`.
NAMED: tuple[Statement, ...] = tuple(lifted(s) for s in NAMED_SUPPORT) + (arb_once,)

#: Statements about which assertions are asserted (the earlier derivations').
UNNAMED: tuple[Statement, ...] = tuple(lifted(s) for s in UNNAMED_SUPPORT + EXTRA_SECOND)

#: Statements about multiplicity, new to this seed.
COUNTED: tuple[Statement, ...] = (nothing_twice, something_twice, same_multiplicity, both_ways_equal)


@dataclass(frozen=True)
class Verdict:
    """Where a statement first holds and first fails in an exploration."""

    statement: str
    wording: str
    in_given: bool
    holds_at: MState | None
    holds_round: int | None
    fails_at: MState | None
    fails_round: int | None

    @property
    def follows_within_bound(self) -> bool:
        """The statement held in every explored result."""
        return self.fails_at is None

    @property
    def independent(self) -> bool:
        """Some explored result satisfies it and some violates it."""
        return self.holds_at is not None and self.fails_at is not None


def verdict(expl: Exploration, statement: Statement) -> Verdict:
    """Earliest results (round, then fixed order) where `statement` holds / fails."""
    holds: MState | None = None
    fails: MState | None = None
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        if statement(state):
            holds = holds if holds is not None else state
        else:
            fails = fails if fails is not None else state
    return Verdict(
        statement=statement.__name__,
        wording=(statement.__doc__ or "").strip(),
        in_given=statement(expl.start),
        holds_at=holds,
        holds_round=None if holds is None else expl.depth[holds],
        fails_at=fails,
        fails_round=None if fails is None else expl.depth[fails],
    )


def verdicts(expl: Exploration) -> tuple[Verdict, ...]:
    """Verdicts for every statement that makes sense for the exploration."""
    chosen = UNNAMED if expl.start.names is None else NAMED + UNNAMED
    return tuple(verdict(expl, s) for s in chosen + COUNTED)
