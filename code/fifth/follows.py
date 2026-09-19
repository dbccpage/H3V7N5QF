"""Statements about a counted state, and witnesses that they do not follow (fifth seed).

Computed.  A statement *does not follow* when some result satisfies it and
some result violates it.  For each statement the exploration is searched for
the earliest result where it holds and the earliest where it fails.

Cited from the fourth derivation (`fourth.follows`) and re-checked
    The statements are about states, not changes, and survive as statements;
    which of them hold in every result changes: every legal state with at
    least one term is now a result, so only "no `xrx`" and "at least one
    term" can hold everywhere (the fourth's `arb` asserted, `a`, `b` two
    terms, something asserted, at least two terms fall).  `Verdict` and
    `verdict` are written again for this exploration with the same fields.
    New statements: the names are one term; nothing is asserted.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from fourth.follows import COUNTED, NAMED, UNNAMED, Statement

from fifth.explore import Exploration, order
from fifth.state import MState, names_one_term

__all__ = ["COUNTED", "EXTRA_NAMED", "EXTRA_UNNAMED", "NAMED", "UNNAMED", "Statement", "Verdict", "verdict", "verdicts"]


def names_merged(state: MState) -> bool:
    """`a` and `b` are one term."""
    if state.names is None:
        raise ValueError("this statement mentions a and b; the state has no names")
    return names_one_term(state)


def nothing_asserted(state: MState) -> bool:
    """Nothing is asserted."""
    return state.m == 0


#: Statements added for the fifth seed.
EXTRA_NAMED: tuple[Statement, ...] = (names_merged,)
EXTRA_UNNAMED: tuple[Statement, ...] = (nothing_asserted,)


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


def verdict(expl: Exploration, statement: Callable[[MState], bool]) -> Verdict:
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
    chosen = UNNAMED if expl.start.names is None else NAMED + EXTRA_NAMED + UNNAMED
    return tuple(verdict(expl, s) for s in chosen + EXTRA_UNNAMED + COUNTED)
