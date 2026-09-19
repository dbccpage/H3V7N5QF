"""Statements about a counted state, and witnesses that they do not follow (seventh seed).

Computed.  A statement *does not follow* when some result satisfies it and
some result violates it.  For each statement the exploration is searched for
the earliest result where it holds and the earliest where it fails.

Cited from the fourth, fifth and sixth derivations (`fourth.follows`,
`fifth.follows`, `sixth.follows`) and re-checked
    The statements that mention no name (`UNNAMED`, `COUNTED`,
    `EXTRA_UNNAMED`, `EXTRA_SIXTH`) are about states, not the given, and
    survive as statements; the named ones (`arb` asserted, `a`, `b` two
    terms, `arb` once, the names one term) have no object and are not
    imported.  Which statements hold in every result changes once more:
    every well-formed state is a result, the empty one included, so the
    sixth's "at least one term" fails at round 0 and *no* tested statement
    holds in every result.  `Verdict` and `verdict` are written again for
    this exploration with the same fields.  New statement: nothing at all
    (no terms and nothing asserted), true of what is given alone.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from fifth.follows import EXTRA_UNNAMED
from fourth.follows import COUNTED, UNNAMED, Statement
from sixth.follows import EXTRA_SIXTH

from seventh.explore import Exploration, order
from seventh.state import MState

__all__ = [
    "COUNTED",
    "EXTRA_SEVENTH",
    "EXTRA_SIXTH",
    "EXTRA_UNNAMED",
    "STATEMENTS",
    "UNNAMED",
    "Statement",
    "Verdict",
    "nothing_at_all",
    "verdict",
    "verdicts",
]


def nothing_at_all(state: MState) -> bool:
    """There are no terms and nothing is asserted."""
    return state.n == 0


#: Statements added for the seventh seed.
EXTRA_SEVENTH: tuple[Statement, ...] = (nothing_at_all,)

#: Every statement tested: the earlier derivations' unnamed ones, then this seed's.
STATEMENTS: tuple[Statement, ...] = UNNAMED + EXTRA_UNNAMED + EXTRA_SIXTH + COUNTED + EXTRA_SEVENTH


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
    """Verdicts for every statement tested."""
    return tuple(verdict(expl, s) for s in STATEMENTS)
