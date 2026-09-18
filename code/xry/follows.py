"""Statements about a state, and witnesses that they do not follow.

Computed.  A statement *does not follow* when some result satisfies it and
some result violates it.  For each statement below the exploration is
searched for the earliest result where it holds and the earliest where it
fails.  A statement found to hold in every explored result is only reported
as such; whether it holds in every result at all needs a proof (paper).

The statements are about the asserting of `xry` only.  None of them is
given by the seed; they are candidates a reader might expect.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from xry.explore import Exploration, order
from xry.state import State


def _names(state: State) -> tuple[int, int]:
    if state.names is None:
        raise ValueError("this statement mentions a and b; the state has no names")
    return state.names


def bra_asserted(state: State) -> bool:
    """`bra` is asserted."""
    a, b = _names(state)
    return a != b and state.has(b, a)


def arb_asserted(state: State) -> bool:
    """`arb` is asserted."""
    a, b = _names(state)
    return a != b and state.has(a, b)


def names_apart(state: State) -> bool:
    """`a` and `b` are two terms."""
    a, b = _names(state)
    return a != b


def both_ways_always(state: State) -> bool:
    """Whenever `xry` is asserted, `yrx` is asserted."""
    return all(state.has(y, x) for x, y in state.pairs)


def both_ways_never(state: State) -> bool:
    """Never are `xry` and `yrx` both asserted."""
    return not any(state.has(y, x) for x, y in state.pairs)


def passes_on(state: State) -> bool:
    """Whenever `xry` and `yrz` are asserted, `xrz` is asserted."""
    return all(
        state.has(x, z) for x, y in state.pairs for y2, z in state.pairs if y2 == y
    )


def any_two_related(state: State) -> bool:
    """For any two terms `x`, `y`: `xry` or `yrx` is asserted."""
    n = state.n
    return all(state.related(x, y) for x in range(n) for y in range(x + 1, n))


def every_term_first(state: State) -> bool:
    """Every term `x` has some `xry` asserted."""
    firsts = {x for x, _ in state.pairs}
    return len(firsts) == state.n


def every_term_mentioned(state: State) -> bool:
    """Every term occurs in some asserted assertion."""
    mentioned = {t for pair in state.pairs for t in pair}
    return len(mentioned) == state.n


def exactly_two_terms(state: State) -> bool:
    """There are exactly two terms."""
    return state.n == 2


def something_asserted(state: State) -> bool:
    """Some assertion is asserted."""
    return state.m > 0


def at_least_one_term(state: State) -> bool:
    """There is at least one term."""
    return state.n >= 1


def no_xrx(state: State) -> bool:
    """No `xrx` is asserted."""
    return state.legal


Statement = Callable[[State], bool]

#: Statements that need the names `a`, `b`.
NAMED: tuple[Statement, ...] = (bra_asserted, arb_asserted, names_apart)

#: Statements about the asserting only.
UNNAMED: tuple[Statement, ...] = (
    both_ways_always,
    both_ways_never,
    passes_on,
    any_two_related,
    every_term_first,
    every_term_mentioned,
    exactly_two_terms,
    something_asserted,
    at_least_one_term,
    no_xrx,
)


@dataclass(frozen=True)
class Verdict:
    """Where a statement first holds and first fails in an exploration."""

    statement: str
    wording: str
    in_given: bool
    holds_at: State | None
    holds_round: int | None
    fails_at: State | None
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
    holds: State | None = None
    fails: State | None = None
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
    return tuple(verdict(expl, s) for s in chosen)
