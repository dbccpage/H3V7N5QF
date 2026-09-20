"""Statements about a two-relation state, and witnesses that they do not follow (ninth seed).

Computed.  A statement *does not follow* when some result satisfies it and
some result violates it.  For each statement the exploration is searched for
the earliest result where it holds and the earliest where it fails.

Cited from the fourth to eighth derivations (`fourth.follows`,
`fifth.follows`, `sixth.follows`, `seventh.follows`, `eighth.follows`) and
re-checked
    The statements that mention no name (`UNNAMED`, `COUNTED`,
    `EXTRA_UNNAMED`, `EXTRA_SIXTH`) are about one-relation states; each
    survives as a statement about the `r` part and as one about the `s` part
    (the eighth's `on_part`, with the wording rewritten for `s`).  The
    eighth's joint statements (`JOINT`: nothing in `s`; nothing in `r`; some
    pair asserted in both relations; the two relations agree everywhere;
    every `s` assertion has its `r` twin, and the converse) mention no name
    and survive.  The named ones (`arb` asserted, `a`, `b` two terms, the
    names one term) have no object and are not imported.  Which statements
    hold in every result changes once more: every well-formed state is a
    result, the empty one included, so the eighth's "at least one term" (on
    either part) fails at round 0 and *no* tested statement holds in every
    result.  `Verdict` and `verdict` are written again for this exploration
    with the same fields.  New statements: nothing at all (no terms and
    nothing asserted, true of what is given alone, the seventh's); the state
    unchanged by exchanging the two relations (`unchanged_by_exchange`, a
    symmetry the eighth seed did not have).
"""

from __future__ import annotations

from dataclasses import dataclass

from eighth.follows import JOINT, Statement8, on_part
from fifth.follows import EXTRA_UNNAMED
from fourth.follows import COUNTED, UNNAMED, Statement
from sixth.follows import EXTRA_SIXTH

from ninth.explore import Exploration, order
from ninth.state import DState, same, swap

__all__ = [
    "EXTRA_NINTH",
    "JOINT",
    "ONE_RELATION",
    "STATEMENTS",
    "Statement",
    "Statement8",
    "Verdict",
    "nothing_at_all",
    "unchanged_by_exchange",
    "verdict",
    "verdicts",
]


def nothing_at_all(state: DState) -> bool:
    """There are no terms and nothing is asserted."""
    return state.n == 0


def unchanged_by_exchange(state: DState) -> bool:
    """Exchanging the two relations gives the same result (up to rewriting the terms)."""
    return same(state, swap(state))


#: Statements added for the ninth seed.
EXTRA_NINTH: tuple[Statement8, ...] = (nothing_at_all, unchanged_by_exchange)

#: The earlier derivations' unnamed statements about one relation, read on each part.
ONE_RELATION: tuple[Statement, ...] = UNNAMED + EXTRA_UNNAMED + EXTRA_SIXTH + COUNTED

#: Every statement tested: the one-relation ones on each part, the eighth's joint ones, then this seed's.
STATEMENTS: tuple[Statement8, ...] = (
    tuple(on_part(s, "r") for s in ONE_RELATION) + tuple(on_part(s, "s") for s in ONE_RELATION) + JOINT + EXTRA_NINTH
)


@dataclass(frozen=True)
class Verdict:
    """Where a statement first holds and first fails in an exploration."""

    statement: str
    wording: str
    in_given: bool
    holds_at: DState | None
    holds_round: int | None
    fails_at: DState | None
    fails_round: int | None

    @property
    def follows_within_bound(self) -> bool:
        """The statement held in every explored result."""
        return self.fails_at is None

    @property
    def independent(self) -> bool:
        """Some explored result satisfies it and some violates it."""
        return self.holds_at is not None and self.fails_at is not None


def verdict(expl: Exploration, statement: Statement8) -> Verdict:
    """Earliest results (round, then fixed order) where `statement` holds / fails."""
    holds: DState | None = None
    fails: DState | None = None
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
