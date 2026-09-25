"""What does not follow: the ninth's statements about a result, read on its plain state.

Cited from the ninth derivation (`ninth.follows`) and re-checked (computed
again)
    `STATEMENTS` (the earlier unnamed one-relation statements on each part,
    the eighth's joint statements, nothing at all, unchanged by the exchange)
    are predicates on states.  Under reading C-R a statement about a result is
    read on its plain state, so each is evaluated on the explored results
    (least writings of plain states).  One of them, "some pair asserted in
    both relations", is false of every plain state by construction; the
    others are tested for holding and failing within the bound.
"""

from __future__ import annotations

from dataclasses import dataclass

from ninth.follows import STATEMENTS, Statement8

from twentysecond.explore import Exploration, order
from twentysecond.state import DState

__all__ = ["STATEMENTS", "Verdict", "verdict", "verdicts"]


@dataclass(frozen=True)
class Verdict:
    """Where a statement first holds and first fails among the explored results."""

    statement: str
    wording: str
    holds_at: DState | None
    holds_round: int | None
    fails_at: DState | None
    fails_round: int | None

    @property
    def in_every_result(self) -> bool:
        """The statement held in every explored result."""
        return self.fails_at is None

    @property
    def in_no_result(self) -> bool:
        """The statement held in no explored result."""
        return self.holds_at is None

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
        holds_at=holds,
        holds_round=None if holds is None else expl.depth[holds],
        fails_at=fails,
        fails_round=None if fails is None else expl.depth[fails],
    )


def verdicts(expl: Exploration) -> tuple[Verdict, ...]:
    """Verdicts for every statement tested."""
    return tuple(verdict(expl, s) for s in STATEMENTS)
