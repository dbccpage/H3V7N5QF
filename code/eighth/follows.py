"""Statements about a two-relation state, and witnesses that they do not follow (eighth seed).

Computed.  A statement *does not follow* when some result satisfies it and
some result violates it.  For each statement the exploration is searched for
the earliest result where it holds and the earliest where it fails.

Cited from the fourth, fifth and sixth derivations (`fourth.follows`,
`fifth.follows`, `sixth.follows`) and re-checked
    The statements are about one multiplicity function; each survives as a
    statement about the `r` part and as one about the `s` part (`on_part`,
    with the wording rewritten for `s`).  New are the joint statements
    (`JOINT`): nothing in `s`; nothing in `r`; some pair asserted in both
    relations; the two relations agree everywhere; every `s` assertion has
    its `r` twin, and the converse.  `Verdict` and `verdict` are written
    again with the same fields.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from fifth.follows import EXTRA_NAMED, EXTRA_UNNAMED
from fourth.follows import COUNTED, NAMED, UNNAMED, Statement
from sixth.follows import EXTRA_SIXTH

from eighth.explore import Exploration, order
from eighth.state import DState

__all__ = ["JOINT", "Statement8", "Verdict", "on_part", "statements", "verdict", "verdicts"]

Statement8 = Callable[[DState], bool]

_REWORD = (("xry", "xsy"), ("yrx", "ysx"), ("xrz", "xsz"), ("xrx", "xsx"), ("arb", "asb"), ("bra", "bsa"), ("yrz", "ysz"))


def on_part(statement: Statement, rel: str) -> Statement8:
    """The earlier statement, read on the `r` part or the `s` part."""

    def on_one(state: DState) -> bool:
        return statement(state.part(rel))

    doc = (statement.__doc__ or "").strip()
    if rel == "s":
        for old, new in _REWORD:
            doc = doc.replace(old, new)
    on_one.__name__ = f"{statement.__name__}_{rel}"
    on_one.__doc__ = f"In `{rel}`: {doc}"
    return on_one


def nothing_in_s(state: DState) -> bool:
    """Nothing is asserted with `s`."""
    return state.total_s == 0


def nothing_in_r(state: DState) -> bool:
    """Nothing is asserted with `r`."""
    return state.total_r == 0


def some_pair_in_both(state: DState) -> bool:
    """Some `xry` and `xsy` are both asserted."""
    return any(kr and ks for kr, ks in zip(state.r, state.s))


def relations_agree(state: DState) -> bool:
    """Every `xry` is asserted exactly as often as `xsy`."""
    return state.r == state.s


def s_within_r(state: DState) -> bool:
    """Whenever `xsy` is asserted, `xry` is asserted."""
    return all(kr for kr, ks in zip(state.r, state.s) if ks)


def r_within_s(state: DState) -> bool:
    """Whenever `xry` is asserted, `xsy` is asserted."""
    return all(ks for kr, ks in zip(state.r, state.s) if kr)


#: Statements about both relations together.
JOINT: tuple[Statement8, ...] = (nothing_in_s, nothing_in_r, some_pair_in_both, relations_agree, s_within_r, r_within_s)


def statements(named: bool) -> tuple[Statement8, ...]:
    """Every statement tested: the earlier ones on each part, then the joint ones."""
    one: tuple[Statement, ...] = (NAMED + EXTRA_NAMED if named else ()) + UNNAMED + EXTRA_UNNAMED + EXTRA_SIXTH + COUNTED
    return tuple(on_part(s, "r") for s in one) + tuple(on_part(s, "s") for s in one) + JOINT


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
    """Verdicts for every statement that makes sense for the exploration."""
    return tuple(verdict(expl, s) for s in statements(expl.start.names is not None))
