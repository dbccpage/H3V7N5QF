"""Statements about writings, and witnesses that they do not follow (eleventh seed).

Computed.  A statement about a *writing of a result* does not follow when
some (state, writing) pair satisfies it and some pair violates it.  The
ninth's statements about states are imported and re-checked: a writing is
not in the state, so their verdicts are the ninth's.

Cited from the ninth derivation (`ninth.follows`) and re-checked
    Every statement about a two-relation state mentions no writing: the
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

from eleventh.explore import Exploration, writings_of
from eleventh.state import DState
from eleventh.writing import determines, determines_rel, injective

__all__ = [
    "EXTRA_NINTH",
    "JOINT",
    "ONE_RELATION",
    "STATEMENTS",
    "Statement",
    "Statement8",
    "Verdict",
    "WritingVerdict",
    "WRITING_STATEMENTS",
    "collides",
    "determines_both",
    "is_injective",
    "nothing_at_all",
    "unchanged_by_exchange",
    "verdict",
    "verdicts",
    "writing_verdicts",
]


def is_injective(writing: tuple[int, ...]) -> bool:
    """The writing gives every term its own letter."""
    return injective(writing)


def determines_both(state: DState, writing: tuple[int, ...]) -> bool:
    """The writing determines both relations."""
    return determines(state, writing)


def collides(state: DState, writing: tuple[int, ...]) -> bool:
    """The writing does not determine the assertions."""
    return not determines(state, writing)


def collides_r_only(state: DState, writing: tuple[int, ...]) -> bool:
    """The writing collides in `r` and determines `s`."""
    return (not determines_rel(state, writing, "r")) and determines_rel(state, writing, "s")


WRITING_STATEMENTS: tuple[tuple[str, Callable[[DState, tuple[int, ...]], bool]], ...] = (
    ("injective", lambda _s, w: injective(w)),
    ("determines", determines_both),
    ("collides", collides),
    ("collides_r_only", collides_r_only),
)


@dataclass(frozen=True)
class WritingVerdict:
    """Where a writing statement first holds and first fails among (state, writing) pairs."""

    name: str
    holds_at: tuple[str, str] | None
    fails_at: tuple[str, str] | None

    @property
    def follows(self) -> bool:
        """Does the statement hold of every writing of every explored result?"""
        return self.fails_at is None and self.holds_at is not None


def verdicts(expl: Exploration) -> tuple[Verdict, ...]:
    """The ninth's state-statements, on this exploration (C-W1: the same results)."""
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


def writing_verdicts(expl: Exploration) -> tuple[WritingVerdict, ...]:
    """For each writing statement, the earliest pair where it holds and where it fails."""
    found: dict[str, list[tuple[str, str] | None]] = {name: [None, None] for name, _ in WRITING_STATEMENTS}
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], s.n, s.key())):
        for writing in writings_of(state):
            written_state = state.key()
            written_w = str(writing)
            for name, pred in WRITING_STATEMENTS:
                slot = 0 if pred(state, writing) else 1
                if found[name][slot] is None:
                    found[name][slot] = (written_state, written_w)
    return tuple(WritingVerdict(name, found[name][0], found[name][1]) for name, _ in WRITING_STATEMENTS)
