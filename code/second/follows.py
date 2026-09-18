"""Statements about a state, and witnesses that they do not follow (second seed).

Cited from the first derivation (`xry.follows`) and re-checked
    The statements and `verdict` are about states, not changes; they apply
    to any exploration.  One statement is added: at least two terms, which
    the second seed makes true of every result (a theorem of the paper) and
    the first did not.
"""

from __future__ import annotations

from xry.explore import Exploration
from xry.follows import NAMED, UNNAMED, Statement, Verdict, verdict
from xry.state import State

__all__ = ["EXTRA", "at_least_two_terms", "verdicts"]


def at_least_two_terms(state: State) -> bool:
    """There are at least two terms."""
    return state.n >= 2


#: Statements added for the second seed.
EXTRA: tuple[Statement, ...] = (at_least_two_terms,)


def verdicts(expl: Exploration) -> tuple[Verdict, ...]:
    """Verdicts for every statement that makes sense for the exploration."""
    chosen = UNNAMED if expl.start.names is None else NAMED + UNNAMED
    return tuple(verdict(expl, s) for s in chosen + EXTRA)
