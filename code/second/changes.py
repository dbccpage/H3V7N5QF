"""Changes of the second seed, obstructions, and the answers that remain.

Given by the second seed
    A change is exactly one of: identifying two terms; adding a term; adding
    an assertion.  Nothing else is a change.  Identifying two terms replaces
    both by one term in every assertion.  A change that makes some `xrx`
    asserted is obstructed.  An obstructed change must be answered: remove
    the obstruction, or build structure by further changes.  A refused change
    is recorded and changes nothing.

Cited from the first derivation (`xry.changes`) and re-checked
    `Change`, `Kind`, `perform`, `obstruction`, `is_build_of` and
    `one_term_builds` are functions of one change and its kind; none of them
    depends on removal being a change.  They are used here only with the
    three kinds in `KINDS`; `perform` below refuses a removal.

Derived (paper, `lean4/Second/`)
    * Which changes are obstructed is as in the first derivation: adding
      `xrx`, and identifying `x`, `y` while `xry` or `yrx` is asserted.
    * "Remove the obstruction" is impossible for every obstructed change: no
      change of the three kinds un-asserts anything, and an assertion, once
      asserted, is carried to every later state.  An obstructed change has
      two answers: refuse, or build.

Chosen here (as in the first derivation, readings C5 and C7)
    * Adding what is asserted and identifying a term with itself change
      nothing, so they are not changes; a new term comes with no assertion;
      an added assertion is between terms that are there.
    * A build for `xrx` adds a term `t` and `xrt` or `trx` (fewest
      additions); for an obstructed identification the state itself is the
      build, with no addition.
"""

from __future__ import annotations

from xry.changes import (
    Answer,
    AnswerKind,
    Change,
    Kind,
    is_build_of,
    obstruction,
    one_term_builds,
)
from xry.changes import perform as perform_first
from xry.state import State

__all__ = [
    "KINDS",
    "REMOVAL_IMPOSSIBLE",
    "Answer",
    "AnswerKind",
    "Change",
    "Kind",
    "answers",
    "changes",
    "is_build_of",
    "is_change",
    "obstruction",
    "one_term_builds",
    "perform",
]

#: The three kinds of change, in the seed's order.
KINDS: tuple[Kind, ...] = (Kind.IDENTIFY, Kind.ADD_TERM, Kind.ADD_ASSERTION)

#: Recorded for every obstructed change: why "remove the obstruction" is not an answer.
REMOVAL_IMPOSSIBLE = "impossible: no change un-asserts an assertion"


def is_change(change: Change) -> bool:
    """Is `change` a change of the second seed?"""
    return change.kind in KINDS


def changes(state: State) -> tuple[Change, ...]:
    """Every change of the second seed on `state`, fewest additions first.

    Identifications (no addition), then adding a term, then adding an
    assertion (one addition each): the seed's order of kinds.  This is the
    first derivation's list without its removals (`tests/test_second_changes.py`
    checks that).
    """
    n = state.n
    out = [Change(Kind.IDENTIFY, x, y) for x in range(n) for y in range(x + 1, n)]
    out.append(Change(Kind.ADD_TERM))
    out += [
        Change(Kind.ADD_ASSERTION, x, y)
        for x in range(n)
        for y in range(n)
        if not state.has(x, y)
    ]
    return tuple(out)


def perform(state: State, change: Change) -> State:
    """The outcome of `change`, legal or not.  A removal is not a change."""
    if not is_change(change):
        raise ValueError("removing an assertion is not a change")
    return perform_first(state, change)


def answers(state: State, change: Change) -> tuple[Answer, ...]:
    """Every answer that remains for an obstructed `change` on a legal `state`.

    Refusal is always there.  For an identification the state itself is the
    build (no addition).  For adding `xrx` the two builds with fewest
    additions add a term `t` and `xrt` or `trx`.  "Remove the obstruction"
    is never among them: no change un-asserts.
    """
    if not is_change(change):
        raise ValueError("removing an assertion is not a change")
    blocked = obstruction(state, change)
    if not blocked:
        raise ValueError("only an obstructed change is answered")
    out = [Answer(AnswerKind.REFUSE, (), False, state)]
    if change.kind is Kind.IDENTIFY:
        out.append(Answer(AnswerKind.BUILD, (), False, state))
        return tuple(out)
    x, new = change.x, state.n
    grown = perform(state, Change(Kind.ADD_TERM))
    for pair in ((x, new), (new, x)):
        step = Change(Kind.ADD_ASSERTION, *pair)
        out.append(
            Answer(AnswerKind.BUILD, (Change(Kind.ADD_TERM), step), False, perform(grown, step))
        )
    return tuple(out)
