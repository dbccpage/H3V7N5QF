"""Changes of the third seed, obstructions, and the answers that remain.

Given by the third seed
    A change is exactly one of: adding a term; adding an assertion.  Nothing
    else is a change.  A change that makes some `xrx` asserted is obstructed.
    An obstructed change must be answered: remove the obstruction, or build
    structure by further changes.  A refused change is recorded and changes
    nothing.

Cited from the first derivation (`xry.changes`) and re-checked
    `Change`, `Kind`, `perform`, `obstruction`, `is_build_of` and
    `one_term_builds` are functions of one change and its kind; none of them
    depends on removal or identification being a change.  They are used here
    only with the two kinds in `KINDS`; `perform` below refuses the others.
    `is_build_of` reads a build through the map that sends the added term to
    the term it stands for; under this seed that map is a relation between
    states, not a change, and the reading is kept as a relation.

Cited from the second derivation (`second.changes`) and re-checked
    `changes` below is the second derivation's list without its
    identifications (`tests/test_third_changes.py` checks that), and the
    answers to adding `xrx` are the same two builds.

Derived (paper, `lean4/Third/`)
    * The obstructed changes are exactly the additions of some `xrx`; adding
      a term, or `xry` with `x` and `y` two terms, is never obstructed.
    * The obstruction of adding `xrx` is that assertion itself.  "Remove the
      obstruction" is impossible: no change un-asserts, and not asserting it
      is refusal.  An obstructed change has two answers: refuse, or build.

Chosen here (readings C5 and C7 of the earlier papers, restricted)
    * Adding what is asserted changes nothing, so it is not a change; a new
      term comes with no assertion; an added assertion is between terms that
      are there.
    * Both kinds add one; "fewest additions first" does not order them, and
      the seed's own order of kinds (a term, then an assertion) is taken.
    * A build for `xrx` adds a term `t` and `xrt` or `trx` (fewest additions).
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
    "attempt_counts",
    "changes",
    "is_build_of",
    "is_change",
    "obstruction",
    "one_term_builds",
    "perform",
]

#: The two kinds of change, in the seed's order.
KINDS: tuple[Kind, ...] = (Kind.ADD_TERM, Kind.ADD_ASSERTION)

#: Recorded for every obstructed change: why "remove the obstruction" is not an answer.
REMOVAL_IMPOSSIBLE = (
    "impossible: the obstruction is the assertion the change itself adds; "
    "no change un-asserts it, and not adding it is refusal"
)


def is_change(change: Change) -> bool:
    """Is `change` a change of the third seed?"""
    return change.kind in KINDS


def changes(state: State) -> tuple[Change, ...]:
    """Every change of the third seed on `state`: adding a term, then adding an assertion.

    Both kinds add one, so "fewest additions first" leaves the seed's own
    order of kinds.  This is the second derivation's list without its
    identifications (`tests/test_third_changes.py` checks that).
    """
    n = state.n
    out = [Change(Kind.ADD_TERM)]
    out += [
        Change(Kind.ADD_ASSERTION, x, y)
        for x in range(n)
        for y in range(n)
        if not state.has(x, y)
    ]
    return tuple(out)


def attempt_counts(state: State) -> tuple[int, int]:
    """How many changes `state` has, and how many of them are obstructed.

    `1 + n² − m` changes (a term; every pair not asserted, `xrx` included),
    of which the `n` additions of some `xrx` are obstructed.
    """
    n = state.n
    return 1 + n * n - state.m, n


def perform(state: State, change: Change) -> State:
    """The outcome of `change`, legal or not.  Only the two kinds are changes."""
    if not is_change(change):
        raise ValueError("neither removing an assertion nor identifying terms is a change")
    return perform_first(state, change)


def answers(state: State, change: Change) -> tuple[Answer, ...]:
    """Every answer that remains for an obstructed `change` on a legal `state`.

    Refusal is always there.  The only obstructed change is adding `xrx`, and
    its two builds with fewest additions add a term `t` and `xrt` or `trx`.
    "Remove the obstruction" is never among them.
    """
    if not is_change(change):
        raise ValueError("neither removing an assertion nor identifying terms is a change")
    if not obstruction(state, change):
        raise ValueError("only an obstructed change is answered")
    x, new = change.x, state.n
    grown = perform(state, Change(Kind.ADD_TERM))
    out = [Answer(AnswerKind.REFUSE, (), False, state)]
    for pair in ((x, new), (new, x)):
        step = Change(Kind.ADD_ASSERTION, *pair)
        out.append(
            Answer(AnswerKind.BUILD, (Change(Kind.ADD_TERM), step), False, perform(grown, step))
        )
    return tuple(out)
