"""Changes of the fifth seed, obstructions, and the answers to an obstructed change.

Given by the fifth seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  Nothing else is a change.  Adding an
    assertion raises its multiplicity by one; removing lowers it by one.
    Identifying two terms replaces both by one term in every assertion.  A
    change that makes some `xrx` asserted is obstructed.  An obstructed
    change must be answered: remove the obstruction, or build structure by
    further changes.  A refused change is recorded and changes nothing.

Cited from the first derivation (`xry.changes`) and re-checked
    `Kind` (the four kinds, in the seed's order) and `AnswerKind` name things
    and mention no multiplicity: they survive and are imported.  The list of
    changes and the obstruction rule are the first derivation's, restated for
    multiplicities: every asserted pair has one removal (it lowers by one);
    every ordered pair has one addition, asserted already or not.

Cited from the fourth derivation (`fourth.changes`) and re-checked
    `image` (reading a state through a map with multiplicities adding up),
    `one_term_builds` and `is_build_of` for an obstructed addition are about
    additions and a map only; they mention no removal or identification and
    survive.  `is_build_of` gains the identification case of the first
    derivation (the state itself is the build).

Derived (paper, `lean4/Fifth/`)
    * The obstructed changes are exactly the additions of some `xrx` and the
      identifications of two related terms; removal and adding a term are
      never obstructed; adding an asserted `xry` with `x ≠ y` is not.
    * The obstruction of an identification is the assertions between the two
      terms with their multiplicities; removing it is `M(u,v) + M(v,u)`
      removals and then the identification — a sequence of performed changes.
    * The obstruction of adding `xrx` is that assertion itself; removing it is
      not adding it, which is refusal (recorded as such).

Chosen here (readings C5″ and C7 of the paper)
    * Removing what is not asserted, and identifying a term with itself,
      change nothing and are not changes; adding what is asserted is a change.
    * An identification adds up the multiplicities of the pairs that become
      one pair (the unchosen reading is discussed in the paper).
    * Fewest additions first: identifications and removals (no addition),
      then a term, then the assertions — the seed's order among equals.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb

from fourth.changes import Change as ChangeFourth
from fourth.changes import image, is_build_of as is_build_of_addition, one_term_builds, perform as perform_fourth
from xry.changes import AnswerKind, Kind

from fifth.state import MState, Pair, identification_map, identify, remove

__all__ = [
    "KINDS",
    "REMOVAL_IS_REFUSAL",
    "Answer",
    "AnswerKind",
    "Change",
    "Kind",
    "answers",
    "attempt_counts",
    "changes",
    "image",
    "is_build_of",
    "is_change",
    "obstruction",
    "obstruction_counted",
    "one_term_builds",
    "perform",
]

#: The four kinds of change, in the seed's order.
KINDS: tuple[Kind, ...] = (Kind.IDENTIFY, Kind.REMOVE, Kind.ADD_TERM, Kind.ADD_ASSERTION)

#: Recorded for every obstructed addition of `xrx`: what "remove the obstruction" comes to.
REMOVAL_IS_REFUSAL = (
    "coincides with refusal: the obstruction is the assertion the change itself adds; "
    "removing it is not adding it, and nothing changes"
)


@dataclass(frozen=True)
class Change:
    """One change.  `x`, `y` are the terms it mentions (none for ADD_TERM)."""

    kind: Kind
    x: int = -1
    y: int = -1

    @property
    def additions(self) -> tuple[int, int]:
        """(terms, assertions) this change adds."""
        if self.kind is Kind.ADD_TERM:
            return (1, 0)
        if self.kind is Kind.ADD_ASSERTION:
            return (0, 1)
        return (0, 0)

    def written(self, state: MState) -> str:
        """The change in words, using the state's writing of its terms."""
        if self.kind is Kind.ADD_TERM:
            return "add a term"
        w = state.term_writing()
        if self.kind is Kind.IDENTIFY:
            return f"identify {w[self.x]} and {w[self.y]}"
        verb = "remove" if self.kind is Kind.REMOVE else "add"
        return f"{verb} {w[self.x]}r{w[self.y]}"


def is_change(change: Change) -> bool:
    """Is `change` one of the four kinds?"""
    return change.kind in KINDS


def changes(state: MState) -> tuple[Change, ...]:
    """Every change of the fifth seed on `state`, fewest additions first.

    Identifications (each unordered pair of terms once), removals (each
    asserted pair once — one removal lowers by one), a term, then every
    ordered pair as an addition, asserted already or not, `xrx` included.
    """
    n = state.n
    out = [Change(Kind.IDENTIFY, x, y) for x in range(n) for y in range(x + 1, n)]
    out += [Change(Kind.REMOVE, x, y) for x, y in state.pairs]
    out.append(Change(Kind.ADD_TERM))
    out += [Change(Kind.ADD_ASSERTION, x, y) for x in range(n) for y in range(n)]
    return tuple(out)


def attempt_counts(state: MState) -> tuple[int, int]:
    """How many changes `state` has, and how many are obstructed.

    `C(n, 2) + d + 1 + n²` changes (`d` asserted pairs); obstructed are the
    `n` additions of some `xrx` and the identifications of related pairs.
    """
    n = state.n
    related = sum(1 for x in range(n) for y in range(x + 1, n) if state.related(x, y))
    return comb(n, 2) + state.distinct + 1 + n * n, n + related


def perform(state: MState, change: Change) -> MState:
    """The outcome of `change`, legal or not."""
    if change.kind is Kind.IDENTIFY:
        return identify(state, change.x, change.y)
    if change.kind is Kind.REMOVE:
        return remove(state, change.x, change.y)
    return perform_fourth(state, ChangeFourth(change.kind, change.x, change.y))


def obstruction(state: MState, change: Change) -> tuple[Pair, ...]:
    """The assertions that would become some `xrx`; empty when unobstructed.

    For an identification of `x` and `y`: those of `xry`, `yrx` that are
    asserted.  For adding `xrx`: that assertion itself.
    """
    if change.kind is Kind.IDENTIFY:
        x, y = change.x, change.y
        return tuple(p for p in ((x, y), (y, x)) if state.has(*p))
    if change.kind is Kind.ADD_ASSERTION and change.x == change.y:
        return ((change.x, change.y),)
    return ()


def obstruction_counted(state: MState, change: Change) -> tuple[tuple[int, int, int], ...]:
    """The obstruction with multiplicities: `(x, y, k)` for each obstructing assertion.

    For adding `xrx` the multiplicity is the one the change would give it.
    """
    if change.kind is Kind.ADD_ASSERTION:
        return tuple((x, y, 1) for x, y in obstruction(state, change))
    return tuple((x, y, state.mult_of(x, y)) for x, y in obstruction(state, change))


@dataclass(frozen=True)
class Answer:
    """One way to deal with an obstructed change.

    `further` are the further changes, in order, each unobstructed where it
    is performed.  `completes` says whether the obstructed change itself is
    then performed.  `result` is the legal state reached.
    """

    kind: AnswerKind
    further: tuple[Change, ...]
    completes: bool
    result: MState

    @property
    def performed(self) -> int:
        """How many changes this answer performs."""
        return len(self.further) + int(self.completes)


def answers(state: MState, change: Change) -> tuple[Answer, ...]:
    """Every answer kept for an obstructed `change` on a legal `state`.

    Refusal is always there.  For an identification: remove the obstruction
    (lower each obstructing assertion to zero, then identify) and build (the
    state itself).  For adding `xrx`: the two one-term builds; "remove the
    obstruction" is refusal and is not listed twice.
    """
    blocked = obstruction(state, change)
    if not blocked:
        raise ValueError("only an obstructed change is answered")
    out = [Answer(AnswerKind.REFUSE, (), False, state)]
    if change.kind is Kind.IDENTIFY:
        removals = tuple(Change(Kind.REMOVE, u, v) for u, v in blocked for _ in range(state.mult_of(u, v)))
        cleared = state
        for removal in removals:
            cleared = perform(cleared, removal)
        out.append(Answer(AnswerKind.REMOVE_OBSTRUCTION, removals, True, perform(cleared, change)))
        out.append(Answer(AnswerKind.BUILD, (), False, state))
        return tuple(out)
    x, new = change.x, state.n
    for pair, built in zip(((x, new), (new, x)), one_term_builds(state, x)):
        out.append(Answer(AnswerKind.BUILD, (Change(Kind.ADD_TERM), Change(Kind.ADD_ASSERTION, *pair)), False, built))
    return tuple(out)


def is_build_of(built: MState, state: MState, change: Change) -> bool:
    """Is `built` a build answering the obstructed `change` on `state`?

    For adding `xrx`: the fourth derivation's criterion (additions only; the
    added terms read as `x`, multiplicities adding up, give the would-be
    outcome).  For an identification: nothing is added and reading the state
    through the identification gives the would-be outcome — the state itself.
    """
    if not built.legal or not obstruction(state, change):
        return False
    if change.kind is Kind.ADD_ASSERTION:
        return is_build_of_addition(built, state, ChangeFourth(change.kind, change.x, change.y))
    if built.n != state.n or built.names != state.names:
        return False
    if any(built.mult_of(u, v) < k for u, v, k in state.counted):
        return False
    target = perform(state, change)
    q = identification_map(state.n, change.x, change.y)
    return image(built, q, target.n, target.names).mult == target.mult
