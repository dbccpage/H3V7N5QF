"""Changes of the fourth seed, obstructions, and the answers that remain.

Given by the fourth seed
    A change is exactly one of: adding a term; adding an assertion.  Nothing
    else is a change.  Adding an assertion raises its multiplicity by one.  A
    change that makes some `xrx` asserted is obstructed.  An obstructed change
    must be answered: remove the obstruction, or build structure by further
    changes.  A refused change is recorded and changes nothing.

Cited from the first derivation (`xry.changes`) and re-checked
    `Kind` (the kinds of change) and `AnswerKind` (refuse, remove the
    obstruction, build) name things and mention no multiplicity; they survive
    the counting and are imported.  `Change`, `perform`, `obstruction`,
    `answers`, `one_term_builds` and `is_build_of` are written afresh: the
    outcome of adding an assertion is now a multiplicity, so adding what is
    asserted is a change (it was not, under the earlier reading C5).

Cited from the third derivation (`third.changes`) and re-checked
    The third's list of changes on a state is the list below without the
    additions of what is asserted (`tests/test_fourth_changes.py` checks
    that); the third's `1 + n² − m` attempts become `1 + n²`.  The answers to
    adding `xrx` are the same two builds; the third's `REMOVAL_IMPOSSIBLE`
    wording is restated for multiplicities.

Derived (paper, `lean4/Fourth/`)
    * The obstructed changes are exactly the additions of some `xrx`; adding
      a term, or `xry` with `x` and `y` two terms — asserted already or not —
      is never obstructed.
    * The obstruction of adding `xrx` is that assertion itself.  "Remove the
      obstruction" is impossible: no change lowers a multiplicity, and not
      asserting it is refusal.  An obstructed change has two answers: refuse,
      or build.
    * Exactly two builds add one term (`xrt`, `trx`): with multiplicities
      counted, a copy of an assertion of `x` for the added term would make
      the build stand for something other than the would-be outcome.

Chosen here (readings C5–C7 of the earlier papers, restated)
    * A new term comes with no assertion; an added assertion is between terms
      that are there.  Adding an asserted assertion is a change (the seed says
      it raises the multiplicity).
    * Both kinds add one; "fewest additions first" does not order them, and
      the seed's own order of kinds (a term, then an assertion) is taken.
    * A build for `xrx` adds a term `t` and `xrt` or `trx` (fewest additions).
"""

from __future__ import annotations

from dataclasses import dataclass

from xry.changes import AnswerKind, Kind

from fourth.state import MState, Names, Pair

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
    "image",
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
    "impossible: the obstruction is the assertion the change itself adds, "
    "raising its multiplicity from none to one; no change lowers a multiplicity, "
    "and not adding it is refusal"
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
        return (1, 0) if self.kind is Kind.ADD_TERM else (0, 1)

    def written(self, state: MState) -> str:
        """The change in words, using the state's writing of its terms."""
        if self.kind is Kind.ADD_TERM:
            return "add a term"
        w = state.term_writing()
        return f"add {w[self.x]}r{w[self.y]}"


def is_change(change: Change) -> bool:
    """Is `change` a change of the fourth seed?"""
    return change.kind in KINDS


def changes(state: MState) -> tuple[Change, ...]:
    """Every change of the fourth seed on `state`: adding a term, then adding each assertion.

    Every ordered pair is listed, asserted already or not, `xrx` included:
    `1 + n²` changes.  Both kinds add one, so "fewest additions first" leaves
    the seed's own order of kinds.
    """
    n = state.n
    return (Change(Kind.ADD_TERM), *(Change(Kind.ADD_ASSERTION, x, y) for x in range(n) for y in range(n)))


def attempt_counts(state: MState) -> tuple[int, int]:
    """How many changes `state` has, and how many of them are obstructed: `1 + n²`, `n`."""
    n = state.n
    return 1 + n * n, n


def perform(state: MState, change: Change) -> MState:
    """The outcome of `change`, legal or not.  Only the two kinds are changes."""
    if not is_change(change):
        raise ValueError("neither removing an assertion nor identifying terms is a change")
    n, x, y = state.n, change.x, change.y
    if change.kind is Kind.ADD_TERM:
        grown = [0] * ((n + 1) * (n + 1))
        for u in range(n):
            grown[u * (n + 1) : u * (n + 1) + n] = state.mult[u * n : u * n + n]
        return MState(n + 1, tuple(grown), state.names)
    if not (0 <= x < n and 0 <= y < n):
        raise ValueError("an assertion is between terms that are there")
    mult = list(state.mult)
    mult[x * n + y] += 1
    return MState(n, tuple(mult), state.names)


def obstruction(state: MState, change: Change) -> tuple[Pair, ...]:
    """The assertions that would become some `xrx`; empty when unobstructed.

    For adding `xrx`: that assertion itself.  Nothing else is obstructed.
    """
    if change.kind is Kind.ADD_ASSERTION and change.x == change.y:
        return ((change.x, change.y),)
    return ()


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


def image(state: MState, q: tuple[int, ...], n: int, names: Names | None) -> MState:
    """The state read with each term `t` as `q[t]`: multiplicities of pairs that become one pair add up."""
    mult = [0] * (n * n)
    for x, y, k in state.counted:
        mult[q[x] * n + q[y]] += k
    return MState(n, tuple(mult), names)


def one_term_builds(state: MState, x: int) -> tuple[MState, ...]:
    """The builds answering 'add `xrx`' that add exactly one term `t` (written `state.n`).

    Exactly two: `xrt` and `trx`.  Both together would stand for `xrx`
    asserted twice, and a copy `try` or `yrt` of an asserted `xry` or `yrx`
    would stand for one more `xry` or `yrx` than the would-be outcome has
    (`tests/test_fourth_changes.py` checks this against every candidate with
    small multiplicities).
    """
    if not 0 <= x < state.n:
        raise ValueError("the term is not there")
    new = state.n
    grown = perform(state, Change(Kind.ADD_TERM))
    return tuple(perform(grown, Change(Kind.ADD_ASSERTION, *pair)) for pair in ((x, new), (new, x)))


def is_build_of(built: MState, state: MState, change: Change) -> bool:
    """Is `built` a build answering the obstructed `change` on `state`?

    It must be legal, contain `state` unchanged (multiplicities included),
    and reading each added term as `x` — the multiplicities of the pairs
    that become one pair adding up — must give exactly the would-be outcome
    of `change`.
    """
    if not built.legal or not obstruction(state, change):
        return False
    target = perform(state, change)
    extra = built.n - state.n
    if extra < 1 or built.names != state.names:
        return False
    n = state.n
    if any(built.mult_of(u, v) != state.mult_of(u, v) for u in range(n) for v in range(n)):
        return False
    q = tuple(range(n)) + (change.x,) * extra
    return image(built, q, target.n, target.names).mult == target.mult
