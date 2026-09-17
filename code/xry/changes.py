"""Changes, obstructions, and the ways an obstructed change can be answered.

Given by the seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  Identifying two terms replaces both
    by one term in every assertion.  A change that makes some `xrx` asserted
    is obstructed.  An obstructed change must be answered: remove the
    obstruction, or build structure by further changes.  A refused change is
    recorded and changes nothing.

Derived (proofs in the paper and in `lean4/`)
    * Only two kinds of change can be obstructed: adding `xrx` itself, and
      identifying two terms `x`, `y` while `xry` or `yrx` is asserted.
    * Removing the obstruction is possible only for an identification, and
      only by removing the assertions between the two terms.

Chosen here
    * Adding an assertion that is already asserted, removing one that is
      not, and identifying a term with itself change nothing, so they are
      not changes.
    * A new term comes with no assertion; an added assertion is between
      terms that are already there.
    * "Build structure" is read as: by additions only, reach a legal state
      from which identifying the added terms back would give exactly the
      would-be outcome of the obstructed change (`is_build_of` checks this).
      Fewest additions first.  For an obstructed identification the state
      itself is such a build, with no addition.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from itertools import product

from xry.state import Pair, State


class Kind(Enum):
    """The four kinds of change, in the seed's order."""

    IDENTIFY = "identify two terms"
    REMOVE = "remove an assertion"
    ADD_TERM = "add a term"
    ADD_ASSERTION = "add an assertion"


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

    def written(self, state: State) -> str:
        """The change in words, using the state's writing of its terms."""
        if self.kind is Kind.ADD_TERM:
            return "add a term"
        w = state.term_writing()
        if self.kind is Kind.IDENTIFY:
            return f"identify {w[self.x]} and {w[self.y]}"
        verb = "remove" if self.kind is Kind.REMOVE else "add"
        return f"{verb} {w[self.x]}r{w[self.y]}"


def changes(state: State) -> tuple[Change, ...]:
    """Every change that can be attempted on `state`, fewest additions first.

    Order: identifications, removals (no addition); then adding a term; then
    adding an assertion (one addition each) -- the seed's own order of kinds.
    """
    n = state.n
    out = [Change(Kind.IDENTIFY, x, y) for x in range(n) for y in range(x + 1, n)]
    out += [Change(Kind.REMOVE, x, y) for x, y in state.pairs]
    out.append(Change(Kind.ADD_TERM))
    out += [
        Change(Kind.ADD_ASSERTION, x, y)
        for x in range(n)
        for y in range(n)
        if not state.has(x, y)
    ]
    return tuple(out)


def identification_map(n: int, x: int, y: int) -> tuple[int, ...]:
    """Where each of `n` terms goes when `x < y` are replaced by one term.

    The one term is written `x`; terms after `y` move down by one.
    """
    if not 0 <= x < y < n:
        raise ValueError("identifying takes two terms, written x < y")
    return tuple(x if t == y else t - (t > y) for t in range(n))


def perform(state: State, change: Change) -> State:
    """The outcome of `change`, legal or not.  Nothing else is a change."""
    n, x, y = state.n, change.x, change.y
    if change.kind is Kind.ADD_TERM:
        return State.of(n + 1, state.pairs, state.names)
    if change.kind is Kind.IDENTIFY:
        q = identification_map(n, x, y)
        names = None if state.names is None else (q[state.names[0]], q[state.names[1]])
        return State.of(n - 1, ((q[u], q[v]) for u, v in state.pairs), names)
    if not (0 <= x < n and 0 <= y < n):
        raise ValueError("an assertion is between terms that are there")
    if change.kind is Kind.REMOVE:
        if not state.has(x, y):
            raise ValueError("removing what is not asserted is not a change")
        return State(n, state.mask & ~(1 << (x * n + y)), state.names)
    if state.has(x, y):
        raise ValueError("adding what is already asserted is not a change")
    return State(n, state.mask | 1 << (x * n + y), state.names)


def obstruction(state: State, change: Change) -> tuple[Pair, ...]:
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


class AnswerKind(Enum):
    """What can be done about an obstructed change."""

    REFUSE = "refused"
    REMOVE_OBSTRUCTION = "remove the obstruction"
    BUILD = "build structure"


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
    result: State

    @property
    def performed(self) -> int:
        """How many changes this answer performs."""
        return len(self.further) + int(self.completes)


def answers(state: State, change: Change) -> tuple[Answer, ...]:
    """Every answer kept for an obstructed `change` on a legal `state`.

    Refusal is always there.  Removing the obstruction exists only for an
    identification.  Building: for an identification, the state itself; for
    adding `xrx`, the two builds with fewest additions (one term and one
    assertion), `x r x'` and `x' r x`.
    """
    blocked = obstruction(state, change)
    if not blocked:
        raise ValueError("only an obstructed change is answered")
    out = [Answer(AnswerKind.REFUSE, (), False, state)]
    if change.kind is Kind.IDENTIFY:
        removals = tuple(Change(Kind.REMOVE, u, v) for u, v in blocked)
        cleared = state
        for removal in removals:
            cleared = perform(cleared, removal)
        out.append(
            Answer(AnswerKind.REMOVE_OBSTRUCTION, removals, True, perform(cleared, change))
        )
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


def one_term_builds(state: State, x: int) -> tuple[State, ...]:
    """Every build answering 'add `xrx`' that adds exactly one term `x'`.

    `x'` is written `state.n`.  At least one of `x r x'`, `x' r x` is
    asserted; each assertion of `x` with another term may be repeated for
    `x'`; nothing else is added.  There are `3 * 2**d` of them, `d` being the
    number of assertions that mention `x`.
    """
    if not 0 <= x < state.n:
        raise ValueError("the term is not there")
    new = state.n
    between = [((x, new),), ((new, x),), ((x, new), (new, x))]
    copies: list[Pair] = []
    for u, v in state.pairs:
        if u == x:
            copies.append((new, v))
        if v == x:
            copies.append((u, new))
    out = []
    for link in between:
        for keep in product((False, True), repeat=len(copies)):
            extra = [p for p, k in zip(copies, keep) if k]
            out.append(State.of(new + 1, [*state.pairs, *link, *extra], state.names))
    return tuple(out)


def is_build_of(built: State, state: State, change: Change) -> bool:
    """Is `built` a build answering the obstructed `change` on `state`?

    It must be legal, contain `state` unchanged, and identifying each added
    term with the term it stands for must give exactly the would-be outcome
    of `change`.  For adding `xrx` the added terms stand for `x`; for an
    identification nothing is added and the map is the identification.
    """
    if not built.legal or not obstruction(state, change):
        return False
    target = perform(state, change)
    extra = built.n - state.n
    if change.kind is Kind.IDENTIFY:
        if extra != 0:
            return False
        q = identification_map(state.n, change.x, change.y)
    else:
        if extra < 1:
            return False
        q = tuple(range(state.n)) + (change.x,) * extra
    if built.names != state.names or any(not built.has(u, v) for u, v in state.pairs):
        return False
    image = State.of(target.n, ((q[u], q[v]) for u, v in built.pairs), target.names)
    return image.mask == target.mask
