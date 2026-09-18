"""States with counted assertions, and sameness (fourth seed).

Given by the fourth seed
    Terms are written with letters.  An assertion `xry` has a first term `x`
    and a second term `y`; it is asserted a number of times, its
    multiplicity.  `arb` is asserted with multiplicity one.  For no term `x`
    may `xrx` be asserted.  Whether `bra` is asserted is not given.  Two
    results that differ only in how their terms are written are the same
    result.

Cited from the first derivation (`xry.state`) and re-checked
    `Sameness` (the two readings of "differ only in how their terms are
    written"), `letter` and `LETTERS` (how terms are written) mention no
    assertion, so they survive the counting and are imported.  `State` is the
    earlier model (asserted or not); it is kept as the *support* of a counted
    state (`support`), and a `State` is read as a counted state asserting
    everything once (`of_state`).  Everything else is defined afresh: what a
    state is, its size, sameness, what is given.

Chosen here (the earlier readings, restated; the unchosen readings are in the paper)
    * "Asserted" means multiplicity at least one (the seed says "is asserted"
      of an assertion with a multiplicity).
    * What is given has exactly the terms `a` and `b`; `arb` once; `bra`
      not at all or once (a beginning with `bra` more than once is a result
      of the latter, so it adds no result).
    * Sameness under two readings, both kept: FREE (any rewriting) and
      ANCHORED (rewritings keeping `a` and `b`).

A `MState` may hold some `xrx`; then it is not legal.  Illegal states only
appear as the would-be outcome of an obstructed change, never as a result.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import permutations
from typing import Iterable

from xry.state import Names, Pair, Sameness, State, letter

__all__ = [
    "GIVEN_ASSERTIONS",
    "GIVEN_TERMS",
    "MState",
    "Names",
    "Pair",
    "Sameness",
    "added",
    "canonical",
    "given",
    "of_state",
    "rewrite",
    "same",
    "support",
]


@dataclass(frozen=True)
class MState:
    """`n` terms written 0..n-1, a multiplicity for each ordered pair, optional names.

    `mult[x * n + y]` is the multiplicity of `xry`.  `names`, when present,
    gives the terms that carry the names `a` and `b`.
    """

    n: int
    mult: tuple[int, ...]
    names: Names | None = None

    def __post_init__(self) -> None:
        if self.n < 0:
            raise ValueError("the number of terms is not negative")
        if len(self.mult) != self.n * self.n:
            raise ValueError("every ordered pair of terms has one multiplicity")
        if any(k < 0 for k in self.mult):
            raise ValueError("a multiplicity is not negative")
        if self.names is not None and not all(0 <= t < self.n for t in self.names):
            raise ValueError("a name is carried by a term that is not there")

    @staticmethod
    def of(n: int, pairs: Iterable[Pair], names: Names | None = None) -> MState:
        """Build a state from asserted pairs; each listing of a pair adds one to its multiplicity."""
        mult = [0] * (n * n)
        for x, y in pairs:
            if not (0 <= x < n and 0 <= y < n):
                raise ValueError("an assertion mentions a term that is not there")
            mult[x * n + y] += 1
        return MState(n, tuple(mult), names)

    def mult_of(self, x: int, y: int) -> int:
        """The multiplicity of `xry`."""
        return self.mult[x * self.n + y]

    def has(self, x: int, y: int) -> bool:
        """Is `xry` asserted (multiplicity at least one)?"""
        return self.mult[x * self.n + y] > 0

    @property
    def pairs(self) -> tuple[Pair, ...]:
        """Asserted pairs `(x, y)`, sorted, each once."""
        n = self.n
        return tuple((x, y) for x in range(n) for y in range(n) if self.mult[x * n + y])

    @property
    def counted(self) -> tuple[tuple[int, int, int], ...]:
        """Asserted pairs with their multiplicities, `(x, y, k)`, sorted."""
        n = self.n
        return tuple((x, y, k) for x in range(n) for y in range(n) if (k := self.mult[x * n + y]))

    @property
    def m(self) -> int:
        """The sum of all multiplicities: how many assertions, counted."""
        return sum(self.mult)

    @property
    def distinct(self) -> int:
        """How many assertions are asserted (each counted once)."""
        return sum(1 for k in self.mult if k)

    @property
    def size(self) -> int:
        """Terms plus assertions, counted with multiplicity."""
        return self.n + self.m

    @property
    def loops(self) -> tuple[int, ...]:
        """Terms `x` with `xrx` asserted."""
        return tuple(x for x in range(self.n) if self.has(x, x))

    @property
    def legal(self) -> bool:
        """No `xrx` is asserted."""
        return not self.loops

    @property
    def simple(self) -> bool:
        """Nothing is asserted more than once."""
        return all(k <= 1 for k in self.mult)

    @property
    def most(self) -> int:
        """The largest multiplicity (0 when nothing is asserted)."""
        return max(self.mult, default=0)

    def related(self, x: int, y: int) -> bool:
        """Is `xry` or `yrx` asserted?"""
        return self.has(x, y) or self.has(y, x)

    def key(self) -> str:
        """A compact identifier of this exact writing.

        Unambiguous while every name index is one digit (at most ten terms);
        it does not follow `explore.order`.
        """
        names = "" if self.names is None else f"{self.names[0]}{self.names[1]}"
        body = ".".join(f"{x}-{y}*{k}" for x, y, k in self.counted)
        return f"{self.n}:{names}:{body}"

    def term_writing(self) -> tuple[str, ...]:
        """One writing of the terms with letters (the named terms `a`, `b`; then the next letters)."""
        if self.names is None:
            return tuple(letter(i) for i in range(self.n))
        a, b = self.names
        out = [""] * self.n
        out[a] = "a"
        if b != a:
            out[b] = "b"
        nxt = 2
        for t in range(self.n):
            if not out[t]:
                out[t] = letter(nxt)
                nxt += 1
        return tuple(out)

    def written(self) -> str:
        """The state written in the seed's notation; a multiplicity above one in brackets."""
        w = self.term_writing()
        terms = " ".join(w)
        if self.names is not None and self.names[0] == self.names[1]:
            terms += " (a and b are one term)"
        parts = [f"{w[x]}r{w[y]}" + (f"({k})" if k > 1 else "") for x, y, k in self.counted]
        return f"terms {terms}; asserted {' '.join(parts) or 'nothing'}"


def support(state: MState) -> State:
    """The earlier derivations' state asserting exactly what `state` asserts (once each)."""
    return State.of(state.n, state.pairs, state.names)


def of_state(state: State) -> MState:
    """The counted state asserting everything `state` asserts, once each."""
    return MState.of(state.n, state.pairs, state.names)


@lru_cache(maxsize=None)
def _rewritings(n: int) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    """Every rewriting `p` of `n` terms, with the index map on ordered pairs."""
    out = []
    for p in permutations(range(n)):
        index = tuple(p[x] * n + p[y] for x in range(n) for y in range(n))
        out.append((p, index))
    return tuple(out)


def rewrite(state: MState, p: tuple[int, ...]) -> MState:
    """The same state with term `t` written as `p[t]`."""
    if sorted(p) != list(range(state.n)):
        raise ValueError("a rewriting writes each term once")
    n = state.n
    mult = [0] * (n * n)
    for x in range(n):
        for y in range(n):
            mult[p[x] * n + p[y]] = state.mult[x * n + y]
    names = None if state.names is None else (p[state.names[0]], p[state.names[1]])
    return MState(n, tuple(mult), names)


_CANONICAL: dict[MState, MState] = {}


def canonical(state: MState) -> MState:
    """The least writing of `state`; equal exactly for same states.

    With `names` the rewriting carries the names along (ANCHORED) and the
    names come first in the comparison, so `a` is written `0` and `b` is
    written `1` whenever they are two terms; without names every rewriting
    counts (FREE).
    """
    hit = _CANONICAL.get(state)
    if hit is not None:
        return hit
    n = state.n
    best: tuple[int, int, tuple[int, ...]] | None = None
    for p, index in _rewritings(n):
        mult = [0] * (n * n)
        for i, k in enumerate(state.mult):
            if k:
                mult[index[i]] = k
        a, b = (0, 0) if state.names is None else (p[state.names[0]], p[state.names[1]])
        cand = (a, b, tuple(mult))
        if best is None or cand < best:
            best = cand
    assert best is not None  # there is always the rewriting that changes nothing
    out = MState(n, best[2], None if state.names is None else (best[0], best[1]))
    _CANONICAL[state] = out
    return out


def same(s: MState, t: MState) -> bool:
    """Do `s` and `t` differ only in how their terms are written?"""
    if s.n != t.n or (s.names is None) != (t.names is None):
        return False
    return canonical(s) == canonical(t)


def given(bra: bool, sameness: Sameness) -> MState:
    """What is given, under one of the two alternatives for `bra`.

    Terms `a` (written 0) and `b` (written 1); `arb` asserted once; `bra`
    asserted once or not at all according to the alternative.
    """
    pairs = [(0, 1), (1, 0)] if bra else [(0, 1)]
    names = (0, 1) if sameness is Sameness.ANCHORED else None
    return MState.of(2, pairs, names)


#: What is given counts two terms and one assertion (`bra` is not given).
GIVEN_TERMS = 2
GIVEN_ASSERTIONS = 1


def added(state: MState) -> tuple[int, int]:
    """How many terms and assertions (counted with multiplicity) `state` adds to what is given.

    A negative number means that the state has fewer than what is given.
    """
    return state.n - GIVEN_TERMS, state.m - GIVEN_ASSERTIONS
