"""States and sameness.

Given by the seed
    Terms are written with letters.  An assertion `xry` has a first term `x`
    and a second term `y`.  `arb` is asserted.  For no term `x` may `xrx` be
    asserted.  Whether `bra` is asserted is not given.  Two results that
    differ only in how their terms are written are the same result.

Chosen here (the seed is silent; the unchosen readings are in the paper)
    * An assertion is either asserted or not (no multiplicity).
    * What is given has exactly the terms `a` and `b`.
    * Sameness is computed under two readings, both kept:
      FREE      any rewriting of terms, `a` and `b` included;
      ANCHORED  rewritings that keep the writing of `a` and of `b`.
      Under ANCHORED a state remembers which terms carry the names `a`, `b`
      (one term may carry both after an identification).

A `State` may hold some `xrx`; then it is not legal.  Illegal states only
appear as the would-be outcome of an obstructed change, never as a result.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from functools import lru_cache
from itertools import permutations
from typing import Iterable

Pair = tuple[int, int]
Names = tuple[int, int]

#: Letters used to write terms.  `r` writes assertions, so it is left out.
LETTERS = "abcdefghijklmnopqstuvwxyz"


class Sameness(Enum):
    """The two readings of 'differ only in how their terms are written'."""

    FREE = "free"
    ANCHORED = "anchored"


def letter(index: int) -> str:
    """Write the `index`-th term with letters (bijective base 25, no `r`)."""
    if index < 0:
        raise ValueError("a term index is not negative")
    base = len(LETTERS)
    out = ""
    index += 1
    while index > 0:
        index, digit = divmod(index - 1, base)
        out = LETTERS[digit] + out
    return out


@dataclass(frozen=True)
class State:
    """`n` terms written 0..n-1, asserted pairs as a bit mask, optional names.

    Bit `x * n + y` of `mask` is set exactly when `xry` is asserted.
    `names`, when present, gives the terms that carry the names `a` and `b`.
    """

    n: int
    mask: int
    names: Names | None = None

    def __post_init__(self) -> None:
        if self.n < 0:
            raise ValueError("the number of terms is not negative")
        if self.mask < 0 or self.mask >> (self.n * self.n):
            raise ValueError("an assertion mentions a term that is not there")
        if self.names is not None and not all(0 <= t < self.n for t in self.names):
            raise ValueError("a name is carried by a term that is not there")

    @staticmethod
    def of(n: int, pairs: Iterable[Pair], names: Names | None = None) -> State:
        """Build a state from asserted pairs."""
        mask = 0
        for x, y in pairs:
            if not (0 <= x < n and 0 <= y < n):
                raise ValueError("an assertion mentions a term that is not there")
            mask |= 1 << (x * n + y)
        return State(n, mask, names)

    @property
    def pairs(self) -> tuple[Pair, ...]:
        """Asserted pairs `(x, y)`, sorted."""
        n = self.n
        return tuple(
            (x, y) for x in range(n) for y in range(n) if self.mask >> (x * n + y) & 1
        )

    @property
    def m(self) -> int:
        """Number of asserted assertions."""
        return self.mask.bit_count()

    def has(self, x: int, y: int) -> bool:
        """Is `xry` asserted?"""
        return bool(self.mask >> (x * self.n + y) & 1)

    @property
    def loops(self) -> tuple[int, ...]:
        """Terms `x` with `xrx` asserted."""
        return tuple(x for x in range(self.n) if self.has(x, x))

    @property
    def legal(self) -> bool:
        """No `xrx` is asserted."""
        return not self.loops

    def related(self, x: int, y: int) -> bool:
        """Is `xry` or `yrx` asserted?"""
        return self.has(x, y) or self.has(y, x)

    def key(self) -> str:
        """A compact identifier of this exact writing.

        Unambiguous while every name index is one digit (at most ten terms);
        it does not follow `explore.order`.
        """
        names = "" if self.names is None else f"{self.names[0]}{self.names[1]}"
        body = ".".join(f"{x}-{y}" for x, y in self.pairs)
        return f"{self.n}:{names}:{body}"

    def term_writing(self) -> tuple[str, ...]:
        """One writing of the terms with letters.

        With names, the named terms are written `a` and `b` (a term carrying
        both is written `a`); the other terms get the next letters.
        """
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
        """The state written in the seed's notation."""
        w = self.term_writing()
        terms = " ".join(w)
        if self.names is not None and self.names[0] == self.names[1]:
            terms += " (a and b are one term)"
        asserted = " ".join(f"{w[x]}r{w[y]}" for x, y in self.pairs) or "nothing"
        return f"terms {terms}; asserted {asserted}"


@lru_cache(maxsize=None)
def _rewritings(n: int) -> tuple[tuple[tuple[int, ...], tuple[tuple[int, ...], ...]], ...]:
    """Every rewriting `p` of `n` terms, with per-byte lookup tables for masks."""
    nbits = n * n
    nbytes = (nbits + 7) // 8
    out = []
    for p in permutations(range(n)):
        image = [1 << (p[x] * n + p[y]) for x in range(n) for y in range(n)]
        tables = []
        for b in range(nbytes):
            table = []
            for value in range(256):
                acc = 0
                for i in range(min(8, nbits - 8 * b)):
                    if value >> i & 1:
                        acc |= image[8 * b + i]
                table.append(acc)
            tables.append(tuple(table))
        out.append((p, tuple(tables)))
    return tuple(out)


def _rewrite_mask(mask: int, tables: tuple[tuple[int, ...], ...]) -> int:
    acc = 0
    b = 0
    while mask:
        acc |= tables[b][mask & 255]
        mask >>= 8
        b += 1
    return acc


def rewrite(state: State, p: tuple[int, ...]) -> State:
    """The same state with term `t` written as `p[t]`."""
    if sorted(p) != list(range(state.n)):
        raise ValueError("a rewriting writes each term once")
    names = None if state.names is None else (p[state.names[0]], p[state.names[1]])
    return State.of(state.n, ((p[x], p[y]) for x, y in state.pairs), names)


_CANONICAL: dict[State, State] = {}


def canonical(state: State) -> State:
    """The least writing of `state`; equal exactly for same states.

    With `names` the rewriting carries the names along (ANCHORED); without
    names every rewriting counts (FREE).
    """
    hit = _CANONICAL.get(state)
    if hit is not None:
        return hit
    best: tuple[int, int, int] | None = None
    for p, tables in _rewritings(state.n):
        mask = _rewrite_mask(state.mask, tables)
        a, b = (0, 0) if state.names is None else (p[state.names[0]], p[state.names[1]])
        cand = (mask, a, b)
        if best is None or cand < best:
            best = cand
    assert best is not None  # there is always the rewriting that changes nothing
    out = State(state.n, best[0], None if state.names is None else (best[1], best[2]))
    _CANONICAL[state] = out
    return out


def same(s: State, t: State) -> bool:
    """Do `s` and `t` differ only in how their terms are written?"""
    if s.n != t.n or (s.names is None) != (t.names is None):
        return False
    return canonical(s) == canonical(t)


def given(bra: bool, sameness: Sameness) -> State:
    """What is given, under one of the two alternatives for `bra`.

    Terms `a` (written 0) and `b` (written 1); `arb` asserted; `bra` asserted
    or not according to the alternative.
    """
    pairs = [(0, 1), (1, 0)] if bra else [(0, 1)]
    names = (0, 1) if sameness is Sameness.ANCHORED else None
    return State.of(2, pairs, names)


#: What is given counts two terms and one assertion (`bra` is not given).
GIVEN_TERMS = 2
GIVEN_ASSERTIONS = 1


def added(state: State) -> tuple[int, int]:
    """How many terms and assertions `state` adds to what is given.

    A negative number means that the state has fewer than what is given.
    """
    return state.n - GIVEN_TERMS, state.m - GIVEN_ASSERTIONS
