"""States with two relations, and sameness (eighth seed).

Given by the eighth seed
    Terms are written with letters.  An assertion is written `xry` or `xsy`,
    where `x` and `y` are terms and `r` and `s` are the two relations; it is
    asserted a number of times, its multiplicity.  `arb` is asserted with
    multiplicity one.  Whether `bra`, or anything written with `s`, is
    asserted is not given.  Identifying two terms replaces both by one term
    in every assertion.  Two results that differ only in how their terms are
    written are the same result.  Nothing forbids `xrx` or `xsx`.

Cited from the fourth, fifth and sixth derivations (`fourth.state`,
`fifth.state`, `sixth.state`) and re-checked
    The counted state `MState` (one multiplicity function) is the model of
    each *projection* of a two-relation state: its `r` part and its `s`
    part share the terms and the names.  `canonical`'s rewritings
    (`_rewritings`), `Sameness`, the names, `identify` and `remove` on a
    projection mention one relation only and survive as the parts of the
    two-relation operations.  Everything else is defined afresh: the state
    `DState`, its sameness (a rewriting acts on both relations at once), its
    size (terms plus both totals), what is given (`arb` once in `r`, `bra`
    once or not at all, nothing in `s`), `added`.

Chosen here (readings C2″, C4, C5⁗ of the paper)
    * What is given asserts nothing with `s` (the unchosen beginnings, with
      something in `s`, are results of it with the same results).
    * Sameness under two readings, both kept: FREE and ANCHORED; either way
      the rewriting rewrites both relations.
    * An identification adds up the multiplicities of the merged pairs in
      each relation separately.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from fifth.state import identify as identify_part
from fifth.state import remove as remove_part
from fourth.state import MState, Names, Pair, Sameness, _rewritings
from fourth.state import given as given_part

__all__ = [
    "GIVEN_ASSERTIONS",
    "GIVEN_TERMS",
    "RELATIONS",
    "DState",
    "MState",
    "Names",
    "Pair",
    "Sameness",
    "added",
    "canonical",
    "forget_canonical_forms",
    "given",
    "identify",
    "names_one_term",
    "of_r",
    "pair",
    "remove",
    "rewrite",
    "same",
]

#: The two relations, in the seed's order.
RELATIONS = ("r", "s")


@dataclass(frozen=True)
class DState:
    """`n` terms written 0..n-1, a multiplicity for each ordered pair in `r` and in `s`, optional names.

    `r[x * n + y]` is the multiplicity of `xry`, `s[x * n + y]` that of `xsy`.
    `names`, when present, gives the terms that carry the names `a` and `b`.
    """

    n: int
    r: tuple[int, ...]
    s: tuple[int, ...]
    names: Names | None = None

    def __post_init__(self) -> None:
        if self.n < 0:
            raise ValueError("the number of terms is not negative")
        if len(self.r) != self.n * self.n or len(self.s) != self.n * self.n:
            raise ValueError("every ordered pair of terms has one multiplicity in each relation")
        if any(k < 0 for k in self.r) or any(k < 0 for k in self.s):
            raise ValueError("a multiplicity is not negative")
        if self.names is not None and not all(0 <= t < self.n for t in self.names):
            raise ValueError("a name is carried by a term that is not there")

    @staticmethod
    def of(n: int, r_pairs: Iterable[Pair], s_pairs: Iterable[Pair] = (), names: Names | None = None) -> DState:
        """Build a state from asserted pairs in each relation; each listing adds one to a multiplicity."""
        return pair(MState.of(n, r_pairs, names), MState.of(n, s_pairs, names))

    def part(self, rel: str) -> MState:
        """The `r` part or the `s` part: a state of the sixth seed with the same terms and names."""
        if rel == "r":
            return MState(self.n, self.r, self.names)
        if rel == "s":
            return MState(self.n, self.s, self.names)
        raise ValueError("a relation is r or s")

    def r_part(self) -> MState:
        """The `r` part."""
        return MState(self.n, self.r, self.names)

    def s_part(self) -> MState:
        """The `s` part."""
        return MState(self.n, self.s, self.names)

    def mult_of(self, rel: str, x: int, y: int) -> int:
        """The multiplicity of `xry` or `xsy`."""
        return self.part(rel).mult[x * self.n + y]

    def has(self, rel: str, x: int, y: int) -> bool:
        """Is `xry` (or `xsy`) asserted?"""
        return self.mult_of(rel, x, y) > 0

    @property
    def total_r(self) -> int:
        """The sum of the `r` multiplicities."""
        return sum(self.r)

    @property
    def total_s(self) -> int:
        """The sum of the `s` multiplicities."""
        return sum(self.s)

    @property
    def m(self) -> int:
        """How many assertions, counted, in both relations."""
        return self.total_r + self.total_s

    @property
    def distinct(self) -> int:
        """How many assertions are asserted (each counted once), both relations."""
        return sum(1 for k in self.r if k) + sum(1 for k in self.s if k)

    @property
    def size(self) -> int:
        """Terms plus assertions of both relations, counted with multiplicity."""
        return self.n + self.m

    @property
    def most(self) -> int:
        """The largest multiplicity in either relation (0 when nothing is asserted)."""
        return max(max(self.r, default=0), max(self.s, default=0))

    @property
    def legal_r(self) -> bool:
        """No `xrx` is asserted."""
        return all(self.r[x * self.n + x] == 0 for x in range(self.n))

    @property
    def legal_s(self) -> bool:
        """No `xsx` is asserted."""
        return all(self.s[x * self.n + x] == 0 for x in range(self.n))

    @property
    def simple(self) -> bool:
        """Nothing is asserted more than once, in either relation."""
        return all(k <= 1 for k in self.r) and all(k <= 1 for k in self.s)

    @property
    def nothing_in_s(self) -> bool:
        """Nothing is asserted with `s`: the state is a state of the sixth seed."""
        return self.total_s == 0

    def key(self) -> str:
        """A compact identifier of this exact writing (unambiguous with at most ten terms)."""
        names = "" if self.names is None else f"{self.names[0]}{self.names[1]}"
        body_r = ".".join(f"{x}-{y}*{k}" for x, y, k in self.r_part().counted)
        body_s = ".".join(f"{x}-{y}*{k}" for x, y, k in self.s_part().counted)
        return f"{self.n}:{names}:{body_r}|{body_s}"

    def term_writing(self) -> tuple[str, ...]:
        """One writing of the terms with letters (the named terms `a`, `b`; then the next letters)."""
        return self.r_part().term_writing()

    def written(self) -> str:
        """The state written in the seed's notation; a multiplicity above one in brackets."""
        w = self.term_writing()
        terms = " ".join(w)
        if self.names is not None and self.names[0] == self.names[1]:
            terms += " (a and b are one term)"
        parts = [f"{w[x]}r{w[y]}" + (f"({k})" if k > 1 else "") for x, y, k in self.r_part().counted]
        parts += [f"{w[x]}s{w[y]}" + (f"({k})" if k > 1 else "") for x, y, k in self.s_part().counted]
        return f"terms {terms}; asserted {' '.join(parts) or 'nothing'}"


def pair(r_part: MState, s_part: MState) -> DState:
    """The two-relation state with the given parts (same terms, same names)."""
    if r_part.n != s_part.n or r_part.names != s_part.names:
        raise ValueError("the two parts share their terms and their names")
    return DState(r_part.n, r_part.mult, s_part.mult, r_part.names)


def of_r(state: MState) -> DState:
    """A state of the sixth seed read as a two-relation state asserting nothing with `s`."""
    return DState(state.n, state.mult, (0,) * (state.n * state.n), state.names)


def rewrite(state: DState, p: tuple[int, ...]) -> DState:
    """The same state with term `t` written as `p[t]`, in both relations."""
    from fourth.state import rewrite as rewrite_part

    return pair(rewrite_part(state.r_part(), p), rewrite_part(state.s_part(), p))


_CANONICAL: dict[DState, DState] = {}


def canonical(state: DState) -> DState:
    """The least writing of `state`; equal exactly for same states.

    With `names` the rewriting carries the names along (ANCHORED) and the
    names come first in the comparison; without names every rewriting counts
    (FREE).  The rewriting acts on both relations at once: the `r`
    multiplicities are compared first, then the `s` ones.
    """
    hit = _CANONICAL.get(state)
    if hit is not None:
        return hit
    n = state.n
    best: tuple[int, int, tuple[int, ...], tuple[int, ...]] | None = None
    for p, index in _rewritings(n):
        r = [0] * (n * n)
        s = [0] * (n * n)
        for i, k in enumerate(state.r):
            if k:
                r[index[i]] = k
        for i, k in enumerate(state.s):
            if k:
                s[index[i]] = k
        a, b = (0, 0) if state.names is None else (p[state.names[0]], p[state.names[1]])
        cand = (a, b, tuple(r), tuple(s))
        if best is None or cand < best:
            best = cand
    assert best is not None  # there is always the rewriting that changes nothing
    out = DState(n, best[2], best[3], None if state.names is None else (best[0], best[1]))
    _CANONICAL[state] = out
    return out


def same(s: DState, t: DState) -> bool:
    """Do `s` and `t` differ only in how their terms are written?"""
    if s.n != t.n or (s.names is None) != (t.names is None):
        return False
    return canonical(s) == canonical(t)


def forget_canonical_forms() -> int:
    """Empty the cache of least writings; returns how many it held."""
    held = len(_CANONICAL)
    _CANONICAL.clear()
    return held


def given(bra: bool, sameness: Sameness) -> DState:
    """What is given: `a`, `b`; `arb` once; `bra` once or not at all; nothing with `s`."""
    return of_r(given_part(bra, sameness))


#: What is given counts two terms and one assertion (`bra` and everything in `s` are not given).
GIVEN_TERMS = 2
GIVEN_ASSERTIONS = 1


def added(state: DState) -> tuple[int, int]:
    """How many terms and assertions (both relations, with multiplicity) `state` adds to what is given."""
    return state.n - GIVEN_TERMS, state.m - GIVEN_ASSERTIONS


def remove(state: DState, rel: str, x: int, y: int) -> DState:
    """The state with the multiplicity of `xry` (or `xsy`) lowered by one."""
    if rel == "r":
        return pair(remove_part(state.r_part(), x, y), state.s_part())
    if rel == "s":
        return pair(state.r_part(), remove_part(state.s_part(), x, y))
    raise ValueError("a relation is r or s")


def identify(state: DState, x: int, y: int) -> DState:
    """The state with the terms `x < y` replaced by one term (written `x`) in every assertion of both relations."""
    return pair(identify_part(state.r_part(), x, y), identify_part(state.s_part(), x, y))


def names_one_term(state: DState) -> bool:
    """Are the names `a` and `b` carried by one term?  (False without names.)"""
    return state.names is not None and state.names[0] == state.names[1]

