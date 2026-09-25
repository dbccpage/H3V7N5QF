"""Filled triples, the states that carry them, the five kinds of change, and the balance record.

Given by the twenty-fifth seed
    The twenty-third's sentences, word for word, except that the list of the
    kinds of change gains a fifth — "filling three different terms" — and one
    sentence is added: "Three filled terms `x`, `y`, `z` balance when, going
    from `x` to `y` to `z` and back to `x`, as many assertions are written
    with `r` as with `s`, each counted as often as it is asserted; for every
    result, record which filled terms balance."

Cited from the twenty-second and twenty-third derivations and re-checked
    The two-relation state (`DState`, no names), `plain`, `excess`,
    `written`, raising, `normal_table`, `rewrite_table`, `excess_table`, the
    sum around three terms (`around`), the sums that show a result is not the
    one asserting nothing (`nothing_certificate`) and the twenty-third's mark
    of a result (`result_key`) are about states and the four kinds of change
    or about the twenty-third's sameness, which this seed repeats word for
    word: imported as they are (no change).  The ninth's `Change`, `changes`
    and `perform` are the four kinds on states: imported, and the filled
    triples carried alongside.

Chosen here (readings of the paper)
    * C-F1: a state carries its filled triples; filling three different
      terms makes them a filled triple and changes nothing else; filling a
      triple already filled changes nothing and is not a change.
    * C-O1: a filled triple keeps the order in which its terms are gone round;
      `x, y, z` is `y, z, x` and `z, x, y`, and `x, z, y` is another filled
      triple.  Written from its least term (`way_round`).
    * C-B1: going from `x` to `y` goes along `xry` and `xsy`; the triple
      balances when `e(x, y) + e(y, z) + e(z, x) = 0` (`balances`).
    * C-M1: a triple is filled or not.
    * C-I1: identifying two terms replaces both by one term in every filled
      triple too; a triple left without three different terms is dropped, two
      that become one are one (`carry`).
    * C-A: fillings are attempted with the changes adding nothing — after the
      removals, before a term (`changes`).
    * Sameness: a rewriting of the terms carries the filled triples; pairs
      asserted together and raising do not touch them.  So a result is its
      twenty-third result and its filled triples, up to one rewriting of both
      (`result_mark`).
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from itertools import combinations

from fourth.state import _rewritings
from ninth.changes import Change, Kind
from ninth.changes import changes as changes_of_state
from ninth.changes import perform as perform_on_state
from xry.changes import identification_map

from twentythird.state import DState, Table, around, empty, excess_table, normal_table, plain, written

__all__ = [
    "Change25",
    "DState",
    "FState",
    "Filling",
    "Mark",
    "Triple",
    "align",
    "balance_record",
    "balances",
    "canonical_state",
    "carry",
    "changes",
    "empty25",
    "embed",
    "forget_marks",
    "is_addition",
    "nothing_with",
    "oriented_triples",
    "perform",
    "plain_state",
    "rename_triples",
    "result_mark",
    "rewrite25",
    "swap25",
    "unbalanced",
    "way_round",
    "written25",
]

#: A filled triple: three different terms, in the order they are gone round, written from the least.
Triple = tuple[int, int, int]
#: The mark of a result: terms, the normal excess table, the filled triples (least over the rewritings).
Mark = tuple[int, Table, tuple[Triple, ...]]


def way_round(x: int, y: int, z: int) -> Triple:
    """The triple gone round `x → y → z → x`, written from its least term."""
    if x <= y and x <= z:
        return (x, y, z)
    if y <= z:
        return (y, z, x)
    return (z, x, y)


def oriented_triples(n: int) -> tuple[Triple, ...]:
    """Every filled triple possible on `n` terms: each three terms, both ways round, in order."""
    out: list[Triple] = []
    for x, y, z in combinations(range(n), 3):
        out.append((x, y, z))
        out.append((x, z, y))
    return tuple(sorted(out))


@dataclass(frozen=True)
class FState:
    """A state of the seed: the two relations' multiplicities, and the filled triples (sorted, each once)."""

    state: DState
    filled: tuple[Triple, ...] = ()

    def __post_init__(self) -> None:
        if self.state.names is not None:
            raise ValueError("a state of this seed carries no names")
        n = self.state.n
        for t in self.filled:
            x, y, z = t
            if not (0 <= x < n and 0 <= y < n and 0 <= z < n) or len({x, y, z}) != 3:
                raise ValueError("a filled triple is three different terms of the state")
            if way_round(x, y, z) != t:
                raise ValueError("a filled triple is written from its least term")
        if list(self.filled) != sorted(set(self.filled)):
            raise ValueError("the filled triples are listed once each, in order")

    @property
    def n(self) -> int:
        """The number of terms."""
        return self.state.n

    def key(self) -> str:
        """A compact identifier of this exact writing."""
        return self.state.key() + "|" + ".".join(f"{x}{y}{z}" for x, y, z in self.filled)


def empty25() -> FState:
    """The beginning: no terms, nothing asserted, nothing filled."""
    return FState(empty(), ())


def embed(state: DState) -> FState:
    """A state of the twenty-third seed read as a state of this seed with nothing filled."""
    return FState(state, ())


def written25(fs: FState) -> str:
    """The state in the seed's notation, its filled triples after it (`filled abc` goes a → b → c → a)."""
    base = written(fs.state)
    if not fs.filled:
        return base
    w = fs.state.term_writing()
    return base + "; filled " + " ".join(w[x] + w[y] + w[z] for x, y, z in fs.filled)


@dataclass(frozen=True)
class Filling:
    """The fifth kind of change: filling the three different terms `x`, `y`, `z`, gone round in that order."""

    x: int
    y: int
    z: int

    def written(self, state: DState) -> str:
        """The change in words."""
        w = state.term_writing()
        return f"fill {w[self.x]} {w[self.y]} {w[self.z]}"


#: One change of the seed: one of the ninth's four kinds, or a filling.
Change25 = Change | Filling


def is_addition(change: Change25) -> bool:
    """Does the change add a term or an assertion?  (A filling adds neither.)"""
    return isinstance(change, Change) and change.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION)


def carry(n: int, filled: Iterable[Triple], u: int, v: int) -> tuple[Triple, ...]:
    """The filled triples after identifying the terms `u < v` of `n` (reading C-I1)."""
    q = identification_map(n, u, v)
    out: set[Triple] = set()
    for x, y, z in filled:
        a, b, c = q[x], q[y], q[z]
        if len({a, b, c}) == 3:
            out.add(way_round(a, b, c))
    return tuple(sorted(out))


def changes(fs: FState) -> tuple[Change25, ...]:
    """Every change of the state, fewest additions first (reading C-A).

    Identifications, removals in `r`, in `s` (the ninth's), then every triple
    not yet filled, then a term, then the additions in `r`, in `s`.
    """
    four = changes_of_state(fs.state)
    first = [c for c in four if c.kind in (Kind.IDENTIFY, Kind.REMOVE)]
    rest = [c for c in four if c.kind not in (Kind.IDENTIFY, Kind.REMOVE)]
    have = set(fs.filled)
    fillings: list[Change25] = [Filling(*t) for t in oriented_triples(fs.n) if t not in have]
    return (*first, *fillings, *rest)


def perform(fs: FState, change: Change25) -> FState:
    """The outcome of a change."""
    if isinstance(change, Filling):
        t = way_round(change.x, change.y, change.z)
        if t in fs.filled:
            raise ValueError("filling a filled triple changes nothing and is not a change")
        return FState(fs.state, tuple(sorted((*fs.filled, t))))
    out = perform_on_state(fs.state, change)
    if change.kind is Kind.IDENTIFY:
        return FState(out, carry(fs.n, fs.filled, change.x, change.y))
    return FState(out, fs.filled)


def plain_state(fs: FState) -> FState:
    """The same result's state with every pair asserted together taken out (the filled triples kept)."""
    return FState(plain(fs.state), fs.filled)


def rename_triples(filled: Iterable[Triple], p: Sequence[int]) -> tuple[Triple, ...]:
    """The filled triples with term `t` written as `p[t]`."""
    return tuple(sorted(way_round(p[x], p[y], p[z]) for x, y, z in filled))


def rewrite25(fs: FState, p: Sequence[int]) -> FState:
    """The state with term `t` written as `p[t]`, in both relations and in the filled triples."""
    n = fs.n
    r = [0] * (n * n)
    s = [0] * (n * n)
    for x in range(n):
        for y in range(n):
            r[p[x] * n + p[y]] = fs.state.r[x * n + y]
            s[p[x] * n + p[y]] = fs.state.s[x * n + y]
    return FState(DState(n, tuple(r), tuple(s)), rename_triples(fs.filled, p))


_CANONICAL: dict[FState, FState] = {}
_MARKS: dict[FState, Mark] = {}


def canonical_state(fs: FState) -> FState:
    """The least writing of the state (its multiplicities and filled triples together)."""
    hit = _CANONICAL.get(fs)
    if hit is not None:
        return hit
    n = fs.n
    best: tuple[tuple[int, ...], tuple[int, ...], tuple[Triple, ...]] | None = None
    for p, index in _rewritings(n):
        r = [0] * (n * n)
        s = [0] * (n * n)
        for i, k in enumerate(fs.state.r):
            if k:
                r[index[i]] = k
        for i, k in enumerate(fs.state.s):
            if k:
                s[index[i]] = k
        cand = (tuple(r), tuple(s), rename_triples(fs.filled, p))
        if best is None or cand < best:
            best = cand
    assert best is not None  # the rewriting that changes nothing is always there
    out = FState(DState(n, best[0], best[1]), best[2])
    _CANONICAL[fs] = out
    return out


def result_mark(fs: FState) -> Mark:
    """The mark of the result of `fs`: equal exactly for two states that are one result."""
    hit = _MARKS.get(fs)
    if hit is not None:
        return hit
    n = fs.n
    table = excess_table(fs.state)
    best: tuple[Table, tuple[Triple, ...]] | None = None
    for p, index in _rewritings(n):
        moved = [0] * (n * n)
        for i, e in enumerate(table):
            moved[index[i]] = e
        cand = (normal_table(n, tuple(moved)), rename_triples(fs.filled, p))
        if best is None or cand < best:
            best = cand
    assert best is not None
    mark = (n, best[0], best[1])
    _MARKS[fs] = mark
    return mark


def forget_marks() -> int:
    """Empty the caches of least writings and marks; returns how many entries they held."""
    held = len(_CANONICAL) + len(_MARKS)
    _CANONICAL.clear()
    _MARKS.clear()
    return held


def align(fs: FState, target: FState) -> FState:
    """A rewriting of `fs` that is the same result as `target` at `target`'s writing."""
    n = fs.n
    want = (normal_table(n, excess_table(target.state)), target.filled)
    for p, _ in _rewritings(n):
        moved = rewrite25(fs, p)
        if target.n == n and (normal_table(n, excess_table(moved.state)), moved.filled) == want:
            return moved
    raise ValueError("the two states are not one result")


def balances(fs: FState, t: Triple) -> bool:
    """Going round `t`, as many assertions written with `r` as with `s` (each counted as often as asserted)."""
    x, y, z = t
    return around(fs.n, excess_table(fs.state), x, y, z) == 0


def balance_record(fs: FState) -> tuple[tuple[Triple, bool], ...]:
    """Which filled triples balance: every filled triple with its verdict."""
    return tuple((t, balances(fs, t)) for t in fs.filled)


def unbalanced(fs: FState) -> tuple[Triple, ...]:
    """The filled triples that do not balance."""
    return tuple(t for t in fs.filled if not balances(fs, t))


def nothing_with(fs: FState) -> FState:
    """The result asserting nothing on the same terms, with the same filled triples."""
    n = fs.n
    return FState(DState(n, (0,) * (n * n), (0,) * (n * n)), fs.filled)


def swap25(fs: FState) -> FState:
    """The two relations exchanged; the filled triples kept."""
    return FState(DState(fs.n, fs.state.s, fs.state.r), fs.filled)
