"""States with filled terms, the results of the twenty-fourth seed, and the record of which filled terms balance.

Given by the twenty-fourth seed
    The twenty-third's sentences, word for word, except two: the list of
    changes gains a fifth kind — "A change is exactly one of: identifying two
    terms; removing an assertion; adding a term; adding an assertion; filling
    one term." — and one sentence is added: "A filled term `x` balances when
    `xrx` and `xsx` are asserted equally often; for every result, record which
    filled terms balance."

Cited from the twenty-third derivation (`twentythird.state`) and re-checked
    The two-relation state `DState` (no names), `excess_table`,
    `normal_table`, `rewrite_table`, the sums kept by its sameness (`two_way`,
    `around`) and `nothing_certificate` are about states and excess tables and
    mention no filled term: imported as they are (no change).  Its mark of a
    result (`result_key`) is extended here by the filled terms, carried by the
    same rewriting.

Chosen here (readings C-F1, C-S, C-B of the paper)
    A state is the twenty-third's state with, for each term, how many times it
    is filled (`fills`): zero or one under C-F1, any number under the unchosen
    C-F2.  A rewriting carries the filled terms with the terms; pairs asserted
    together and raising touch none; two results that differ in which terms
    are filled are two results.  `x` balances when `M_r(x, x) = M_s(x, x)`.

Derived (paper; `lean4_core/Twentyfourth/Same.lean`, `Balance.lean`)
    Two states are one result exactly when they have equally many terms and,
    after one rewriting, excesses differing by `g(x) − g(y)` and the same
    filled terms: the least over the rewritings of (normal table, filled
    terms) is a complete mark (`result_key`).  A loop's excess is kept by the
    sameness, so whether a filled term balances is read on the result
    (`balance_record`, from the mark).
"""

from __future__ import annotations

from dataclasses import dataclass

from fourth.state import _rewritings

from twentythird.state import DState, excess_table, normal_table, nothing_certificate, two_way
from twentythird.state import plain as plain_state

__all__ = [
    "DState",
    "FState",
    "Key24",
    "Table",
    "balance_record",
    "balances",
    "canonical",
    "empty",
    "forget",
    "forget_caches",
    "keeping_size",
    "keeping_terms",
    "key_balance",
    "of_state",
    "plain",
    "result_key",
    "rewrite",
    "same",
    "state_of",
    "swap",
    "tell_class",
    "told",
    "unbalanced_filled",
]

#: An excess table: `table[x * n + y]` is `e(x, y)`.
Table = tuple[int, ...]
#: The mark of a result: its terms, the least (normal table, fills) over the rewritings.
Key24 = tuple[int, Table, tuple[int, ...]]


@dataclass(frozen=True)
class FState:
    """A state of this seed: the twenty-third's state and, per term, how many times it is filled."""

    base: DState
    fills: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.base.names is not None:
            raise ValueError("a state of this seed carries no names")
        if len(self.fills) != self.base.n or any(k < 0 for k in self.fills):
            raise ValueError("one filling count, not negative, per term")

    @property
    def n(self) -> int:
        """The number of terms."""
        return self.base.n

    @property
    def filled(self) -> tuple[int, ...]:
        """The filled terms, in order."""
        return tuple(x for x, k in enumerate(self.fills) if k)

    @property
    def filled_count(self) -> int:
        """How many terms are filled."""
        return sum(1 for k in self.fills if k)

    @property
    def fillings(self) -> int:
        """How many fillings in all (the filled count under C-F1)."""
        return sum(self.fills)

    def key(self) -> str:
        """A compact identifier of this exact writing."""
        return f"{self.base.key()}|f{''.join(str(k) for k in self.fills)}"

    def written(self) -> str:
        """The state in the seed's notation, its filled terms named."""
        if self.n == 0:
            return "no terms; asserted nothing"
        text = self.base.written()
        w = self.base.term_writing()
        marks = [w[x] + (f"({k})" if k > 1 else "") for x, k in enumerate(self.fills) if k]
        return f"{text}; filled {' '.join(marks) if marks else 'none'}"


def empty() -> FState:
    """What is given: no terms, nothing asserted, nothing filled."""
    return FState(DState(0, (), ()), ())


def of_state(base: DState) -> FState:
    """A state of the twenty-third seed read as a state of this one with no term filled."""
    return FState(base, (0,) * base.n)


def forget(state: FState) -> DState:
    """The state with its filled terms forgotten: a state of the twenty-third seed."""
    return state.base


def plain(state: FState) -> FState:
    """Every pair asserted together taken out; the filled terms kept."""
    return FState(plain_state(state.base), state.fills)


def swap(state: FState) -> FState:
    """The two relations exchanged; the filled terms kept."""
    b = state.base
    return FState(DState(b.n, b.s, b.r), state.fills)


def rewrite(state: FState, p: tuple[int, ...]) -> FState:
    """The same state with term `t` written as `p[t]`: both relations and the filled terms."""
    n = state.n
    if sorted(p) != list(range(n)):
        raise ValueError("a rewriting writes each term once")
    r = [0] * (n * n)
    s = [0] * (n * n)
    fills = [0] * n
    for x in range(n):
        fills[p[x]] = state.fills[x]
        for y in range(n):
            r[p[x] * n + p[y]] = state.base.r[x * n + y]
            s[p[x] * n + p[y]] = state.base.s[x * n + y]
    return FState(DState(n, tuple(r), tuple(s)), tuple(fills))


_CANONICAL: dict[FState, FState] = {}
_KEYS: dict[FState, Key24] = {}


def canonical(state: FState) -> FState:
    """The least writing of `state` (both relations and the filled terms): equal exactly for same states."""
    hit = _CANONICAL.get(state)
    if hit is not None:
        return hit
    n = state.n
    best: tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]] | None = None
    for p, index in _rewritings(n):
        r = [0] * (n * n)
        s = [0] * (n * n)
        fills = [0] * n
        for i in range(n * n):
            r[index[i]] = state.base.r[i]
            s[index[i]] = state.base.s[i]
        for x in range(n):
            fills[p[x]] = state.fills[x]
        cand = (tuple(fills), tuple(r), tuple(s))
        if best is None or cand < best:
            best = cand
    assert best is not None  # the rewriting that changes nothing is always there
    out = FState(DState(n, best[1], best[2]), best[0])
    _CANONICAL[state] = out
    return out


def state_of(state: FState) -> FState:
    """The state an exploration keeps for `state`: its plain state at its least writing."""
    return canonical(plain(state))


def result_key(state: FState) -> Key24:
    """The mark of the result of `state`: equal exactly for two states that are one result."""
    hit = _KEYS.get(state)
    if hit is not None:
        return hit
    n = state.n
    table = excess_table(state.base)
    best: tuple[Table, tuple[int, ...]] | None = None
    for p, index in _rewritings(n):
        moved = [0] * (n * n)
        for i, e in enumerate(table):
            moved[index[i]] = e
        fills = [0] * n
        for x in range(n):
            fills[p[x]] = state.fills[x]
        cand = (normal_table(n, tuple(moved)), tuple(fills))
        if best is None or cand < best:
            best = cand
    assert best is not None
    key = (n, best[0], best[1])
    _KEYS[state] = key
    return key


def forget_caches() -> int:
    """Empty the caches of least writings and marks; returns how many entries they held."""
    held = len(_CANONICAL) + len(_KEYS)
    _CANONICAL.clear()
    _KEYS.clear()
    return held


def same(s: FState, t: FState) -> bool:
    """Are `s` and `t` one result (rewriting, pairs asserted together, raising; filled terms carried)?"""
    return s.n == t.n and result_key(s) == result_key(t)


def balances(state: FState, x: int) -> bool:
    """Is `x` filled and are `xrx` and `xsx` asserted equally often?"""
    n = state.n
    return state.fills[x] > 0 and state.base.r[x * n + x] == state.base.s[x * n + x]


def unbalanced_filled(state: FState) -> tuple[int, ...]:
    """The filled terms that do not balance."""
    return tuple(x for x in state.filled if not balances(state, x))


def key_balance(key: Key24) -> tuple[tuple[int, bool], ...]:
    """Which filled terms balance, read from the mark alone (at the result's least writing)."""
    n, table, fills = key
    return tuple((x, table[x * n + x] == 0) for x in range(n) if fills[x])


def balance_record(state: FState) -> tuple[int, int]:
    """(filled terms that balance, filled terms that do not): the record without the writing."""
    bad = len(unbalanced_filled(state))
    return state.filled_count - bad, bad


def told(state: FState) -> bool:
    """Is the result told apart from the one asserting nothing by a filled term that does not balance?"""
    return bool(unbalanced_filled(state))


def tell_class(state: FState) -> str:
    """How the result stands against the one asserting nothing on as many terms, the same terms filled.

    `nothing` (it is that result); `told` (a filled term does not balance);
    `one filling away` (a loop of non-zero excess, at unfilled terms only);
    `two terms` (every loop balances, a two-way sum is not zero); `three terms`
    (every loop and two-way sum is zero, a sum around three terms is not).
    """
    if told(state):
        return "told"
    cert = nothing_certificate(state.base)
    if cert is None:
        return "nothing"
    kind = cert[0]
    if kind == "loop":
        return "one filling away"
    return "two terms" if kind == "two-way" else "three terms"


def keeping_size(base: DState) -> int:
    """The fewest terms that keep a result from being the one asserting nothing (0 for that result).

    One when a loop's excess is not zero; else two when a two-way sum is not
    zero; else three when a sum around three terms is not zero (23:D2).
    """
    cert = nothing_certificate(base)
    if cert is None:
        return 0
    return {"loop": 1, "two-way": 2, "around": 3}[cert[0]]


def keeping_terms(base: DState) -> int:
    """How many terms lie in some smallest set keeping the result from the one asserting nothing.

    The smallest sets: a term whose loop is not zero; two terms whose loops are
    zero and whose two-way sum is not; three terms whose loops and two-way sums
    are zero and whose sum around is not.  Their union does not depend on the
    state of the result or its writing (the sums are kept, 23:D2).
    """
    n = base.n
    table = excess_table(base)
    loop = [table[x * n + x] != 0 for x in range(n)]
    terms = {x for x in range(n) if loop[x]}
    for x in range(n):
        for y in range(x + 1, n):
            if not (loop[x] or loop[y]) and two_way(n, table, x, y):
                terms |= {x, y}
    for x in range(n):
        for y in range(x + 1, n):
            for z in range(y + 1, n):
                if loop[x] or loop[y] or loop[z]:
                    continue
                if two_way(n, table, x, y) or two_way(n, table, y, z) or two_way(n, table, x, z):
                    continue
                if table[x * n + y] + table[y * n + z] + table[z * n + x]:
                    terms |= {x, y, z}
    return len(terms)
