"""Raising, the results of the twenty-third seed, and the sums that tell them apart.

Given by the twenty-third seed
    The twenty-second's sentences, word for word, except the sameness
    sentence, which gains a clause — "Two results that differ only in how
    their terms are written, only by an `xry` and an `xsy` asserted together,
    or only by raising terms, are the same result." — and one new sentence:
    "Raising a term `x` adds `xry` and `ysx` once for every other term `y`."

Cited from the twenty-second derivation (`twentysecond.state`) and re-checked
    The state (`DState`, no names), the empty beginning, `canonical` (the least
    writing), `rewrite`, `swap`, `excess`, `plain` and `written` are about
    states and mention no sameness of results: imported as they are (no
    change).  The twenty-second's result of a state (the least writing of its
    plain state, `plain_result`) and its cost (`plain_cost`, the terms plus the
    plain state's assertions) are used as what they are: a state of the
    exploration, and the size of that state.

Chosen here (reading C-H1 of the paper)
    Raising `x` gives the state with one more `xry` and one more `ysx` for
    every term `y ≠ x` (`raise_term`); "differ only by raising terms": one
    state is the other with terms raised, any number of times each; "are the
    same result": the equivalence the three clauses generate.

Derived (paper; `lean4_core/Twentythird/Same.lean`)
    Raising `x` moves the excess `e(x, y) = M_r(x, y) − M_s(x, y)` by `+1` and
    `e(y, x)` by `−1` for every `y ≠ x`, and nothing else.  Two states are the
    same result exactly when they have equally many terms and, after one
    rewriting, their excesses differ by `g(x) − g(y)` at every ordered pair,
    for whole numbers `g`.  Such a difference is determined by its values at
    the pairs `(x, 0)`, so an excess table made zero there (`normal_table`),
    least over the rewritings, is a complete mark of a result (`result_key`).
    Kept by the sameness: every loop's excess, every two-way sum
    `e(x, y) + e(y, x)`, every sum around three terms
    `e(x, y) + e(y, z) + e(z, x)`; a result is the one asserting nothing on
    its terms exactly when all of these are zero (`nothing_certificate` finds
    the first that is not).
"""

from __future__ import annotations

from collections.abc import Sequence

from fourth.state import _rewritings

from twentysecond.state import DState, MState, canonical, empty, excess, is_plain, of_r, plain, rewrite, swap, written
from twentysecond.state import cost as plain_cost
from twentysecond.state import result_of as plain_result

__all__ = [
    "Certificate",
    "align",
    "DState",
    "Key",
    "MState",
    "Table",
    "around",
    "canonical",
    "empty",
    "excess",
    "excess_table",
    "forget_keys",
    "is_nothing",
    "is_plain",
    "normal_table",
    "nothing_certificate",
    "nothing_key",
    "of_r",
    "plain",
    "plain_cost",
    "plain_of",
    "plain_result",
    "raise_term",
    "raise_terms",
    "result_key",
    "rewrite",
    "rewrite_table",
    "same",
    "shifted",
    "sum_profile",
    "swap",
    "total_excess",
    "two_way",
    "written",
]

#: An excess table: `table[x * n + y]` is `e(x, y)`.
Table = tuple[int, ...]
#: The mark of a result: its terms and the least normal table over the rewritings.
Key = tuple[int, Table]
#: What shows a result is not the one asserting nothing: the kind of sum, its terms, its value.
Certificate = tuple[str, tuple[int, ...], int]


def excess_table(state: DState) -> Table:
    """The excess `M_r(x, y) − M_s(x, y)` at every ordered pair."""
    return tuple(a - b for a, b in zip(state.r, state.s))


def plain_of(n: int, table: Table) -> DState:
    """The state on `n` terms asserting no pair in both relations whose excess is `table`."""
    if len(table) != n * n:
        raise ValueError("an excess table has one entry per ordered pair")
    return DState(n, tuple(max(e, 0) for e in table), tuple(max(-e, 0) for e in table))


def raise_term(state: DState, x: int) -> DState:
    """Raising `x`: one more `xry` and one more `ysx` for every term `y` other than `x`."""
    n = state.n
    if not 0 <= x < n:
        raise ValueError("a raised term is a term of the state")
    r = list(state.r)
    s = list(state.s)
    for y in range(n):
        if y != x:
            r[x * n + y] += 1
            s[y * n + x] += 1
    return DState(n, tuple(r), tuple(s))


def raise_terms(state: DState, counts: Sequence[int]) -> DState:
    """Every term `x` raised `counts[x]` times."""
    if len(counts) != state.n or any(k < 0 for k in counts):
        raise ValueError("one count, not negative, per term")
    out = state
    for x, k in enumerate(counts):
        for _ in range(k):
            out = raise_term(out, x)
    return out


def shifted(n: int, table: Table, g: Sequence[int]) -> Table:
    """`table` moved by `g(x) − g(y)` at every ordered pair (raising each `x` `g(x)` times, read on the excess)."""
    return tuple(table[x * n + y] + g[x] - g[y] for x in range(n) for y in range(n))


def normal_table(n: int, table: Table) -> Table:
    """The table moved so that its excess is zero at every pair `(x, 0)`, `x ≠ 0`.

    With `g(0) = 0` and `g(x) = −e(x, 0)`; two tables differ by some
    `g(x) − g(y)` exactly when their normal tables are equal.
    """
    if n == 0:
        return ()
    g = [0] + [-table[x * n] for x in range(1, n)]
    return shifted(n, table, g)


def rewrite_table(n: int, table: Table, p: Sequence[int]) -> Table:
    """The table with term `t` written as `p[t]`."""
    out = [0] * (n * n)
    for x in range(n):
        for y in range(n):
            out[p[x] * n + p[y]] = table[x * n + y]
    return tuple(out)


_KEYS: dict[DState, Key] = {}


def result_key(state: DState) -> Key:
    """The mark of the result of `state`: equal exactly for two states that are one result."""
    hit = _KEYS.get(state)
    if hit is not None:
        return hit
    n = state.n
    table = excess_table(state)
    best: Table | None = None
    for _, index in _rewritings(n):
        moved = [0] * (n * n)
        for i, e in enumerate(table):
            moved[index[i]] = e
        cand = normal_table(n, tuple(moved))
        if best is None or cand < best:
            best = cand
    assert best is not None  # the rewriting that changes nothing is always there
    key = (n, best)
    _KEYS[state] = key
    return key


def align(state: DState, target: DState) -> DState:
    """A rewriting of `state` that is the same result as `target` at `target`'s writing."""
    n = state.n
    want = normal_table(n, excess_table(target))
    table = excess_table(state)
    for p, _ in _rewritings(n):
        if target.n == n and normal_table(n, rewrite_table(n, table, p)) == want:
            return rewrite(state, p)
    raise ValueError("the two states are not one result")


def forget_keys() -> int:
    """Empty the cache of marks; returns how many it held."""
    held = len(_KEYS)
    _KEYS.clear()
    return held


def same(s: DState, t: DState) -> bool:
    """Are `s` and `t` one result (rewriting, pairs asserted together, raising)?"""
    return s.n == t.n and result_key(s) == result_key(t)


def nothing_key(n: int) -> Key:
    """The mark of the result asserting nothing on `n` terms."""
    return (n, (0,) * (n * n))


def two_way(n: int, table: Table, x: int, y: int) -> int:
    """`e(x, y) + e(y, x)`: kept by raising (the two moves cancel)."""
    return table[x * n + y] + table[y * n + x]


def around(n: int, table: Table, x: int, y: int, z: int) -> int:
    """`e(x, y) + e(y, z) + e(z, x)`: the sum around three terms, kept by raising."""
    return table[x * n + y] + table[y * n + z] + table[z * n + x]


def total_excess(state: DState) -> int:
    """`Σ e` over all ordered pairs: `Σ M_r − Σ M_s`, kept by raising."""
    return state.total_r - state.total_s


def nothing_certificate(state: DState) -> Certificate | None:
    """The first loop, two terms or three terms whose sum is not zero; `None` exactly for the result
    asserting nothing on the state's terms."""
    n = state.n
    table = excess_table(state)
    for x in range(n):
        if table[x * n + x]:
            return ("loop", (x,), table[x * n + x])
    for x in range(n):
        for y in range(x + 1, n):
            v = two_way(n, table, x, y)
            if v:
                return ("two-way", (x, y), v)
    for x in range(n):
        for y in range(x + 1, n):
            for z in range(y + 1, n):
                v = around(n, table, x, y, z)
                if v:
                    return ("around", (x, y, z), v)
    return None


def is_nothing(state: DState) -> bool:
    """Is the state's result the one asserting nothing on its terms?"""
    return nothing_certificate(state) is None


def sum_profile(state: DState) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], int]:
    """The loops, two-way sums and sums around three terms (both ways round), each sorted, and `Σ e`.

    Computed from the excess alone, without `result_key`: two states of one
    result have the same profile (the sums are kept by every clause of the
    sameness, and sorting forgets the writing).
    """
    n = state.n
    table = excess_table(state)
    loops = sorted(table[x * n + x] for x in range(n))
    pairs = sorted(two_way(n, table, x, y) for x in range(n) for y in range(x + 1, n))
    rounds = sorted(
        v
        for x in range(n)
        for y in range(x + 1, n)
        for z in range(y + 1, n)
        for v in (around(n, table, x, y, z), around(n, table, x, z, y))
    )
    return tuple(loops), tuple(pairs), tuple(rounds), sum(table)
