"""The fewest changes to a result, and the states of a result asserting the fewest.

Derived (paper; `lean4_core/Twentythird/Cost.lean`)
    Every state is reached from the empty state, the fewest changes to a
    state being its size (the ninth's, re-proved by the twenty-second), so the
    fewest changes to a result is the least size among its states: its terms
    plus the fewest assertions among its states.  A state asserting the
    fewest asserts no pair in both relations (taking a pair out keeps the
    result), so the fewest assertions is `min_g Σ |e(x, y) + g(x) − g(y)|`
    over whole numbers `g(x)`, the excess moved by raising (`fewest`).

    *Raising sets of terms reaches it.*  Raising every term of a set `X` once
    moves `e(x, y)` by `+1` for `x ∈ X`, `y ∉ X` and by `−1` the other way.  A
    table from which raising no set lowers `Σ |e|` is a least one (paper,
    D5: take a least `g*` nearest to `g`, the set where `g* − g` is largest,
    and the per-pair inequality of a sum of two absolute values); so raising
    sets while the count falls (`descend`) reaches the fewest, and the tables
    of least count are connected by raisings of sets that keep the count
    (`least_tables`, the same inequality).

    *Closed forms.*  With at most two terms the fewest is
    `Σ |loops| + |e(0, 1) + e(1, 0)|`; with three terms
    `Σ |loops| + Σ |two-way| + 2 · dist(T, [−N, P])`, `T` the sum around
    `0, 1, 2`, `P` and `N` the positive and negative parts of the two-way sums
    added up (`cost_closed`).  In general the loops and two-way sums give a
    lower bound (`lower_bound`), not always reached (three terms, `T` outside).

Computed
    `search_fewest` tries every `g` with `g(0) = 0` in a box; used only to
    check `descend` on small tables.
"""

from __future__ import annotations

from collections.abc import Iterator
from itertools import product

from twentythird.state import DState, Table, excess_table, plain_of, shifted, total_excess, two_way

__all__ = [
    "cost",
    "cost_closed",
    "descend",
    "fewest",
    "fewest_states",
    "least_tables",
    "lower_bound",
    "masks",
    "raise_set",
    "record",
    "search_box",
    "search_fewest",
    "set_moves_least",
    "single_moves_least",
    "table_weight",
    "together_free_of_opposites",
]


def table_weight(table: Table) -> int:
    """`Σ |e|`: the assertions of the state with that excess asserting no pair in both relations."""
    return sum(abs(e) for e in table)


def masks(n: int) -> range:
    """The sets of terms that can be raised to some effect: every set but none and all (as bit masks)."""
    return range(1, (1 << n) - 1) if n >= 2 else range(0)


def raise_set(n: int, table: Table, mask: int) -> Table:
    """The table after raising every term of the set `mask` once."""
    return shifted(n, table, [(mask >> x) & 1 for x in range(n)])


def descend(n: int, table: Table) -> Table:
    """Raise sets of terms, the first that lowers the count each time, until none does."""
    cur = table
    weight = table_weight(cur)
    while True:
        for mask in masks(n):
            nxt = raise_set(n, cur, mask)
            w = table_weight(nxt)
            if w < weight:
                cur, weight = nxt, w
                break
        else:
            return cur


def fewest(state: DState) -> int:
    """The fewest assertions among the states of the result of `state`."""
    return table_weight(descend(state.n, excess_table(state)))


def cost(state: DState) -> int:
    """The fewest changes from the empty state to the result of `state`: terms plus the fewest assertions."""
    return state.n + fewest(state)


def record(state: DState) -> tuple[int, int, int]:
    """What is recorded for the result of `state` (reading C-R): terms, and the assertions in `r` and in
    `s` of a state asserting the fewest — the same for all of them, `(w ± Σ e) / 2`."""
    w = fewest(state)
    t = total_excess(state)
    return state.n, (w + t) // 2, (w - t) // 2


def set_moves_least(n: int, table: Table) -> bool:
    """Does raising no set of terms lower the count?"""
    w = table_weight(table)
    return all(table_weight(raise_set(n, table, m)) >= w for m in masks(n))


def single_moves_least(n: int, table: Table) -> bool:
    """Does raising no single term, and no set of all terms but one, lower the count?"""
    w = table_weight(table)
    full = (1 << n) - 1
    singles = [1 << x for x in range(n)] + [full ^ (1 << x) for x in range(n)]
    return all(table_weight(raise_set(n, table, m)) >= w for m in singles if m in masks(n))


def together_free_of_opposites(n: int, table: Table) -> bool:
    """No `xry` asserted together with `ysx` (read on the table): for two terms, the whole condition."""
    return all(
        not (table[x * n + y] > 0 and table[y * n + x] < 0) for x in range(n) for y in range(n) if x != y
    )


def least_tables(n: int, table: Table) -> list[Table]:
    """Every table of least count reached from `table` by raising: the fewest states' excesses.

    Starts from `descend`, then follows raisings of sets that keep the least
    count (the least tables are connected that way, paper D5).  Sorted.
    """
    start = descend(n, table)
    least = table_weight(start)
    seen = {start}
    todo = [start]
    while todo:
        cur = todo.pop()
        for m in masks(n):
            nxt = raise_set(n, cur, m)
            if nxt not in seen and table_weight(nxt) == least:
                seen.add(nxt)
                todo.append(nxt)
    return sorted(seen)


def fewest_states(state: DState) -> list[DState]:
    """The states of the result of `state` asserting the fewest, at the state's writing."""
    return [plain_of(state.n, t) for t in least_tables(state.n, excess_table(state))]


def lower_bound(state: DState) -> int:
    """Terms plus `Σ |loops| + Σ |two-way sums|`: kept by the sameness, never above the cost."""
    n = state.n
    table = excess_table(state)
    loops = sum(abs(table[x * n + x]) for x in range(n))
    pairs = sum(abs(two_way(n, table, x, y)) for x in range(n) for y in range(x + 1, n))
    return n + loops + pairs


def cost_closed(state: DState) -> int | None:
    """The cost in closed form, with at most three terms; `None` beyond."""
    n = state.n
    if n > 3:
        return None
    base = lower_bound(state)
    if n < 3:
        return base
    table = excess_table(state)
    sums = [two_way(3, table, 0, 1), two_way(3, table, 1, 2), two_way(3, table, 2, 0)]
    t = table[1] + table[5] + table[6]  # e(0, 1) + e(1, 2) + e(2, 0)
    top = sum(max(v, 0) for v in sums)
    bottom = -sum(max(-v, 0) for v in sums)
    return base + 2 * max(0, t - top, bottom - t)


def search_box(n: int, table: Table) -> int:
    """A box holding a least `g` with `g(0) = 0`: `(n − 1)` times the largest excess between two terms.

    (Paper D5: where two neighbouring values of `g`, sorted, are further apart
    than every excess between two terms, raising every term of the lower part
    lowers the count; so a least `g` has no such gap.)
    """
    most = max((abs(table[x * n + y]) for x in range(n) for y in range(n) if x != y), default=0)
    return (n - 1) * most


def _gs(n: int, box: int) -> Iterator[tuple[int, ...]]:
    for rest in product(range(-box, box + 1), repeat=max(n - 1, 0)):
        yield (0, *rest)


def search_fewest(state: DState) -> int:
    """The fewest assertions by trying every `g` in the box (small tables only)."""
    n = state.n
    table = excess_table(state)
    if n == 0:
        return 0
    return min(table_weight(shifted(n, table, g)) for g in _gs(n, search_box(n, table)))
