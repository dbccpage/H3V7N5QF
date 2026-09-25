"""The unchosen readings C-J2 and C-J3 of the changed sentence, computed at a small bound.

Kept because each gives different results (rule 4 of the task).

C-J2 (the letters as placeholders: any `xry` with any `usv`)
    The sameness these steps generate keeps the terms and the difference of
    the two totals `D = Σ M_r − Σ M_s` and nothing else: with a term, any
    two states with equally many terms and the same `D` are joined by adding
    and taking out such pairs (paper).  A result is `(n, D)`, `D = 0` when
    `n = 0`.  Every change moves `n + |D|` by at most one (an identification
    keeps both totals), and additions reach `(n, D)` in `n + |D|`: the cost
    is `n + |D|` (`cost_j2`); the results of round `r` within `N` terms are
    `[r = 0] + [1 ≤ r ≤ N] + 2·min(r − 1, N)` for `r ≥ 1`
    (`round_count_j2`).  The exploration (`explore_j2`) attempts the changes
    of a state of each result that asserts a pair in both relations, so that
    both removals are there; the outcomes of every state of a result are
    among them (paper).

C-J3 (only two different terms: `xrx` and `xsx` are not merged)
    Off the diagonal the excess is kept; on it both multiplicities.  Under
    the chosen C-X′ reading (a result's changes are those of its reduced
    state, `reduce_j3`), the cost is the size of the reduced state
    (`cost_j3`) and the results are counted per cycle of pairs: off the
    diagonal `(1 + x^L)/(1 − x^L)`, on it `1/(1 − x^L)²` (`count_j3`).
    Under C-X (a change of any state of the result), identification depends
    on the state taken: two terms with `k` copies of `0r1` and `0s1` (one
    result with the two terms asserting nothing) identify to one term asserting
    `ara` and `asa` `k` times each — a different result for every `k`, all
    three changes from the empty state (`padding_witness`): round 3 is
    infinite and no bound on terms and rounds makes the rounds finite.
"""

from __future__ import annotations

from math import factorial

from ninth.changes import Kind, changes, perform
from ninth.changes import Change as NinthChange
from xry.orbits import class_size, partitions

from twentysecond.orbits import all_pair_cycles
from twentysecond.state import DState, canonical

__all__ = [
    "cost_j2",
    "cost_j3",
    "count_j3",
    "explore_j2",
    "explore_j3",
    "key_j2",
    "padding_witness",
    "reduce_j3",
    "rep_j2",
    "round_count_j2",
]


def key_j2(state: DState) -> tuple[int, int]:
    """The result of a state under C-J2: its terms and `Σ M_r − Σ M_s`."""
    return state.n, state.total_r - state.total_s


def rep_j2(n: int, d: int) -> DState:
    """A state of the C-J2 result `(n, d)` asserting a pair in both relations (when it has a term)."""
    if n == 0:
        return DState(0, (), ())
    r = [0] * (n * n)
    s = [0] * (n * n)
    r[0] = 1 + max(d, 0)
    s[0] = 1 + max(-d, 0)
    return DState(n, tuple(r), tuple(s))


def cost_j2(key: tuple[int, int]) -> int:
    """`n + |D|`."""
    return key[0] + abs(key[1])


def explore_j2(bound: int, rounds: int) -> dict[tuple[int, int], int]:
    """Results under C-J2 within `bound` terms and `rounds` rounds, with their rounds."""
    depth = {(0, 0): 0}
    wave = [(0, 0)]
    for r in range(1, rounds + 1):
        found = []
        for key in wave:
            rep = rep_j2(*key)
            for change in changes(rep):
                out = perform(rep, change)
                if out.n > bound:
                    continue
                k = key_j2(out)
                if k not in depth:
                    depth[k] = r
                    found.append(k)
        wave = sorted(found)
    return depth


def round_count_j2(r: int, bound: int) -> int:
    """Results of round `r` within `bound` terms under C-J2, in closed form."""
    if r == 0:
        return 1
    return int(r <= bound) + 2 * min(r - 1, bound)


def reduce_j3(state: DState) -> DState:
    """Off the diagonal, the pairs asserted in both relations taken out; on it, nothing taken out."""
    n = state.n
    r = list(state.r)
    s = list(state.s)
    for x in range(n):
        for y in range(n):
            if x != y:
                i = x * n + y
                c = min(r[i], s[i])
                r[i] -= c
                s[i] -= c
    return DState(n, tuple(r), tuple(s))


def cost_j3(state: DState) -> int:
    """The size of the reduced state: terms, `Σ |excess|` off the diagonal, both multiplicities on it."""
    return reduce_j3(state).size


def explore_j3(bound: int, rounds: int) -> dict[DState, int]:
    """Results under C-J3 (changes of the reduced state, C-X′) within `bound` terms and `rounds` rounds."""
    root = DState(0, (), ())
    depth = {root: 0}
    wave = [root]
    for r in range(1, rounds + 1):
        found = []
        for state in wave:
            for change in changes(state):
                out = perform(state, change)
                if out.n > bound:
                    continue
                k = canonical(reduce_j3(out))
                if k not in depth:
                    depth[k] = r
                    found.append(k)
        wave = sorted(found, key=lambda s: (s.n, s.r, s.s))
    return depth


def count_j3(n: int, degree: int) -> list[int]:
    """Results under C-J3 with `n` terms by cost minus terms, `0..degree`, by orbit counting."""
    total = [0] * (degree + 1)
    for parts in partitions(n):
        cycles = all_pair_cycles(parts)
        poly = [1] + [0] * degree
        for length, count in sorted(cycles.items()):
            diagonal = parts.count(length)
            for i in range(count):
                if i < diagonal:
                    for _ in range(2):
                        for j in range(length, degree + 1):
                            poly[j] += poly[j - length]
                else:
                    nxt = list(poly)
                    for j, c in enumerate(poly):
                        if c:
                            for k in range(j + length, degree + 1, length):
                                nxt[k] += 2 * c
                    poly = nxt
        size = class_size(parts)
        for t, c in enumerate(poly):
            total[t] += size * c
    return [c // factorial(n) for c in total]


def padding_witness(k: int) -> tuple[DState, DState, int]:
    """Under C-J3 and C-X: a state of the two-term result asserting nothing, and its identification.

    Returns the padded state (two terms, `k` copies of `0r1` and of `0s1`),
    the reduced result of identifying its two terms (one term, `ara` and
    `asa` `k` times each), and that result's cost under C-X′.
    """
    padded = DState(2, (0, k, 0, 0), (0, k, 0, 0))
    out = perform(padded, NinthChange(Kind.IDENTIFY, "", 0, 1))
    result = canonical(reduce_j3(out))
    return padded, result, cost_j3(result)
