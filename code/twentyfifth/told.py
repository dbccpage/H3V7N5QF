"""Which results filled triples that do not balance tell from a result asserting nothing, and which they cannot.

Derived (paper, D3–D6; `lean4_core/Twentyfifth/Balance.lean`, `Blind.lean`)
    * A result asserting nothing balances every filled triple, so a result is
      told from the result asserting nothing on as many terms (with the same
      filled triples) by filled triples that do not balance exactly when one
      of its filled triples does not balance (`told`).  The direct reading —
      the two records compared — is `record_differs_from_nothing`.
    * Not told: every result with nothing filled; a result differing from
      nothing only at loops (a loop is never gone along); a result whose sums
      around the filled triples are zero while another sum is not
      (`why_not_told`).
    * Blind (no filling tells it): every sum around three different terms,
      both ways round, is zero (`blind`).  What that forces on the two-way
      sums (`blind_by_description`): with three terms, they add up to zero;
      with four, they are equal on the two pairs of each split of the terms
      and the three values add up to zero; with five or more, they are zero.
    * With every loop and two-way sum zero, a set of filled triples decides
      (every such result balancing them all is the one asserting nothing)
      exactly when their sums around have rank `C(n − 1, 2)` on the excesses
      with every two-way sum zero (`decides`); when it does not, an integer
      witness balancing them all and not the result asserting nothing exists
      (`undecided_witness`).
    * The least sets of terms keeping a result from being the one asserting
      nothing (the task's words, reading of the paper): a term with a loop;
      two terms with every loop zero and their two-way sum not; three terms
      with every loop and two-way sum among them zero and their sum around
      not (`keeping_sets`).  Found again by reading the result on every set
      of terms (`keeping_sets_by_restriction`).
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from fractions import Fraction
from itertools import combinations
from math import comb

from twentythird.state import DState, Table, around, excess_table, is_nothing, plain_of, two_way

from twentyfifth.state import FState, Triple, balance_record, nothing_with, unbalanced

__all__ = [
    "antisymmetric_rows",
    "blind",
    "blind_by_description",
    "decides",
    "keeping_sets",
    "keeping_sets_by_restriction",
    "rank",
    "record_differs_from_nothing",
    "restrict",
    "told",
    "undecided_witness",
    "why_not_told",
]


def told(fs: FState) -> bool:
    """Is some filled triple not balanced?"""
    return bool(unbalanced(fs))


def record_differs_from_nothing(fs: FState) -> bool:
    """Does the record of which filled triples balance differ from that of the result asserting nothing on the
    same terms with the same filled triples?"""
    return balance_record(fs) != balance_record(nothing_with(fs))


def _without_loops_nothing(n: int, table: Table) -> bool:
    return is_nothing(plain_of(n, tuple(0 if i % (n + 1) == 0 else e for i, e in enumerate(table))))


def blind(state: DState) -> bool:
    """Every sum around three different terms, both ways round, zero: no filling tells the result."""
    n = state.n
    table = excess_table(state)
    return all(
        around(n, table, x, y, z) == 0 and around(n, table, x, z, y) == 0
        for x, y, z in combinations(range(n), 3)
    )


def blind_by_description(state: DState) -> bool:
    """Blind, read from what it forces on the two-way sums, and the sums around one way round."""
    n = state.n
    if n <= 2:
        return True
    table = excess_table(state)
    s = {(x, y): two_way(n, table, x, y) for x in range(n) for y in range(x + 1, n)}
    one_way = all(around(n, table, x, y, z) == 0 for x, y, z in combinations(range(n), 3))
    if n == 3:
        return one_way and s[(0, 1)] + s[(1, 2)] + s[(0, 2)] == 0
    if n == 4:
        splits = s[(0, 1)] == s[(2, 3)] and s[(0, 2)] == s[(1, 3)] and s[(0, 3)] == s[(1, 2)]
        return one_way and splits and s[(0, 1)] + s[(0, 2)] + s[(0, 3)] == 0
    return one_way and all(v == 0 for v in s.values())


def why_not_told(fs: FState) -> str:
    """Why a result is not told: it asserts nothing, nothing is filled, it differs from nothing only at loops, it
    is blind, or its sums around are not zero only off the filled triples.  `told` for a told result."""
    if told(fs):
        return "told"
    n = fs.n
    table = excess_table(fs.state)
    if is_nothing(fs.state):
        return "the result asserting nothing"
    if not fs.filled:
        return "nothing filled"
    if _without_loops_nothing(n, table):
        return "differs from nothing only at loops"
    if blind(fs.state):
        return "blind: every sum around zero both ways round"
    return "a sum around not zero only off the filled triples"


def restrict(state: DState, terms: Sequence[int]) -> DState:
    """The state read on some of its terms alone (their assertions among themselves), terms renumbered in order."""
    n = state.n
    k = len(terms)
    r = tuple(state.r[terms[i] * n + terms[j]] for i in range(k) for j in range(k))
    s = tuple(state.s[terms[i] * n + terms[j]] for i in range(k) for j in range(k))
    return DState(k, r, s)


def keeping_sets(state: DState) -> tuple[tuple[int, ...], ...]:
    """The least sets of terms keeping the result from being the one asserting nothing, read from its sums."""
    n = state.n
    table = excess_table(state)
    loop = [table[x * n + x] != 0 for x in range(n)]
    out: list[tuple[int, ...]] = [(x,) for x in range(n) if loop[x]]
    pairs = {(x, y) for x in range(n) for y in range(x + 1, n) if two_way(n, table, x, y) != 0}
    out += [(x, y) for x, y in sorted(pairs) if not loop[x] and not loop[y]]
    for x, y, z in combinations(range(n), 3):
        if loop[x] or loop[y] or loop[z] or {(x, y), (x, z), (y, z)} & pairs:
            continue
        if around(n, table, x, y, z) != 0:
            out.append((x, y, z))
    return tuple(out)


def keeping_sets_by_restriction(state: DState, most: int | None = None) -> tuple[tuple[int, ...], ...]:
    """The same sets found by reading the result on every set of terms (up to `most` terms) and keeping the
    least ones whose reading is not the result asserting nothing."""
    n = state.n
    top = n if most is None else min(n, most)
    found: list[tuple[int, ...]] = []
    for k in range(1, top + 1):
        for terms in combinations(range(n), k):
            if any(set(f) <= set(terms) for f in found):
                continue
            if not is_nothing(restrict(state, terms)):
                found.append(terms)
    return tuple(found)


def rank(rows: Sequence[Sequence[int]]) -> int:
    """The rank of whole-number rows over the fractions (exact)."""
    m = [[Fraction(v) for v in row] for row in rows]
    r = 0
    width = len(m[0]) if m else 0
    for c in range(width):
        pivot = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if pivot is None:
            continue
        m[r], m[pivot] = m[pivot], m[r]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                factor = m[i][c] / m[r][c]
                m[i] = [a - factor * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


def antisymmetric_rows(n: int, triples: Iterable[Triple]) -> list[list[int]]:
    """The sums around the triples, read on excesses with every two-way sum zero (one value per pair `x < y`)."""
    pairs = [(x, y) for x in range(n) for y in range(x + 1, n)]
    index = {p: i for i, p in enumerate(pairs)}
    rows: list[list[int]] = []
    for x, y, z in triples:
        row = [0] * len(pairs)
        for a, b in ((x, y), (y, z), (z, x)):
            if a < b:
                row[index[(a, b)]] += 1
            else:
                row[index[(b, a)]] -= 1
        rows.append(row)
    return rows


def decides(n: int, triples: Iterable[Triple]) -> bool:
    """With every loop and two-way sum zero, does balancing these triples force the result asserting nothing?"""
    rows = antisymmetric_rows(n, triples)
    need = comb(n - 1, 2)
    return need == 0 or (bool(rows) and rank(rows) == need)


def _nullspace(rows: list[list[int]], width: int) -> list[list[Fraction]]:
    m = [[Fraction(v) for v in row] for row in rows]
    pivots: list[int] = []
    r = 0
    for c in range(width):
        pivot = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if pivot is None:
            continue
        m[r], m[pivot] = m[pivot], m[r]
        lead = m[r][c]
        m[r] = [v / lead for v in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                factor = m[i][c]
                m[i] = [a - factor * b for a, b in zip(m[i], m[r])]
        pivots.append(c)
        r += 1
    basis: list[list[Fraction]] = []
    for free in (c for c in range(width) if c not in pivots):
        vec = [Fraction(0)] * width
        vec[free] = Fraction(1)
        for i, c in enumerate(pivots):
            vec[c] = -m[i][free]
        basis.append(vec)
    return basis


def undecided_witness(n: int, triples: Sequence[Triple]) -> Table | None:
    """A whole-number excess table with every loop and two-way sum zero, balancing every triple given, that is not
    the result asserting nothing; `None` when there is none (the triples decide)."""
    pairs = [(x, y) for x in range(n) for y in range(x + 1, n)]
    all_rows = antisymmetric_rows(n, combinations(range(n), 3))
    for vec in _nullspace(antisymmetric_rows(n, triples), len(pairs)):
        if all(sum(a * v for a, v in zip(row, vec)) == 0 for row in all_rows):
            continue  # every sum around zero: the result asserting nothing
        scale = 1
        for v in vec:
            scale = scale * v.denominator // _gcd(scale, v.denominator)
        table = [0] * (n * n)
        for (x, y), v in zip(pairs, vec):
            table[x * n + y] = int(v * scale)
            table[y * n + x] = -int(v * scale)
        return tuple(table)
    return None


def _gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a
