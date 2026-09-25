"""The unchosen readings of filling and balance, explored at a small bound.

Each reading changes one choice of the paper's §3 (`Reading`):

* C-F2: filling leaves the state as it was (`fill_changes_state=False`) — then
  every result is a twenty-third result, at the twenty-third's round;
* C-O2 / C-O3: three terms filled as a set, balancing both ways round / either
  way round; C-O4: every starting term a different filled triple;
* C-B2: going from `x` to `y` counts the assertions between them either way —
  a triple balances when its three two-way sums add up to zero;
* C-M2: fillings counted, like a multiplicity;
* C-I2: identifying drops every filled triple naming either term; C-I3: it keeps
  the triples left without three different terms;
* fillings attempted last.

`explore_reading` is written independently of `twentyfifth.explore` (it keeps
triples as plain tuples and writes them per reading), so run with the chosen
reading it is a second computation of the chosen exploration.

Derived (paper, D14)
    Under every reading but C-I3 the round of a result is the twenty-third's
    cost of its assertions plus its filled triples (counted under C-M2): a
    change raises that by at most one, and additions then fillings reach it.
    Under C-I2 and with fillings last the results and rounds are the chosen
    reading's; under C-F2 they are the twenty-third's.  Under C-I3 a triple
    left without three different terms is never lost and cannot be filled
    directly, so the cost formula fails and a result with a filled triple never
    reaches one with none (`i3_reach_failures`).
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass
from itertools import combinations, permutations

from fourth.state import _rewritings
from ninth.changes import Change, Kind
from ninth.changes import changes as changes_of_state
from ninth.changes import perform as perform_on_state
from xry.changes import identification_map

from twentythird.cost import cost as cost23
from twentythird.state import DState, Table, around, empty, excess_table, normal_table, plain, two_way

__all__ = [
    "CHOSEN",
    "READINGS",
    "Reading",
    "ReadingRun",
    "balances_under",
    "explore_reading",
    "i3_reach_failures",
]

Trip = tuple[int, int, int]
RState = tuple[DState, tuple[Trip, ...]]
RMark = tuple[int, Table, tuple[Trip, ...]]


@dataclass(frozen=True)
class Reading:
    """One reading of filling and balance."""

    name: str
    way_round: str = "cyclic"
    along: str = "direction"
    counted: bool = False
    identify: str = "carry"
    fills_last: bool = False
    fill_changes_state: bool = True


CHOSEN = Reading("chosen (C-F1, C-O1, C-B1, C-M1, C-I1)")
READINGS: tuple[Reading, ...] = (
    CHOSEN,
    Reading("C-F2: filling changes nothing", fill_changes_state=False),
    Reading("C-O2: a set, balancing both ways round", way_round="set-both"),
    Reading("C-O3: a set, balancing either way round", way_round="set-either"),
    Reading("C-O4: every starting term another triple", way_round="ordered"),
    Reading("C-B2: the assertions between two terms either way", along="either"),
    Reading("C-M2: fillings counted", counted=True),
    Reading("C-I2: identifying drops the triples naming either term", identify="drop"),
    Reading("C-I3: identifying keeps the triples left without three different terms", identify="keep"),
    Reading("fillings attempted last", fills_last=True),
)


def _write(reading: Reading, t: Trip) -> Trip:
    """A triple written the reading's way: from where it starts, as a set, or as it is."""
    if reading.way_round in ("set-both", "set-either"):
        a, b, c = sorted(t)
        return (a, b, c)
    if reading.way_round == "ordered":
        return t
    x, y, z = t
    return min((x, y, z), (y, z, x), (z, x, y))


def _fillable(reading: Reading, n: int) -> list[Trip]:
    if reading.way_round in ("set-both", "set-either"):
        return [(x, y, z) for x, y, z in combinations(range(n), 3)]
    if reading.way_round == "ordered":
        return [(x, y, z) for x, y, z in permutations(range(n), 3)]
    out: list[Trip] = []
    for x, y, z in combinations(range(n), 3):
        out += [(x, y, z), (x, z, y)]
    return out


def balances_under(reading: Reading, state: DState, t: Trip) -> bool:
    """Does the filled triple `t` balance under the reading?"""
    n = state.n
    table = excess_table(state)
    x, y, z = t
    if reading.along == "either":
        return two_way(n, table, x, y) + two_way(n, table, y, z) + two_way(n, table, z, x) == 0
    one = around(n, table, x, y, z) == 0
    other = around(n, table, x, z, y) == 0
    if reading.way_round == "set-both":
        return one and other
    if reading.way_round == "set-either":
        return one or other
    return one


def _carry(reading: Reading, n: int, filled: tuple[Trip, ...], u: int, v: int) -> tuple[Trip, ...]:
    q = identification_map(n, u, v)
    out: list[Trip] = []
    for x, y, z in filled:
        if reading.identify == "drop" and {x, y, z} & {u, v}:
            continue
        a, b, c = q[x], q[y], q[z]
        if reading.identify == "carry" and len({a, b, c}) < 3:
            continue
        out.append(_write(reading, (a, b, c)))
    if not reading.counted:
        out = sorted(set(out))
    return tuple(sorted(out))


def _changes(reading: Reading, rs: RState) -> Iterator[Change | Trip]:
    state, filled = rs
    four = changes_of_state(state)
    first = [c for c in four if c.kind in (Kind.IDENTIFY, Kind.REMOVE)]
    rest = [c for c in four if c.kind not in (Kind.IDENTIFY, Kind.REMOVE)]
    fills = [t for t in _fillable(reading, state.n) if reading.counted or t not in filled]
    ordered: list[Change | Trip] = [*first, *rest, *fills] if reading.fills_last else [*first, *fills, *rest]
    yield from ordered


def _perform(reading: Reading, rs: RState, change: Change | Trip) -> RState:
    state, filled = rs
    if isinstance(change, tuple):
        if not reading.fill_changes_state:
            return rs
        return state, tuple(sorted((*filled, _write(reading, change))))
    out = perform_on_state(state, change)
    if change.kind is Kind.IDENTIFY:
        return out, _carry(reading, state.n, filled, change.x, change.y)
    return out, filled


def _moved(reading: Reading, filled: tuple[Trip, ...], p: tuple[int, ...]) -> tuple[Trip, ...]:
    return tuple(sorted(_write(reading, (p[x], p[y], p[z])) for x, y, z in filled))


def _canonical(reading: Reading, rs: RState) -> RState:
    state, filled = rs
    state = plain(state)
    n = state.n
    best: tuple[tuple[int, ...], tuple[int, ...], tuple[Trip, ...]] | None = None
    for p, index in _rewritings(n):
        r = [0] * (n * n)
        s = [0] * (n * n)
        for i, k in enumerate(state.r):
            r[index[i]] = k
        for i, k in enumerate(state.s):
            s[index[i]] = k
        cand = (tuple(r), tuple(s), _moved(reading, filled, p))
        if best is None or cand < best:
            best = cand
    assert best is not None
    return DState(n, best[0], best[1]), best[2]


def _mark(reading: Reading, rs: RState) -> RMark:
    state, filled = rs
    n = state.n
    table = excess_table(state)
    best: tuple[Table, tuple[Trip, ...]] | None = None
    for p, index in _rewritings(n):
        moved = [0] * (n * n)
        for i, e in enumerate(table):
            moved[index[i]] = e
        cand = (normal_table(n, tuple(moved)), _moved(reading, filled, p))
        if best is None or cand < best:
            best = cand
    assert best is not None
    return (n, best[0], best[1])


@dataclass
class ReadingRun:
    """One reading explored: the states reached, the results formed, their rounds and first states."""

    reading: Reading
    bound: int
    rounds: int
    depth: dict[RState, int]
    round_of: dict[RMark, int]
    first: dict[RMark, RState]

    def cost(self, mark: RMark) -> int:
        """The twenty-third's cost of the result's assertions plus its filled triples (counted)."""
        state, filled = self.first[mark]
        return cost23(state) + len(filled)

    def per_round(self) -> list[int]:
        """New results in each round."""
        return [sum(1 for r in self.round_of.values() if r == k) for k in range(self.rounds + 1)]

    def told(self, mark: RMark) -> bool:
        """Does some filled triple of the result not balance under the reading?"""
        state, filled = self.first[mark]
        return any(not balances_under(self.reading, state, t) for t in filled)


def explore_reading(reading: Reading, bound: int, rounds: int) -> ReadingRun:
    """The states reached from the empty state under the reading, and the results formed afterwards."""
    root: RState = (empty(), ())
    depth = {root: 0}
    wave = [root]
    for r in range(1, rounds + 1):
        found: list[RState] = []
        for rs in wave:
            for change in _changes(reading, rs):
                raw = _perform(reading, rs, change)
                if raw[0].n > bound:
                    continue
                out = _canonical(reading, raw)
                if out not in depth:
                    depth[out] = r
                    found.append(out)
        wave = sorted(found, key=lambda s: (s[0].n, s[0].r, s[0].s, s[1]))
    round_of: dict[RMark, int] = {}
    first: dict[RMark, RState] = {}
    for rs in sorted(depth, key=lambda s: (depth[s], s[0].n, s[0].r, s[0].s, s[1])):
        m = _mark(reading, rs)
        if m not in round_of:
            round_of[m] = depth[rs]
            first[m] = rs
    return ReadingRun(reading, bound, rounds, depth, round_of, first)


def i3_reach_failures(run: ReadingRun) -> tuple[int, int]:
    """Under C-I3, from every result with a filled triple: how many such results reach a result with none (along
    the explored states), and how many there are."""
    graph: dict[RState, list[RState]] = {}
    for rs in run.depth:
        outs: list[RState] = []
        for change in _changes(run.reading, rs):
            raw = _perform(run.reading, rs, change)
            if raw[0].n > run.bound:
                continue
            out = _canonical(run.reading, raw)
            if out in run.depth:
                outs.append(out)
        graph[rs] = outs
    filled_results = [m for m in run.round_of if m[2]]
    reaching = 0
    for m in filled_results:
        seen = {run.first[m]}
        todo = [run.first[m]]
        while todo:
            cur = todo.pop()
            for nxt in graph[cur]:
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
        if any(not s[1] for s in seen):
            reaching += 1
    return reaching, len(filled_results)
