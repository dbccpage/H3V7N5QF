"""Reachability between results under the twenty-fourth seed, for each reading of identifying.

Chosen here (reading C-E, the twenty-third's)
    A result reaches another when some state of the first reaches, by changes
    performed on states, some state of the second.

Derived (paper, D12; `lean4_core/Twentyfourth/Reach.lean`)
    * Under C-I1 (the one term of an identification is filled when either
      was) a filled term never goes away: no change turns a state with a
      filled term into one without.  A result reaches another exactly when
      the other has a term or the first is empty, *and* the other has a filled
      term or the first has none (`reachable`).  The twenty-third's criterion
      (23:D12) fails exactly on the pairs from a result with a filled term to
      one without.
    * Under C-I2 and C-I3 a filled term can be merged away (with an unfilled
      term, or always), and the twenty-third's criterion holds.
    The path — remove every assertion, identify the terms down to one, add
    terms, fill, add the assertions of a state asserting the fewest — never has
    more terms, or a larger cost, than the larger of its two ends, except that
    under C-I2 and C-I3 unfilling one term takes a second term; a search among
    the states of one exploration decides every pair within its bound.
"""

from __future__ import annotations

from twentyfourth.changes import ID_EITHER, Reading, moves, perform24
from twentyfourth.explore import Grouped
from twentyfourth.state import FState, Key24, result_key

__all__ = ["reachable", "reached_by_search", "search_graph"]


def reachable(s: FState, t: FState, reading: Reading) -> bool:
    """Does the result of `s` reach the result of `t` under `reading`?"""
    terms = t.n >= 1 or s.n == 0
    if reading.identify == ID_EITHER:
        return terms and (t.filled_count >= 1 or s.filled_count == 0)
    return terms


def search_graph(grouped: Grouped) -> dict[FState, tuple[FState, ...]]:
    """The explored states one change away from each explored state (every change performed, any round)."""
    expl = grouped.states
    edges: dict[FState, set[FState]] = {s: set() for s in expl.depth}
    for state in expl.depth:
        for change in moves(state, expl.reading):
            raw = perform24(state, change, expl.reading)
            if raw.n <= expl.bound:
                out = expl.keep(raw)
                if out in expl.depth:
                    edges[state].add(out)
    return {s: tuple(sorted(v, key=lambda x: x.key())) for s, v in edges.items()}


def reached_by_search(grouped: Grouped, graph: dict[FState, tuple[FState, ...]], key: Key24) -> set[Key24]:
    """The results reached from any state of the result `key`, along the explored states, itself included."""
    seen: set[FState] = set()
    todo = [m for m in grouped.members[key]]
    seen.update(todo)
    while todo:
        cur = todo.pop()
        for nxt in graph[cur]:
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return {result_key(s) for s in seen}
