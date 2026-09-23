"""Reachability between results under the sixteenth seed: the mass is carried, never lost.

Derived (paper; the necessity in `lean4/Sixteenth/Reach.lean`)
    Along one change the mass of a pair (both multiplicities plus the
    record) is kept by a removal and by an admission, raised by a direct
    addition, and, on an identification, added up over the pairs that become
    one pair.  A term is never lost except by merging into another.  So a
    sequence of changes from `s` to `t` induces a map of the terms of `s`
    into the terms of `t` under which every pair of `t` receives at most its
    own mass (`carries`); conversely such a map is realised by identifying
    the terms it merges, adding the terms it misses, and then, pair by pair,
    removing every assertion, adding the missing mass directly, removing it,
    and admitting the wanted multiplicities.  Hence

        `t` is reachable from `s` exactly when `s` is empty or some map of
        the terms of `s` into the terms of `t` carries the mass,

    the criterion of this seed.  Its computed form is checked against
    breadth-first search along the changes on every ordered pair of results
    within a small bound (`sixteenth.evidence`).  Necessity of the mass
    (both totals plus the record) is `Reach16.mass_le`.  The diagonal mass
    is computed only (ledger O4; there is no `Reach16.diag_le`).  Sufficiency
    of the carrying criterion is computed (ledger O3); Lean has it from the
    empty state (`reach16_by_additions`) and by admitting every leftover
    (`reach16_admit_all`), not for an arbitrary carrying map.

Cited from the ninth derivation (`ninth.reach`) and re-checked
    The ninth's criterion (a term decides) does not survive: the one-term
    state asserting `ara` once reaches the one-term state asserting nothing
    under the ninth seed and not here, since its mass would fall.  It is
    imported as `reachable_ninth` for the comparison on the state parts:
    wherever the sixteenth's criterion says yes, so does the ninth's (the
    mass condition only refuses), and the pairs the ninth admits and the
    sixteenth refuses are counted.  `reach_graph` and `reachable_in_graph`
    are written again for states with a record.
"""

from __future__ import annotations

from itertools import product

from ninth.reach import reachable as reachable_ninth_state

from sixteenth.changes import changes16, perform16
from sixteenth.explore import Exploration16, order16
from sixteenth.state import RState, canonical16

__all__ = [
    "carries",
    "carrying_maps",
    "mass_ok",
    "mutual16",
    "reach_graph16",
    "reachable16",
    "reachable_by_search16",
    "reachable_in_graph16",
    "reachable_ninth",
]


def mass_ok(s: RState, t: RState) -> bool:
    """The two necessary conditions: neither the mass nor the diagonal mass falls from `s` to `t`."""
    return t.mass >= s.mass and t.diagonal_mass >= s.diagonal_mass


def carrying_maps(s: RState, t: RState) -> list[tuple[int, ...]]:
    """Every map of the terms of `s` into the terms of `t` under which each pair of `t` receives at most its mass."""
    if s.n == 0:
        return [()]
    found: list[tuple[int, ...]] = []
    for f in product(range(t.n), repeat=s.n):
        carried = [0] * (t.n * t.n)
        for x in range(s.n):
            for y in range(s.n):
                carried[f[x] * t.n + f[y]] += s.pair_mass(x, y)
        if all(carried[u * t.n + v] <= t.pair_mass(u, v) for u in range(t.n) for v in range(t.n)):
            found.append(f)
    return found


def carries(s: RState, t: RState) -> bool:
    """Is `s` empty, or is there a map of its terms into those of `t` carrying the mass?"""
    return bool(carrying_maps(s, t))


def reachable16(s: RState, t: RState) -> bool:
    """Is `t` reachable from `s` by changes of the sixteenth seed?  The criterion: `carries`."""
    return carries(s, t)


def reachable_ninth(s: RState, t: RState) -> bool:
    """The ninth's criterion on the state parts: `t` has a term, or `s` is empty."""
    return reachable_ninth_state(s.state, t.state)


def mutual16(s: RState, t: RState) -> bool:
    """Do `s` and `t` reach each other?"""
    return reachable16(s, t) and reachable16(t, s)


def reachable_by_search16(s: RState, bound: int, rounds: int) -> set[RState]:
    """Every result (least writing) reached from `s` within `bound` terms and `rounds` changes."""
    root = canonical16(s)
    seen = {root}
    wave = [root]
    for _ in range(rounds):
        found = []
        for rs in wave:
            for change in changes16(rs):
                out = perform16(rs, change)
                if out.n > bound:
                    continue
                out = canonical16(out)
                if out not in seen:
                    seen.add(out)
                    found.append(out)
        wave = found
    return seen


def reach_graph16(expl: Exploration16) -> dict[RState, tuple[RState, ...]]:
    """The changes among the results of `expl`, as a graph; outcomes outside it are dropped."""
    inside = expl.depth
    graph: dict[RState, tuple[RState, ...]] = {}
    for rs in sorted(inside, key=order16):
        outs: list[RState] = []
        for change in changes16(rs):
            out = perform16(rs, change, expl.reading)
            if out.n > expl.bound:
                continue
            out = canonical16(out)
            if out in inside and out not in outs:
                outs.append(out)
        graph[rs] = tuple(outs)
    return graph


def reachable_in_graph16(graph: dict[RState, tuple[RState, ...]], s: RState) -> set[RState]:
    """Every node of `graph` reached from `s` along its edges (`s` included)."""
    seen = {s}
    wave = [s]
    while wave:
        found = []
        for rs in wave:
            for out in graph[rs]:
                if out not in seen:
                    seen.add(out)
                    found.append(out)
        wave = found
    return seen
