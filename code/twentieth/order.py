"""The round is the number of changes, not the number of additions.

Every performed change counts one, so the set of results first reached at
each round does not depend on the order of attempts inside a round. The
base already explores that way. "Fewest additions first" only lists the
changes inside a result. Additions (terms and assertions added to what is
given) are a different ranking.
"""

from __future__ import annotations

from xry.changes import changes, obstruction, perform
from xry.explore import order
from xry.state import State, added, canonical


def _bfs(start: State, bound: int, rounds: int, by_additions: bool) -> dict[State, int]:
    """One change per round. `by_additions` only reorders the attempts inside a state."""
    if not start.legal:
        raise ValueError("what is given asserts no xrx")
    if start.n > bound:
        raise ValueError("the bound is below what is given")
    root = canonical(start)
    depth = {root: 0}
    wave = [root]
    for rnd in range(1, rounds + 1):
        found: list[State] = []
        for state in sorted(wave, key=order):
            pending = list(changes(state))
            if by_additions:
                pending.sort(key=lambda change: (change.additions, change.kind.value, change.x, change.y))
            for change in pending:
                if obstruction(state, change):
                    continue
                out = perform(state, change)
                if out.n > bound:
                    continue
                out = canonical(out)
                if out not in depth:
                    depth[out] = rnd
                    found.append(out)
        wave = found
        if not wave:
            break
    return depth


def frontiers(depth: dict[State, int], bound: int) -> frozenset[State]:
    """Results at the term bound: adding a term would leave it."""
    return frozenset(state for state in depth if state.n == bound)


def rankings_differ(depth: dict[State, int]) -> tuple[State, State] | None:
    """Two results where fewer additions is the later round, if there are any."""
    ranked = sorted(depth, key=lambda state: (sum(added(state)), depth[state], order(state)))
    for earlier in ranked:
        for later in ranked:
            if sum(added(earlier)) < sum(added(later)) and depth[earlier] > depth[later]:
                return earlier, later
    return None


def _expand_capped(start: State, bound: int, expansions: int, by_additions: bool) -> dict[State, int]:
    """Expand reached results one at a time, at most `expansions` of them.

    `by_additions` ranks the pending results by the additions they record
    (O2); otherwise by the round they were reached at (O1, breadth first).
    The value is the number of changes along the path that found the result.
    """
    if not start.legal:
        raise ValueError("what is given asserts no xrx")
    if start.n > bound:
        raise ValueError("the bound is below what is given")
    root = canonical(start)
    depth = {root: 0}
    pending = [root]
    expanded = 0
    while pending and expanded < expansions:
        if by_additions:
            pending.sort(key=lambda state: (sum(added(state)), depth[state], order(state)))
        else:
            pending.sort(key=lambda state: (depth[state], order(state)))
        state = pending.pop(0)
        expanded += 1
        for change in changes(state):
            if obstruction(state, change):
                continue
            out = perform(state, change)
            if out.n > bound:
                continue
            out = canonical(out)
            if out not in depth:
                depth[out] = depth[state] + 1
                pending.append(out)
    return depth


def additions_priority(start: State, bound: int, expansions: int) -> dict[State, int]:
    """Expand reached results fewest additions first, for `expansions` expansions.

    Unchosen reading of the base sentence: the additions rank the results
    globally, instead of listing the attempts inside one round.
    """
    return _expand_capped(start, bound, expansions, True)


def changes_priority(start: State, bound: int, expansions: int) -> dict[State, int]:
    """The chosen reading with the same cap: expand reached results round by round."""
    return _expand_capped(start, bound, expansions, False)
