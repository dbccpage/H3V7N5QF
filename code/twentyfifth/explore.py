"""Changes performed on states, the results formed afterwards (the twenty-third's reading C-E, with fillings).

Given by the seed
    Attempt every change, fewest additions first; 100 changes along each
    alternative, earlier changes on every alternative before later ones; a
    finite bound, the exact frontier, and what is complete within it.  The
    task: "Explore by performing changes on states, as the twenty-third's
    exploration does, and form the results afterwards."

Cited from the twenty-third derivation (`twentythird.explore`) and re-checked
    Its exploration runs the twenty-second's: every change of every state
    reached — each state a plain state (no pair asserted in both relations)
    in its least writing — round by round, bounded in terms and rounds, the
    states grouped afterwards into results.  It knows no filled triple, so it
    is written again here with the filled triples carried and the fifth kind
    attempted (`explore`); with at most two terms nothing can be filled and it
    is the twenty-third's (compared in `twentyfifth.evidence`).

Derived (paper, D5 and K2)
    The round of a state reached is its `phi` plus its filled triples: a
    change raises that by at most one, and additions then fillings reach it.
    A state of a result asserting the fewest is plain, so every result with
    at most `N` terms and cost at most `R` is formed, at the round of its
    cost, and its states reached in that round (`fewest_members`) are its
    states asserting the fewest with its filled triples.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from twentyfifth.state import Change25, FState, Filling, Mark, canonical_state, changes, empty25, is_addition
from twentyfifth.state import perform, plain_state, result_mark

__all__ = [
    "Attempt",
    "Exploration",
    "Grouped",
    "explore",
    "explore_states",
    "group",
    "order",
    "performed",
    "shortest_sequences",
]


def order(fs: FState) -> tuple[int, tuple[int, ...], tuple[int, ...], tuple[tuple[int, int, int], ...]]:
    """A fixed order on states, for reproducible output."""
    return (fs.n, fs.state.r, fs.state.s, fs.filled)


@dataclass(frozen=True)
class Attempt:
    """One attempted change: the state, the change, the state it reaches, and that state as explored."""

    state: FState
    change: Change25
    raw: FState
    outcome: FState | None
    beyond: bool


@dataclass
class Exploration:
    """Everything recorded by `explore_states`."""

    bound: int
    rounds: int
    depth: dict[FState, int]
    new_per_round: list[int]
    frontier: list[tuple[FState, Change25]] = field(default_factory=list)
    log: list[Attempt] = field(default_factory=list)


def explore_states(bound: int, rounds: int, keep_log: bool = False) -> Exploration:
    """The states reached from the empty state, round by round, within `bound` terms and `rounds` rounds."""
    if bound < 1:
        raise ValueError("the bound admits at least one term")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")
    root = empty25()
    depth = {root: 0}
    wave = [root]
    new_per_round = [1]
    frontier: list[tuple[FState, Change25]] = []
    log: list[Attempt] = []
    for r in range(1, rounds + 1):
        found: list[FState] = []
        for state in wave:
            for change in changes(state):
                raw = perform(state, change)
                if raw.n > bound:
                    frontier.append((state, change))
                    if keep_log:
                        log.append(Attempt(state, change, raw, None, True))
                    continue
                out = canonical_state(plain_state(raw))
                if out not in depth:
                    depth[out] = r
                    found.append(out)
                if keep_log:
                    log.append(Attempt(state, change, raw, out, False))
        wave = sorted(found, key=order)
        new_per_round.append(len(wave))
    return Exploration(bound, rounds, depth, new_per_round, frontier, log)


@dataclass
class Grouped:
    """The exploration of states, and the results formed from it."""

    states: Exploration
    round_of: dict[Mark, int]
    members: dict[Mark, tuple[FState, ...]]

    def fewest_members(self, mark: Mark) -> tuple[FState, ...]:
        """The states of the result reached in its round: those asserting the fewest (up to writing)."""
        r = self.round_of[mark]
        return tuple(m for m in self.members[mark] if self.states.depth[m] == r)

    def representative(self, mark: Mark) -> FState:
        """The result's first state reached."""
        return self.members[mark][0]

    def ordered_marks(self) -> list[Mark]:
        """The results in round order, then by their representative."""
        return sorted(self.round_of, key=lambda k: (self.round_of[k], order(self.representative(k))))

    @property
    def bound(self) -> int:
        """The bound on terms."""
        return self.states.bound

    @property
    def rounds(self) -> int:
        """The bound on rounds."""
        return self.states.rounds


def group(states: Exploration) -> Grouped:
    """Form the results from the states an exploration reached."""
    lists: dict[Mark, list[FState]] = {}
    for fs in sorted(states.depth, key=lambda s: (states.depth[s], order(s))):
        lists.setdefault(result_mark(fs), []).append(fs)
    members = {k: tuple(v) for k, v in lists.items()}
    round_of = {k: states.depth[v[0]] for k, v in members.items()}
    return Grouped(states, round_of, members)


def explore(bound: int, rounds: int, keep_log: bool = False) -> Grouped:
    """The exploration of states from the empty state, then the results formed."""
    return group(explore_states(bound, rounds, keep_log))


def performed(expl: Exploration) -> list[tuple[FState, Change25, FState, FState]]:
    """Every change within the bound of every state whose changes were attempted: the state, the change, the
    outcome, and the outcome as explored (plain, least writing)."""
    out: list[tuple[FState, Change25, FState, FState]] = []
    for fs in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        if expl.depth[fs] >= expl.rounds:
            continue
        for change in changes(fs):
            raw = perform(fs, change)
            if raw.n <= expl.bound:
                out.append((fs, change, raw, canonical_state(plain_state(raw))))
    return out


def shortest_sequences(grouped: Grouped) -> dict[Mark, int]:
    """Shortest sequences of changes to each result: counted along additions and fillings that raise the round
    by one, on the explored states, then added over the result's states asserting the fewest."""
    expl = grouped.states
    counts = {fs: 0 for fs in expl.depth}
    counts[empty25()] = 1
    for fs, change, _, out in performed(expl):
        raises = isinstance(change, Filling) or is_addition(change)
        if raises and out in expl.depth and expl.depth[out] == expl.depth[fs] + 1:
            counts[out] += counts[fs]
    return {k: sum(counts[m] for m in grouped.fewest_members(k)) for k in grouped.round_of}
