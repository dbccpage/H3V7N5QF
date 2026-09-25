"""Changes performed on states, round by round, from the empty state; the results formed afterwards.

Given by the seed
    Attempt every change, fewest additions first; 100 changes along each
    alternative, earlier changes on every alternative before later ones; a
    finite bound, the exact frontier, and what is complete within it.  The
    task: "Explore by performing changes on states, as the twenty-third's
    exploration does, and form the results afterwards."

Cited from the twenty-third derivation (`twentythird.explore`) and re-checked
    Its exploration is the twenty-second's: every change performed on every
    state reached, a state kept as its plain state at its least writing,
    bounded in terms and rounds, the frontier the attempts leaving the bound on
    terms; the results formed afterwards, the round of a result the first round
    in which one of its states is reached (reading C-E).  Written again here
    for states with filled terms (a fifth kind of change, and the filled
    terms carried by the least writing): re-proved, and compared with the
    twenty-third's own run on the results with no filled term
    (`twentyfourth.embed`).

Chosen here (reading C-E′, unchosen, computed at a small bound)
    `plain_states=False` keeps every state at its least writing instead of its
    plain state: the ninth's exploration of states, with filled terms.

Derived (paper, D5, K2)
    The round of a state is the twenty-second's `phi` (terms plus the plain
    state's assertions) plus its filled terms; the round of a result is its
    cost, and the states of it reached in that round are exactly its states
    asserting the fewest.  A shortest sequence adds terms, adds assertions and
    fills, and never has more terms than its end: the counts are exact within
    the bound.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field

from twentyfourth.changes import CHOSEN, Move, Reading, is_raising, moves, perform24
from twentyfourth.state import FState, Key24, canonical, empty, result_key, state_of

__all__ = [
    "Attempt",
    "Exit",
    "Exploration",
    "Grouped",
    "explore",
    "explore_states",
    "group",
    "order",
    "performed",
    "shortest_sequences",
]


def order(state: FState) -> tuple[int, tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    """A fixed order on states, for reproducible output."""
    return (state.n, state.fills, state.base.r, state.base.s)


@dataclass(frozen=True)
class Attempt:
    """One attempted change: the state, the change, the state reached and the state kept (`None` beyond)."""

    state: FState
    change: Move
    raw: FState
    outcome: FState | None
    beyond: bool


@dataclass(frozen=True)
class Exit:
    """A frontier entry: an attempt that leaves the bound on terms (always "add a term")."""

    state: FState
    change: Move


@dataclass
class Exploration:
    """Everything recorded by `explore_states`."""

    reading: Reading
    plain_states: bool
    bound: int
    rounds: int
    depth: dict[FState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    frontier: list[Exit] = field(default_factory=list)
    log: list[Attempt] = field(default_factory=list)

    def keep(self, state: FState) -> FState:
        """The state kept for `state`: plain or not, at its least writing."""
        return state_of(state) if self.plain_states else canonical(state)


def explore_states(
    bound: int,
    rounds: int,
    reading: Reading = CHOSEN,
    plain_states: bool = True,
    keep_log: bool = False,
) -> Exploration:
    """Every state reached from the empty state within `bound` terms and `rounds` rounds."""
    if bound < 1:
        raise ValueError("the bound admits at least one term")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")
    expl = Exploration(reading, plain_states, bound, rounds, {}, [1], [0])
    root = empty()
    expl.depth[root] = 0
    wave = [root]
    known = 0
    for r in range(1, rounds + 1):
        found: list[FState] = []
        for state in wave:
            for change in moves(state, reading):
                raw = perform24(state, change, reading)
                known += 1
                if raw.n > bound:
                    expl.frontier.append(Exit(state, change))
                    if keep_log:
                        expl.log.append(Attempt(state, change, raw, None, True))
                    continue
                out = expl.keep(raw)
                if out not in expl.depth:
                    expl.depth[out] = r
                    found.append(out)
                if keep_log:
                    expl.log.append(Attempt(state, change, raw, out, False))
        expl.attempts_per_round.append(known)
        wave = sorted(found, key=order)
        expl.new_per_round.append(len(wave))
    return expl


def performed(expl: Exploration) -> Iterator[tuple[FState, Move, FState, FState]]:
    """Every change within the bound on every state whose changes were attempted.

    Yields the state, the change, the state reached, and the state kept.
    """
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        if expl.depth[state] >= expl.rounds:
            continue
        for change in moves(state, expl.reading):
            raw = perform24(state, change, expl.reading)
            if raw.n > expl.bound:
                continue
            yield state, change, raw, expl.keep(raw)


@dataclass
class Grouped:
    """An exploration of states, and this seed's results formed from it."""

    states: Exploration
    round_of: dict[Key24, int]
    members: dict[Key24, tuple[FState, ...]]

    def fewest_members(self, key: Key24) -> tuple[FState, ...]:
        """The states of the result reached in its round: those asserting the fewest (up to writing)."""
        r = self.round_of[key]
        return tuple(m for m in self.members[key] if self.states.depth[m] == r)

    def representative(self, key: Key24) -> FState:
        """The result's first state reached."""
        return self.members[key][0]

    def ordered_keys(self) -> list[Key24]:
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


def group(expl: Exploration) -> Grouped:
    """Form the results from the states an exploration reached."""
    lists: dict[Key24, list[FState]] = {}
    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        lists.setdefault(result_key(state), []).append(state)
    members = {k: tuple(v) for k, v in lists.items()}
    round_of = {k: expl.depth[v[0]] for k, v in members.items()}
    return Grouped(states=expl, round_of=round_of, members=members)


def explore(
    bound: int,
    rounds: int,
    reading: Reading = CHOSEN,
    plain_states: bool = True,
    keep_log: bool = False,
) -> Grouped:
    """The exploration of states from the empty state, then the results formed."""
    return group(explore_states(bound, rounds, reading, plain_states, keep_log))


def shortest_sequences(grouped: Grouped) -> dict[Key24, int]:
    """Shortest sequences of changes to each result: counted change by change on the states kept.

    Only changes that raise the round by one and add a term, add an assertion
    or fill are followed (a shortest sequence has no other change, D5); a
    result's count adds up the counts of its states reached in its round.
    """
    expl = grouped.states
    counts = {s: 0 for s in expl.depth}
    counts[empty()] = 1
    for state, change, _, out in performed(expl):
        if out in expl.depth and expl.depth[out] == expl.depth[state] + 1 and is_raising(change):
            counts[out] += counts[state]
    return {k: sum(counts[m] for m in grouped.fewest_members(k)) for k in grouped.round_of}
