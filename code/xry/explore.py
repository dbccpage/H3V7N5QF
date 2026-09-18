"""Attempting every change on every alternative, round by round.

Given by the seed
    Attempt every change, fewest additions first.  Attempt 100 changes along
    each alternative, finishing earlier changes on every alternative before
    later ones.  Do not invent a change to reach 100.  If the alternatives
    exceed what can be completed, declare a finite bound, export the exact
    frontier, and prove what is complete within it.

Chosen here
    * An alternative is a result (a legal state, up to sameness) together
      with the changes that can be attempted on it.
    * Round `k` attempts every change on every result first reached in
      round `k - 1`, so each change on each result is attempted exactly once,
      in the round after the result is reached.  Attempting it again in a
      later round would repeat a known outcome.  Within a result, changes are
      taken fewest additions first; results are taken in a fixed order.
      Each performed change counts one; a refused change is an attempt of its
      round and changes nothing.
    * The declared bound is on the number of terms.  The frontier lists,
      for every attempt whose outcome or whose answer has more terms than the
      bound, one entry for the outcome and one for each such answer.

Derived (paper, Theorem on answers)
    Every answer to an obstructed change is a sequence of unobstructed
    changes, so answers reach no result that unobstructed changes do not
    reach.  The exploration therefore spreads along unobstructed changes and
    *checks* the answers afterwards (`check_answers`).
"""

from __future__ import annotations

from dataclasses import dataclass, field

from xry.changes import Answer, Change, Kind, answers, changes, obstruction, perform
from xry.state import Pair, State, canonical


def order(state: State) -> tuple[int, int, int, int]:
    """A fixed order on states, for reproducible output."""
    a, b = state.names if state.names is not None else (-1, -1)
    return (state.n, state.mask, a, b)


@dataclass(frozen=True)
class Attempt:
    """One attempted change: the change, the obstruction, the outcome or answers.

    `outcome` is the result (least writing) of an unobstructed change within
    the bound; it is `None` for an obstructed change and for an outcome
    beyond the bound (`beyond`).
    """

    state: State
    change: Change
    obstruction: tuple[Pair, ...]
    outcome: State | None
    beyond: bool
    answers: tuple[Answer, ...]


@dataclass(frozen=True)
class Exit:
    """A frontier entry: an attempt that leaves the bound, and how."""

    state: State
    change: Change
    by: str


@dataclass
class Exploration:
    """Everything recorded by `explore`."""

    start: State
    bound: int
    rounds: int
    depth: dict[State, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    obstructed_per_round: list[int]
    frontier: list[Exit]
    log: list[Attempt] = field(default_factory=list)

    @property
    def last_new_round(self) -> int:
        """The last round that produced a new result within the bound."""
        return max(r for r, new in enumerate(self.new_per_round) if new)


def attempt(state: State, change: Change, bound: int) -> Attempt:
    """Attempt `change` on the legal `state` and record what happens."""
    blocked = obstruction(state, change)
    if blocked:
        return Attempt(state, change, blocked, None, False, answers(state, change))
    out = perform(state, change)
    if out.n > bound:
        return Attempt(state, change, (), None, True, ())
    return Attempt(state, change, (), canonical(out), False, ())


def explore(start: State, bound: int, rounds: int = 100, keep_log: bool = False) -> Exploration:
    """Explore from `start`, keeping every result with at most `bound` terms."""
    if not start.legal:
        raise ValueError("what is given asserts no xrx")
    if start.n > bound:
        raise ValueError("the bound is below what is given")
    root = canonical(start)
    depth = {root: 0}
    wave = [root]
    new_per_round = [1]
    attempts_per_round = [0]
    obstructed_per_round = [0]
    frontier: list[Exit] = []
    log: list[Attempt] = []
    attempts_known = 0
    obstructed_known = 0
    for r in range(1, rounds + 1):
        found: list[State] = []
        for state in wave:
            for change in changes(state):
                rec = attempt(state, change, bound)
                attempts_known += 1
                obstructed_known += bool(rec.obstruction)
                if rec.beyond:
                    frontier.append(Exit(state, change, "the change"))
                for ans in rec.answers:
                    if ans.result.n > bound:
                        frontier.append(Exit(state, change, ans.kind.value))
                if rec.outcome is not None and rec.outcome not in depth:
                    depth[rec.outcome] = r
                    found.append(rec.outcome)
                if keep_log:
                    log.append(rec)
        # Round r attempted every change on every result first reached in round r - 1.
        attempts_per_round.append(attempts_known)
        obstructed_per_round.append(obstructed_known)
        wave = sorted(found, key=order)
        new_per_round.append(len(wave))
    return Exploration(
        start=root,
        bound=bound,
        rounds=rounds,
        depth=depth,
        new_per_round=new_per_round,
        attempts_per_round=attempts_per_round,
        obstructed_per_round=obstructed_per_round,
        frontier=frontier,
        log=log,
    )


@dataclass(frozen=True)
class AnswerCheck:
    """Totals of `check_answers`."""

    obstructed: int
    answers_within: int
    answers_beyond: int
    failures: tuple[str, ...]


def check_answers(expl: Exploration) -> AnswerCheck:
    """Check that no answer reaches anything the unobstructed changes do not.

    For every obstructed attempt on every explored result and every answer
    within the bound: the answer's result is an explored result, reached no
    later than the round of the state plus the changes the answer performs.
    """
    obstructed = within = beyond = 0
    failures: list[str] = []
    for state in sorted(expl.depth, key=order):
        for change in changes(state):
            if not obstruction(state, change):
                continue
            obstructed += 1
            for ans in answers(state, change):
                if ans.result.n > expl.bound:
                    beyond += 1
                    continue
                within += 1
                got = expl.depth.get(canonical(ans.result))
                if got is None or got > expl.depth[state] + ans.performed:
                    failures.append(f"{state.key()} / {change.written(state)} / {ans.kind.value}")
    return AnswerCheck(obstructed, within, beyond, tuple(failures))


def rigid(state: State) -> bool:
    """Is every identification on `state` obstructed (and is there one)?"""
    pairs = [c for c in changes(state) if c.kind is Kind.IDENTIFY]
    return bool(pairs) and all(obstruction(state, c) for c in pairs)
