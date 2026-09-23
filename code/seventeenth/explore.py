"""The two explorations: do not enter an obstructed change, or perform it.

Given
    Attempt every change, fewest additions first. A refused change changes
    nothing. Any outcome is valid.

Cited from the base and re-checked
    A-replace is the closure under unobstructed `perform`, which `xry.explore`
    computes. The base cost is `xry.cost.cost`.

Chosen
    A-perform enters `perform` of an obstructed change as well. The round of
    a result is the length of the shortest sequence of performed changes.
"""

from __future__ import annotations

from dataclasses import dataclass

from xry.changes import Change, Kind, changes, obstruction, perform
from xry.cost import cost
from xry.explore import order
from xry.state import Sameness, State, canonical, given


@dataclass(frozen=True)
class StepRecord:
    """One attempted change in a reading."""

    reading: str
    round: int
    state: str
    change: str
    obstructed: bool
    outcome: str
    entered: bool


@dataclass
class Closure:
    """States reached, by round, and where the declared bound cut the closure.

    `frontier` lists the attempts that leave the term bound. `unexpanded`
    lists the results first reached in the last round: the round bound left
    their changes unattempted. Both are empty only for a closure that
    finished inside the bound.
    """

    depth: dict[State, int]
    frontier: tuple[str, ...]
    log: tuple[StepRecord, ...] = ()
    unexpanded: tuple[str, ...] = ()


def closure(
    start: State,
    bound: int,
    rounds: int,
    *,
    enter_obstructed: bool,
    keep_log: bool = False,
) -> Closure:
    """Breadth-first closure under `perform`.

    `enter_obstructed` is A-perform when true and A-replace when false.
    An outcome with more than `bound` terms is frontier, not a result. A
    result first reached in round `rounds` is unexpanded.
    """
    if rounds < 0 or bound < start.n:
        raise ValueError("the bound is below the start, or the rounds are negative")
    root = canonical(start)
    depth: dict[State, int] = {root: 0}
    wave = [root]
    frontier: list[str] = []
    log: list[StepRecord] = []
    reading = "perform" if enter_obstructed else "replace"
    for round_index in range(1, rounds + 1):
        found: list[State] = []
        for state in wave:
            for change in changes(state):
                blocked = bool(obstruction(state, change))
                outcome = perform(state, change)
                entered = (enter_obstructed or not blocked) and outcome.n <= bound
                if outcome.n > bound and (enter_obstructed or not blocked):
                    frontier.append(f"{state.key()}|{change.written(state)}|terms")
                key = canonical(outcome)
                if entered and key not in depth:
                    depth[key] = round_index
                    found.append(key)
                if keep_log:
                    log.append(
                        StepRecord(
                            reading,
                            round_index,
                            state.key(),
                            change.written(state),
                            blocked,
                            key.key(),
                            entered,
                        )
                    )
        wave = sorted(found, key=order)
    unexpanded = tuple(sorted(state.key() for state in wave))
    return Closure(depth, tuple(sorted(set(frontier))), tuple(log), unexpanded)


def closure_unobstructed(start: State, bound: int, rounds: int, keep_log: bool = False) -> Closure:
    """A-replace: an obstructed change is not entered."""
    return closure(start, bound, rounds, enter_obstructed=False, keep_log=keep_log)


def closure_perform(start: State, bound: int, rounds: int, keep_log: bool = False) -> Closure:
    """A-perform: every change is entered, obstructed or not."""
    return closure(start, bound, rounds, enter_obstructed=True, keep_log=keep_log)


def loopfree_states(n: int, sameness: Sameness) -> set[State]:
    """Every state of `n` terms that asserts no `xrx`, up to `sameness`.

    Independent of the exploration: each off-diagonal mask, each placement of
    the names, then the least writing.
    """
    if n < 1:
        raise ValueError("a state counted here has a term")
    off = [(x, y) for x in range(n) for y in range(n) if x != y]
    if sameness is Sameness.ANCHORED:
        name_sets: tuple[tuple[int, int] | None, ...] = tuple((a, b) for a in range(n) for b in range(n))
    else:
        name_sets = (None,)
    out: set[State] = set()
    for bits in range(1 << len(off)):
        pairs = [pair for index, pair in enumerate(off) if bits >> index & 1]
        for names in name_sets:
            out.add(canonical(State.of(n, pairs, names)))
    return out


def by_cost(bound: int, rounds: int, bra: bool, sameness: Sameness) -> set[State]:
    """Loop-free states with at most `bound` terms whose base cost is at most `rounds`.

    The base formula, cited. It is a certificate for A-replace only if it
    agrees with the closure.
    """
    found: set[State] = set()
    for n in range(1, bound + 1):
        for state in loopfree_states(n, sameness):
            if cost(state, bra) <= rounds:
                found.add(state)
    return found


def identified(bra: bool, sameness: Sameness) -> State:
    """The outcome of identifying `a` with `b` in what is given. One change."""
    return canonical(perform(given(bra, sameness), Change(Kind.IDENTIFY, 0, 1)))


def added_loop(bra: bool, sameness: Sameness) -> State:
    """The outcome of adding `ara` to what is given. One change."""
    return canonical(perform(given(bra, sameness), Change(Kind.ADD_ASSERTION, 0, 0)))


def _with_loop_on(bra: bool, sameness: Sameness, at: int) -> State:
    """What is given, plus `xrx` on term `at` (0 is `a`, 1 is `b`)."""
    pairs: list[tuple[int, int]] = [(0, 1), (at, at)]
    if bra:
        pairs.append((1, 0))
    names = (0, 1) if sameness is Sameness.ANCHORED else None
    return canonical(State.of(2, pairs, names))


def with_loop(bra: bool, sameness: Sameness) -> State:
    """The unchosen beginning: what is given, and also `ara`."""
    return _with_loop_on(bra, sameness, 0)


def with_other_loop(bra: bool, sameness: Sameness) -> State:
    """The unchosen beginning: what is given, and also `brb`."""
    return _with_loop_on(bra, sameness, 1)


def loopy_witness() -> tuple[State, Change]:
    """A state asserting `ara`, and an identification M1 allows and M2 does not.

    Terms 0, 1, 2; `0r0` asserted; nothing between 1 and 2.
    """
    return State.of(3, [(0, 0)], (0, 1)), Change(Kind.IDENTIFY, 1, 2)
