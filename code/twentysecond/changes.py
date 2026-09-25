"""Changes of the twenty-second seed: the ninth's four kinds, attempted on results.

Given by the seed
    A change is exactly one of: identifying two terms; removing an assertion;
    adding a term; adding an assertion.  Nothing else is a change.  (The
    ninth's sentences, word for word.)

Cited from the ninth derivation (`ninth.changes`) and re-checked (no change)
    `Change`, `Kind`, `KINDS`, `changes` (identifications, removals in `r`,
    in `s`, a term, additions in `r`, in `s` — fewest additions first),
    `perform` and `is_addition` act on states and mention no sameness of
    results: they stand.  `identification_map` (`xry.changes`) is where each
    term goes when two are identified.

Chosen here (reading C-X of the paper)
    A change of a result is a change of any state that is that result; its
    outcome is the result of the outcome state.

Derived (paper; `lean4_core/Twentysecond/Same.lean`, `step_of_same`)
    The results one change away do not depend on which state of the result
    is taken: adding and identifying commute with adding a pair asserted
    together, and removing `xry` has the result of adding `xsy`.  So a result
    attempts the changes of its plain state (`result_changes`), and a
    removal from any other of its states (`padded_removals`) lands on one of
    their outcomes (checked in `twentysecond.evidence`).

Derived (paper; `lean4_core/Twentysecond/Record.lean`)
    How a change moves what is recorded for a result (`predicted_move`,
    computed from the excesses alone, independently of the outcome): a term
    `(+1, 0)`; adding `xqy` `(0, −1)` when the result asserts the pair in the
    other relation, else `(0, +1)`; removing `xqy` from a state asserting it
    `(0, −1)` when the result asserts `xqy`, else `(0, +1)`; identifying two
    terms `(−1, −2c)`, `c` the part of the merged excesses that are of
    opposite relations (`merge_loss`).
"""

from __future__ import annotations

from math import comb

from ninth.changes import KINDS, Change, Kind, changes, is_addition, perform
from xry.changes import identification_map

from twentysecond.state import DState, excess, plain

__all__ = [
    "KINDS",
    "Change",
    "Kind",
    "add_r_then_s",
    "attempt_count",
    "changes",
    "is_addition",
    "merge_loss",
    "pad",
    "padded_removals",
    "perform",
    "predicted_move",
    "removal_move",
    "result_changes",
]


def result_changes(state: DState) -> tuple[Change, ...]:
    """The changes attempted for the result of `state`: those of its plain state, fewest additions first."""
    return changes(plain(state))


def attempt_count(state: DState) -> int:
    """`C(n, 2) + d + 1 + 2n²`, `d` the pairs asserted in the plain state (the ninth's count, read there)."""
    n = state.n
    return comb(n, 2) + plain(state).distinct + 1 + 2 * n * n


def merge_loss(state: DState, u: int, v: int) -> int:
    """Half the recorded assertions an identification of `u < v` takes out: `Σ (Σ|e| − |Σe|) / 2` over merged pairs."""
    n = state.n
    q = identification_map(n, u, v)
    groups: dict[tuple[int, int], list[int]] = {}
    for x in range(n):
        for y in range(n):
            groups.setdefault((q[x], q[y]), []).append(excess(state, x, y))
    lost = sum(sum(abs(e) for e in group) - abs(sum(group)) for group in groups.values())
    return lost // 2


def removal_move(state: DState, rel: str, x: int, y: int) -> int:
    """How removing `x rel y` (from a state asserting it) moves the recorded assertions of the result."""
    e = excess(state, x, y)
    asserts = e > 0 if rel == "r" else e < 0
    return -1 if asserts else 1


def pad(state: DState, x: int, y: int) -> DState:
    """`state` with one more `xry` and one more `xsy`: the same result, another state of it."""
    i = x * state.n + y
    r = list(state.r)
    s = list(state.s)
    r[i] += 1
    s[i] += 1
    return DState(state.n, tuple(r), tuple(s))


def add_r_then_s(state: DState, x: int, y: int) -> DState:
    """Two additions in a row: `xry`, then `xsy` (the pair that undoes the first)."""
    return perform(perform(state, Change(Kind.ADD_ASSERTION, "r", x, y)), Change(Kind.ADD_ASSERTION, "s", x, y))


def padded_removals(state: DState) -> list[tuple[DState, Change]]:
    """Removals from states of the result that are not plain: at every pair, pad it, then remove either relation there."""
    out: list[tuple[DState, Change]] = []
    for x in range(state.n):
        for y in range(state.n):
            padded = pad(state, x, y)
            for rel in ("r", "s"):
                out.append((padded, Change(Kind.REMOVE, rel, x, y)))
    return out


def predicted_move(state: DState, change: Change) -> tuple[int, int]:
    """(terms, assertions) by which `change` moves what is recorded for the result of `state`."""
    if change.kind is Kind.ADD_TERM:
        return 1, 0
    if change.kind is Kind.IDENTIFY:
        return -1, -2 * merge_loss(state, change.x, change.y)
    if change.kind is Kind.REMOVE:
        return 0, removal_move(state, change.rel, change.x, change.y)
    e = excess(state, change.x, change.y)
    other = e < 0 if change.rel == "r" else e > 0
    return 0, -1 if other else 1
