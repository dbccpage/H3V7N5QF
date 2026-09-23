"""States of the sixteenth seed: a two-relation state together with its record of unadmitted leftovers.

Given by the sixteenth seed
    Terms are written with letters.  An assertion is written `xry` or `xsy`;
    it is asserted a number of times, its multiplicity.  Nothing is given.
    After every change, record what that change leaves.  A leftover is
    written neither `xry` nor `xsy`.  A recorded leftover `xℓy` may be
    admitted, adding the assertion `xry` or the assertion `xsy`; an
    unadmitted leftover is not an assertion.  Two results that differ only in
    how their terms are written are the same result.

Chosen here (reading C-R1 of the paper)
    A state is a ninth state (terms, a multiplicity per ordered pair in `r`
    and in `s`, no names) together with its *record*: for every ordered pair
    of its terms, how many leftovers `xℓy` are recorded and not admitted.
    The record is carried by the state because a recorded leftover may
    later be admitted; it is not an assertion of either relation (an
    unadmitted leftover is not an assertion), so it is kept apart from the
    two multiplicity functions and is not counted in the ninth's size.  A
    rewriting of the terms acts on the two relations and on the record
    together: two results are the same when one rewriting carries all three.

Cited from the ninth derivation (`ninth.state`, `eighth.state`) and re-checked
    The two-relation state `DState` (with `names = None`), `canonical`,
    `rewrite`, `identify`, `remove`, `swap`, `has_term` and `written` mention
    no record; they survive as the ninth-state part of a sixteenth state and
    are used through `to_ninth`.  A sixteenth state with an empty record is
    exactly a ninth state (`of_ninth`, `to_ninth`).

Cited from the fourth and fifth derivations (`fourth.state`, `fourth.changes`,
`fifth.state`) and re-checked
    The record is a counted one-relation state on the same terms (`MState`
    with `names = None`), so the fourth's `perform` (a term; raising one
    count), `rewrite` and `_rewritings`, and the fifth's `remove` (lowering
    one count) and `identify` (the counts of the pairs that become one pair
    add up) act on the record exactly as they act on a multiplicity
    function.  They are reused, not reproved: the record is a third function
    on pairs in every respect but one — it is fed by removals, not by
    additions, and it feeds the two relations, not itself.

Defined here
    `RState`, `empty16`, `of_ninth`, `to_ninth`, the five operations
    (`add_term16`, `add_assertion16`, `remove16`, `admit16`, `identify16`),
    `rewrite16`, `canonical16`, `same16`, `swap16`, `written16`, the
    potential (`RState.potential`: the size plus twice the record) and the
    mass (`RState.mass`: both totals plus the record), and the two unchosen
    readings of the record (`Reading.SET`: a leftover of a pair is recorded
    or not; `Reading.DROP`: an identification drops the leftovers naming
    either merged term).
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from enum import Enum

from eighth.changes import Change as NinthChange
from eighth.changes import perform as perform_ninth
from fifth.state import identify as identify_part
from fifth.state import remove as remove_part
from fourth.changes import Change as ChangePart
from fourth.changes import perform as perform_part
from fourth.state import MState, Pair, _rewritings
from fourth.state import rewrite as rewrite_part
from ninth.state import DState, empty, has_term, rewrite, swap, written
from xry.changes import Kind

__all__ = [
    "DState",
    "MState",
    "Pair",
    "RState",
    "Reading",
    "add_assertion16",
    "add_term16",
    "admit16",
    "canonical16",
    "empty16",
    "forget_canonical_forms16",
    "has_term16",
    "identify16",
    "of_ninth",
    "remove16",
    "rewrite16",
    "same16",
    "swap16",
    "to_ninth",
    "written16",
]


class Reading(Enum):
    """How the record behaves: the chosen reading and the two unchosen ones kept."""

    COUNT = "a count of unadmitted leftovers per pair (C-R1, chosen)"
    SET = "a leftover of a pair is recorded or not (C-R2, unchosen)"
    DROP = "an identification drops the leftovers naming a merged term (C-R3, unchosen)"


@dataclass(frozen=True)
class RState:
    """A ninth state and its record: `record.mult[x * n + y]` unadmitted leftovers `xℓy`."""

    state: DState
    record: MState

    def __post_init__(self) -> None:
        if self.state.names is not None or self.record.names is not None:
            raise ValueError("a state of the sixteenth seed carries no names")
        if self.record.n != self.state.n:
            raise ValueError("the record is over the terms of the state")

    @staticmethod
    def of(n: int, r_pairs: Iterable[Pair], s_pairs: Iterable[Pair] = (), recorded: Iterable[Pair] = ()) -> RState:
        """Build a state from asserted pairs in each relation and recorded pairs; each listing adds one."""
        return RState(DState.of(n, r_pairs, s_pairs), MState.of(n, recorded))

    @property
    def n(self) -> int:
        """How many terms."""
        return self.state.n

    @property
    def size(self) -> int:
        """The ninth's size of the state: terms plus both totals (the record not counted)."""
        return self.state.size

    @property
    def record_total(self) -> int:
        """How many leftovers are recorded and not admitted, in all."""
        return self.record.m

    @property
    def potential(self) -> int:
        """The size plus twice the record: the fewest changes from the empty beginning (a theorem of the paper)."""
        return self.state.size + 2 * self.record.m

    @property
    def mass(self) -> int:
        """Both totals plus the record: what no change ever lowers (a theorem of the paper)."""
        return self.state.m + self.record.m

    @property
    def diagonal_mass(self) -> int:
        """The mass carried by the pairs `(x, x)`: what no change ever lowers either."""
        n = self.n
        return sum(self.state.r[x * n + x] + self.state.s[x * n + x] + self.record.mult[x * n + x] for x in range(n))

    def pair_mass(self, x: int, y: int) -> int:
        """The mass of one ordered pair: both multiplicities plus the record."""
        return self.state.mult_of("r", x, y) + self.state.mult_of("s", x, y) + self.record.mult_of(x, y)

    def recorded(self, x: int, y: int) -> int:
        """How many leftovers `xℓy` are recorded and not admitted."""
        return self.record.mult_of(x, y)

    def has_leftover(self, x: int, y: int) -> bool:
        """Is some leftover `xℓy` recorded and not admitted?"""
        return self.record.has(x, y)

    @property
    def recorded_pairs(self) -> tuple[tuple[int, int], ...]:
        """The pairs with a recorded leftover, sorted, each once."""
        return self.record.pairs

    @property
    def record_empty(self) -> bool:
        """Is nothing recorded?  Then the state is a ninth state."""
        return self.record.m == 0

    def key(self) -> str:
        """A compact identifier of this exact writing: the ninth's key, then the record."""
        body = ".".join(f"{x}-{y}*{k}" for x, y, k in self.record.counted)
        return f"{self.state.key()}#{body}"

    def written(self) -> str:
        """The state in the seed's notation, the record written with `ℓ`."""
        return written16(self)


def empty16() -> RState:
    """What is given: no terms, nothing asserted, nothing recorded."""
    return RState(empty(), MState(0, ()))


def of_ninth(state: DState) -> RState:
    """A ninth state read as a sixteenth state with an empty record."""
    if state.names is not None:
        raise ValueError("a state of the ninth seed carries no names")
    return RState(state, MState(state.n, (0,) * (state.n * state.n)))


def to_ninth(rs: RState) -> DState:
    """The ninth state of a sixteenth state: the record forgotten."""
    return rs.state


def written16(rs: RState) -> str:
    """The state written: terms, assertions, then what is recorded with the letter `ℓ`."""
    head = written(rs.state)
    if rs.record.m == 0:
        return f"{head}; recorded nothing"
    w = rs.state.term_writing()
    parts = [f"{w[x]}ℓ{w[y]}" + (f"({k})" if k > 1 else "") for x, y, k in rs.record.counted]
    return f"{head}; recorded {' '.join(parts)}"


def rewrite16(rs: RState, p: tuple[int, ...]) -> RState:
    """The same state with term `t` written as `p[t]`, in both relations and in the record."""
    return RState(rewrite(rs.state, p), rewrite_part(rs.record, p))


_CANONICAL: dict[RState, RState] = {}


def canonical16(rs: RState) -> RState:
    """The least writing of `rs`; equal exactly for same states.

    The rewriting acts on the `r` multiplicities, the `s` multiplicities and
    the record together; the three are compared in that order.  A sixteenth
    state with an empty record has the ninth's least writing.
    """
    hit = _CANONICAL.get(rs)
    if hit is not None:
        return hit
    n = rs.n
    best: tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]] | None = None
    for _p, index in _rewritings(n):
        r = [0] * (n * n)
        s = [0] * (n * n)
        rec = [0] * (n * n)
        for i, k in enumerate(rs.state.r):
            if k:
                r[index[i]] = k
        for i, k in enumerate(rs.state.s):
            if k:
                s[index[i]] = k
        for i, k in enumerate(rs.record.mult):
            if k:
                rec[index[i]] = k
        cand = (tuple(r), tuple(s), tuple(rec))
        if best is None or cand < best:
            best = cand
    assert best is not None  # there is always the rewriting that changes nothing
    out = RState(DState(n, best[0], best[1]), MState(n, best[2]))
    _CANONICAL[rs] = out
    return out


def same16(a: RState, b: RState) -> bool:
    """Do `a` and `b` differ only in how their terms are written?"""
    return a.n == b.n and canonical16(a) == canonical16(b)


def forget_canonical_forms16() -> int:
    """Empty the cache of least writings; returns how many it held."""
    held = len(_CANONICAL)
    _CANONICAL.clear()
    return held


def swap16(rs: RState) -> RState:
    """The two relations exchanged; the record, naming no relation, is unchanged."""
    return RState(swap(rs.state), rs.record)


def add_term16(rs: RState) -> RState:
    """A new term, with nothing asserted and nothing recorded about it."""
    return RState(
        perform_ninth(rs.state, NinthChange(Kind.ADD_TERM)),
        perform_part(rs.record, ChangePart(Kind.ADD_TERM)),
    )


def add_assertion16(rs: RState, rel: str, x: int, y: int) -> RState:
    """`xry` (or `xsy`) asserted once more, directly; the record unchanged."""
    return RState(perform_ninth(rs.state, NinthChange(Kind.ADD_ASSERTION, rel, x, y)), rs.record)


def remove16(rs: RState, rel: str, x: int, y: int, reading: Reading = Reading.COUNT) -> RState:
    """`xry` (or `xsy`) asserted once less, and one leftover `xℓy` recorded.

    Under the unchosen reading `SET` a pair already recorded records nothing
    new.
    """
    lowered = perform_ninth(rs.state, NinthChange(Kind.REMOVE, rel, x, y))
    if reading is Reading.SET and rs.record.has(x, y):
        return RState(lowered, rs.record)
    return RState(lowered, perform_part(rs.record, ChangePart(Kind.ADD_ASSERTION, x, y)))


def admit16(rs: RState, rel: str, x: int, y: int) -> RState:
    """A recorded leftover `xℓy` admitted into `rel`: `xry` (or `xsy`) asserted once more, the record lowered."""
    if not rs.record.has(x, y):
        raise ValueError("only a recorded leftover is admitted")
    return RState(perform_ninth(rs.state, NinthChange(Kind.ADD_ASSERTION, rel, x, y)), remove_part(rs.record, x, y))


def identify16(rs: RState, x: int, y: int, reading: Reading = Reading.COUNT) -> RState:
    """The terms `x < y` replaced by one term in every assertion and in the record.

    The record of the pairs that become one pair adds up (the fifth's
    reading, reused).  Under the unchosen reading `DROP` the leftovers
    naming either merged term are dropped first.
    """
    record = rs.record
    if reading is Reading.DROP:
        n = rs.n
        kept = [0 if (i // n in (x, y) or i % n in (x, y)) else k for i, k in enumerate(record.mult)]
        record = MState(n, tuple(kept))
    return RState(perform_ninth(rs.state, NinthChange(Kind.IDENTIFY, "", x, y)), identify_part(record, x, y))


def has_term16(rs: RState) -> bool:
    """Does the state have a term?"""
    return has_term(rs.state)
