from __future__ import annotations

import pytest

from fourth.state import MState
from ninth.state import DState, empty
from sixteenth.state import (
    RState,
    Reading,
    add_assertion16,
    add_term16,
    admit16,
    canonical16,
    empty16,
    forget_canonical_forms16,
    has_term16,
    identify16,
    of_ninth,
    remove16,
    rewrite16,
    same16,
    swap16,
    to_ninth,
    written16,
)


def test_empty_beginning() -> None:
    start = empty16()
    assert start.n == 0 and start.size == 0 and start.potential == 0 and start.mass == 0
    assert start.record_empty and start.recorded_pairs == () and start.diagonal_mass == 0
    assert written16(start) == "no terms; asserted nothing; recorded nothing"
    assert start.key() == "0::|#" and not has_term16(start)
    assert to_ninth(start) == empty() and of_ninth(empty()) == start


def test_state_shape_is_checked() -> None:
    with pytest.raises(ValueError, match="over the terms"):
        RState(DState.of(1, [], []), MState(2, (0,) * 4))
    with pytest.raises(ValueError, match="no names"):
        RState(DState.of(1, [], [], (0, 0)), MState(1, (0,)))
    with pytest.raises(ValueError, match="no names"):
        of_ninth(DState.of(1, [], [], (0, 0)))


def test_written_and_measures() -> None:
    rs = RState.of(2, [(0, 1)], [(1, 0)], [(0, 1), (0, 1), (1, 1)])
    assert written16(rs) == "terms a b; asserted arb bsa; recorded aℓb(2) bℓb"
    assert rs.size == 4 and rs.record_total == 3 and rs.potential == 10 and rs.mass == 5
    assert rs.diagonal_mass == 1 and rs.pair_mass(0, 1) == 3 and rs.pair_mass(1, 0) == 1
    assert rs.recorded(0, 1) == 2 and rs.has_leftover(1, 1) and not rs.has_leftover(0, 0)
    assert rs.recorded_pairs == ((0, 1), (1, 1)) and not rs.record_empty
    assert rs.key() == "2::0-1*1|1-0*1#0-1*2.1-1*1" and rs.written() == written16(rs)


def test_the_five_operations() -> None:
    one = RState.of(1, [])
    ara = add_assertion16(one, "r", 0, 0)
    assert ara == RState.of(1, [(0, 0)]) and ara.record_empty
    left = remove16(ara, "r", 0, 0)
    assert left == RState.of(1, [], [], [(0, 0)]) and left.potential == 3 and left.mass == 1
    assert admit16(left, "r", 0, 0) == ara
    assert admit16(left, "s", 0, 0) == RState.of(1, [], [(0, 0)])
    with pytest.raises(ValueError, match="recorded leftover"):
        admit16(ara, "r", 0, 0)
    two = add_term16(left)
    assert two.n == 2 and two.recorded(0, 0) == 1 and two.record.mult == (1, 0, 0, 0)
    merged = identify16(add_assertion16(two, "s", 0, 1), 0, 1)
    assert merged.n == 1 and merged.state.s == (1,) and merged.recorded(0, 0) == 1
    # the record of merged pairs adds up
    both = RState.of(2, [], [], [(0, 1), (1, 0), (1, 1)])
    assert identify16(both, 0, 1).recorded(0, 0) == 3
    assert identify16(both, 0, 1, Reading.DROP).recorded(0, 0) == 0
    kept = RState.of(3, [], [], [(2, 2), (0, 2)])
    dropped = identify16(kept, 0, 1, Reading.DROP)
    assert dropped.n == 2 and dropped.record.mult == (0, 0, 0, 1)


def test_set_reading_records_a_pair_once() -> None:
    twice = RState.of(1, [(0, 0), (0, 0)])
    once = remove16(twice, "r", 0, 0, Reading.SET)
    assert once.recorded(0, 0) == 1
    assert remove16(once, "r", 0, 0, Reading.SET).recorded(0, 0) == 1
    assert remove16(once, "r", 0, 0).recorded(0, 0) == 2


def test_sameness_rewrites_the_record_with_the_relations() -> None:
    a = RState.of(2, [(0, 1)], [], [(1, 1)])
    b = RState.of(2, [(1, 0)], [], [(0, 0)])
    assert same16(a, b) and canonical16(a) == canonical16(b)
    c = RState.of(2, [(0, 1)], [], [(0, 0)])
    assert not same16(a, c)
    assert not same16(a, RState.of(1, [(0, 0)], [], [(0, 0)]))
    assert rewrite16(a, (1, 0)) == b
    assert canonical16(a) is canonical16(a)
    assert forget_canonical_forms16() >= 1 and forget_canonical_forms16() == 0


def test_swap_keeps_the_record() -> None:
    rs = RState.of(2, [(0, 1)], [(1, 1)], [(0, 0)])
    exchanged = swap16(rs)
    assert exchanged.state.r == rs.state.s and exchanged.state.s == rs.state.r and exchanged.record == rs.record
    assert swap16(exchanged) == rs


def test_of_helper_builds_states() -> None:
    rs = RState.of(2, [(0, 1)], recorded=[(0, 1)])
    assert rs.state.total_r == 1 and rs.state.total_s == 0 and rs.recorded(0, 1) == 1
    assert has_term16(rs)
