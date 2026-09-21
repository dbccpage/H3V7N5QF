from __future__ import annotations

import pytest

from eighth.state import DState as DStateEighth
from eighth.state import canonical as canonical_eighth
from eighth.state import identify as identify_eighth
from ninth.state import (
    RELATIONS,
    DState,
    MState,
    added,
    canonical,
    empty,
    forget_canonical_forms,
    forget_names,
    has_term,
    identify,
    name_terms,
    nothing_in,
    of_r,
    of_s,
    remove,
    rewrite,
    same,
    swap,
    written,
)


def test_the_state_is_the_eighths_without_names() -> None:
    assert DState is DStateEighth and canonical is canonical_eighth and identify is identify_eighth
    start = empty()
    assert start == DState(0, (), ()) and start.n == 0 and start.m == 0 and start.size == 0 and start.names is None
    assert canonical(start) == start and rewrite(start, ()) == start
    assert not has_term(start) and has_term(DState.of(1, [], []))
    assert added(start) == (0, 0) and added(DState.of(2, [(0, 1), (0, 1)], [(1, 1)])) == (2, 3)
    assert written(start) == "no terms; asserted nothing"
    assert written(DState.of(2, [(0, 1)], [])) == "terms a b; asserted arb"
    assert start.key() == "0::|" and start.legal_r and start.legal_s and start.simple
    assert nothing_in(start, "r") and nothing_in(start, "s") and RELATIONS == ("r", "s")


def test_the_two_readings_of_sameness_coincide_without_names() -> None:
    s = DState.of(2, [(1, 1)], [(1, 0)])
    t = DState.of(2, [(0, 0)], [(0, 1)])
    assert same(s, t) and canonical(s) == canonical(t)
    assert remove(DState.of(1, [(0, 0)], []), "r", 0, 0) == DState.of(1, [], [])
    assert identify(DState.of(2, [(0, 1)], [(1, 0), (1, 1)]), 0, 1) == DState.of(1, [(0, 0)], [(0, 0)] * 2)


def test_the_maps_to_and_from_the_eighth_and_the_exchange() -> None:
    named = DState.of(2, [(0, 1)], [(1, 0)], (0, 1))
    assert forget_names(named) == DState.of(2, [(0, 1)], [(1, 0)]) and forget_names(forget_names(named)).names is None
    assert name_terms(DState.of(2, [(0, 1)], []), 1) == DState.of(2, [(0, 1)], [], (1, 1))
    assert forget_names(name_terms(DState.of(1, [(0, 0)], []), 0)) == DState.of(1, [(0, 0)], [])
    ara = DState.of(1, [(0, 0)], [])
    asa = DState.of(1, [], [(0, 0)])
    assert swap(ara) == asa and swap(swap(ara)) == ara and same(swap(asa), ara)
    part = MState.of(2, [(0, 1)])
    assert of_r(part).nothing_in_s and of_s(part).total_r == 0 and of_s(part).s_part() == part
    assert of_s(MState(0, ())).n == 0
    with pytest.raises(ValueError):
        name_terms(named, 0)
    with pytest.raises(ValueError):
        name_terms(empty(), 0)
    with pytest.raises(ValueError):
        name_terms(DState.of(1, [], []), 1)


def test_the_cache_of_least_writings_can_be_emptied() -> None:
    canonical(DState.of(2, [(1, 1)], []))
    assert forget_canonical_forms() >= 1
    assert forget_canonical_forms() == 0
