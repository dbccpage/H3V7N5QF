"""seventh: the seed of `prompt/seventh/seed_prompt.md`, four kinds of change from nothing.

The seventh seed differs from the sixth (`prompt/sixth/seed_prompt.md`) by one
passage: "Given: `arb` is asserted with multiplicity one. Whether `bra` is
asserted is not given." becomes "Nothing is given: to begin with there are no
terms and nothing is asserted."  The state is the sixth's with the names left
out (`fourth.state.MState` with `names = None`; a state may have no terms);
the changes are the sixth's four kinds; the beginning is the empty state.
This package imports from `xry`, `fourth`, `fifth` and `sixth` only what the
given and the names leave intact and defines afresh what it changes.  Each
module's docstring says which notions are given by the seed, which are cited
from an earlier derivation and re-checked (and whether they survive with
nothing given and no names), and which are readings chosen here.
"""
