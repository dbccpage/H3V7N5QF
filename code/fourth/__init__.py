"""fourth: the seed of `prompt/fourth/seed_prompt.md`, assertions counted.

The fourth seed differs from the third (`prompt/third/seed_prompt.md`) in two
sentences: an assertion is asserted a number of times, its multiplicity, and
adding an assertion raises its multiplicity by one; `arb` is asserted with
multiplicity one.  The state model changes (`fourth.state`), so this package
imports from `xry`, `second` and `third` only what the multiplicity leaves
intact and defines afresh what it changes.  Each module's docstring says which
notions are given by the seed, which are cited from an earlier derivation and
re-checked (and whether they survive the assertion being counted), and which
are readings chosen here.
"""
