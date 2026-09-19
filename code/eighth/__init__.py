"""eighth: the seed of `prompt/eighth/seed_prompt.md`, two relations `r` and `s`.

The eighth seed differs from the sixth (`prompt/sixth/seed_prompt.md`) by two
passages: an assertion is written `xry` or `xsy`, `r` and `s` being the two
relations, and whether `bra` or anything written with `s` is asserted is not
given.  The state gains a second multiplicity function (`eighth.state`
`DState`), whose two parts are each a state of the sixth seed with the same
terms and names; the changes are the sixth's four kinds over both relations.
This package imports from `xry`, `fourth`, `fifth` and `sixth` only what one
relation leaves intact — applied to a part — and defines afresh what the
second relation changes.  Each module's docstring says which notions are
given by the seed, which are cited from an earlier derivation and re-checked
(and whether they survive the second relation), and which are readings
chosen here.
"""
