# Reading the thirteenth seed

Diff against `prompt/ninth/seed_prompt.md`: one passage added after the four
kinds.

"A coarser writing of an assertion forgets whether it was written with `r` or
with `s`. For every result, record also its coarser writing. Two results that
differ only in which relation wrote their assertions may be the same coarser
result."

Tenth leftover, eleventh colliding-writing, and twelfth identification-record
are not in this seed.

## Chosen readings

- C-C1. The coarser writing of a two-relation state is the one-relation state
  whose multiplicity at each pair is the sum of the `r` and `s`
  multiplicities (a seventh state). It is extra data on the result, not a
  third multiplicity. A result remains a ninth state up to writing.
- C-C2, unchosen, kept. The result *is* the coarser writing: two finer
  states with the same sum are one result.

## Expected

- The coarser writing determines the finer one exactly when nothing is
  asserted (the only split of a zero sum is `(0, 0)`).
- `0 r 1` and `0 s 1` are different finer results and the same coarser
  result.
- Adding in `r` and adding in `s` land on the same coarser writing.
- A coarser collision on one pair does not force a collision on another.
- Under C-C1 the ninth's results, cost, reachability and count survive.
- Under C-C2 the cost and the has-a-term criterion descend (size and terms
  are the same); the count of results does not (the quotient is strictly
  coarser for any state that asserts something).
