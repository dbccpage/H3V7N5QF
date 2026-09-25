# H1 prediction, to be frozen before launch

Written by the operator on 2026-09-24, by hand, from the seed and the ninth's
ledger. Nothing here was computed. Its SHA-256 is in `prediction.sha256`; the
digest is committed before launch, and the run's worktree omits `meta/`.
After the run each item is scored hit, miss or not addressed, against the
paper and evidence verbatim, without editing this file. A miss is a result.

## Words used here

For an ordered pair of terms `(x, y)`: its *r-count* is the multiplicity of
`xry`, its *s-count* that of `xsy`, and its *difference* is the r-count minus
the s-count, a whole number that may be below zero.

For a result:

- its *size* is its number of terms plus the sum of its multiplicities;
- its *spread* is its number of terms plus the sum, over ordered pairs, of
  the difference without its sign;
- its *signed total* is its number of terms plus the sum of the differences.

## Predictions

**P1. Sameness.** Two results are the same exactly when, after rewriting
terms, they have the same number of terms and every ordered pair has the same
difference. Each result is the same as exactly one result in which no ordered
pair carries both `xry` and `xsy`: its *plain form*. [expected: derived, Lean]

**P2. Readings the run must keep.** Identifying two terms, adding a term and
adding an assertion each respect the new sameness. Removing an assertion,
read on the written assertions, does not. Witness: on two terms `x` and `y`,
the result asserting `xry` and `xsy` once each is the same as the result
asserting nothing, yet only the first allows a removal. So the run keeps at
least two readings of removal. The record ("how many terms and assertions it
adds to what is given") splits the same way. Read on the written assertions,
it depends on which member of a result was reached: adding `xry` and then
`xsy` returns to the same result with a record two higher. Read on the plain
form, it is the spread. [expected: derived, with the two-term witness]

**P3. Fewest changes.** From the beginning, where nothing is given, the
fewest changes to a result equal its spread, under every reading kept in P2.
The lower bound: no change raises the spread by more than one, and an
identification never raises it. The upper bound: add the terms, then the
plain form's assertions. [expected: derived, Lean]

**P4. The demand, answered.** In the ninth, no addition is ever undone by
later additions: each addition raises the size by exactly one (the ninth's
D4). Here, adding `xsy` right after `xry` returns to the same result, so an
addition can undo an earlier addition. [expected: derived on both sides]

**P5. What survives of the ninth's step law.** The ninth's law, that every
change moves the size by exactly one, fails for the spread. Witness: in the
result on `x`, `y`, `z` asserting `xry` and `zsy`, identifying `x` with `z`
lowers the spread from 5 to 2. The law survives for the signed total: every
change moves it by exactly one, up or down. Hence every sequence of changes
between two results has a length at least the gap between their signed
totals, and of the same parity. [expected: computed witness, derived, Lean]

**P6. The exchange.** Exchanging `r` and `s` changes the sign of every
difference, respects the sameness, and done twice gives back the result. It
is a symmetry of the results, the fewest changes and reachability, as the
ninth's D16 is. [expected: derived, Lean]

**P7. Reachability.** A result is reachable from another exactly when it has
a term or the start is empty. The empty result is left and never returned
to. The ninth's D8 and D9 survive. [expected: derived, Lean]

**P8. Rounds.** The results first reached in round `k` are exactly the
results of spread `k`. Their plain forms correspond one to one with the
ninth's round-`k` results in which no ordered pair carries both relations,
so each round's count here equals the ninth's count restricted to those
results, under the same bound on terms. [expected: computed, derived]

**P9. The pair of maps.** The ninth's results do not map one to one: on two
terms, asserting `xry` and `xsy` once each and asserting nothing become one
result. The seventh's do: reading each multiplicity as a difference is one
to one and carries the seventh's changes to changes here. The map back
answers "none" exactly on the results with a difference below zero. The
smallest such result has one term and asserts `xsx` once. Where two of the
ninth's results become one, each ordered pair loses the smaller of its two
counts. [expected: derived, Lean]
