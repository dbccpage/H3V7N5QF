# H2 prediction, to be frozen before launch

Written by the operator on 2026-09-26, by hand, from the seed and the
twenty-second's ledger. Nothing here was computed. Its SHA-256 is in
`prediction.sha256` and is committed before the seed is installed. The run's
clone holds no `meta/` and no history. After the run each item is scored
hit, partial or miss, against the paper and evidence verbatim, without
editing this file. A miss is a result.

## Words used here

- The *difference* at an ordered pair `(x, y)` is the multiplicity of `xry`
  minus that of `xsy`, as in the twenty-second.
- A *closed sequence* is a list of terms `x1, …, xk` read round back to
  `x1`. One term gives its loop `(x1, x1)`; two terms give a *return*
  `x → y → x`.
- The *sum* of a closed sequence is the sum of the differences along it:
  `(x1, x2)`, …, `(xk, x1)`.
- A *member* of a result is a state that is that result.
- A result is *exact* when it is the same as the result with nothing
  asserted on as many terms. Otherwise it is a *survivor*.

## Predictions

**Q0. The demand.** In the twenty-second, no result with something asserted
is the same as a result with nothing asserted, because its sameness keeps
every difference (its D1). Here some are: on two terms, the result asserting
`xry` and `ysx` is `x` raised, so it is the same as nothing.
[expected: derived, Lean]

**Q1. Sameness.** Two results are the same exactly when, after rewriting,
they have equally many terms and every closed sequence has the same sum in
both. Raising changes no loop's sum and no return's sum.
[expected: derived, Lean]

**Q2. Exact results.** A result is exact exactly when every closed sequence
sums to zero. Checking the closed sequences of one, two and three terms is
enough. [expected: derived, Lean for the criterion]

**Q3. Certified survivors.** Every survivor has a closed sequence of one, two
or three terms whose sum is not zero. That sequence is a check computed from
the result alone; it holds for every member and fails for every exact
result. Survivors occur on each size:

- one term: `xrx`;
- two terms: `xry` alone;
- three terms, with every loop and return summing to zero: `xry` and `ysx`,
  where the sequence `x, y, z` sums to 1.

[expected: derived, computed witnesses]

**Q4. Growth creates survivors.** Adding a term does not respect the
sameness. On `x`, `y`, the result asserting `xry` and `ysx` is the same as
the result asserting nothing. Add a term `z` to each: the sequence `x, y, z`
sums to 1 in the first and 0 in the second, so they are different results.
So adding a term to an exact result can reach a survivor, and which result
an added term reaches depends on the member taken. The run keeps at least
two readings of a change of a result:

- (S) changes act on states, and results are formed afterwards; a result's
  round is the first round in which any of its members is reached;
- (X) a change of a result is a change of any of its members.

[expected: derived, with the witness]

**Q5. Identifying two terms does not respect the sameness either, once
three terms remain.** On `x`, `u`, `v`, `y`, the result with `x` raised
asserts `xru`, `usx`, `xrv`, `vsx`, `xry` and `ysx`. It is the same as
nothing. Identify `u` with `v` as `t`: the result asserts `xrt` and `tsx`
twice each, `xry` and `ysx`. Its sequence `x, t, y` sums to 1, while
identifying `u` with `v` in nothing gives nothing. When at most two terms
remain it does respect the sameness. Adding an assertion respects it, and a
removal has the result of an addition, as in the twenty-second.
[expected: derived by hand; Lean or computed witness]

**Q6. Fewest changes, by reading.**

- Under (S): the fewest changes to a result equal its number of terms plus
  the fewest assertions of any of its members.
- Under (X): they equal its number of terms plus the sum, over loops, of
  each loop's sum without its sign, plus the sum, over pairs of terms, of
  each return's sum without its sign. What raising can move costs nothing,
  because a term can be added to whichever member suits.
- The readings part: the three-term survivor `xry`, `ysx` costs 5 under (S)
  and 3 under (X).
- Under (X), one added term from the two-term result asserting nothing
  already reaches infinitely many results: raise `x` any number of times,
  then add `z`. So under (X) round 3 is infinite, and a finite exploration
  needs (S) or another bounded reading.

[expected: derived; computed under (S)]

**Q7. Members with the fewest assertions.** Every result has members with
the fewest assertions. Their number of assertions is at least the loop part
plus the return part of Q6's (X) formula, with equality on at most two
terms. On three terms it can exceed it: `xry`, `ysx` has fewest 2 against 0.
Such a member need not be unique: that result has three, one on each pair
of its terms. A result is exact exactly when its fewest is 0.
[expected: derived, computed]

**Q8. The exchange.** Exchanging `r` and `s` changes the sign of every
difference and turns raising a term into its reverse. It is still a symmetry
of the results, the fewest changes and exactness. [expected: derived, Lean]

**Q9. No new level.** No earlier seed in this line (the seventh, the ninth,
the twenty-second) maps one to one into these results. Witness on two
terms: `xry` twice, and `xry` with `yrx`, differ by raising `x`, so they are
one result here, yet they are different results in each of those seeds.
Every result here is the result of some twenty-second result; exactly those
that differ by raising are merged. So this rung repairs within its level:
the pair of maps of the twenty-second's kind is not available, and the run
says so with a witness. [expected: derived, Lean witness]
