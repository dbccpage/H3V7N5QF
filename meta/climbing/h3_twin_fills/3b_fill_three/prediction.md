# H3 twin 3B ("fill three") prediction, to be frozen before launch

Written by the operator on 2026-09-25, by hand, from the seed and the
twenty-third's paper and ledger. Nothing here was computed. Its SHA-256 is in
`prediction.sha256` and is committed before the seed is installed. The run's
clone holds no `meta/` and no history. After the run each item is scored
hit, partial or miss against the paper and evidence verbatim, without
editing this file. A miss is a result.

## Words used here

These are H2's words, in `../../h2_raising/prediction.md`.

- The *difference* at an ordered pair `(x, y)` is the multiplicity of `xry`
  minus that of `xsy`.
- A *loop* is the pair `(x, x)`. A *return* between `x` and `y` is the pair
  of `(x, y)` and `(y, x)`, and its sum is the sum of their differences.
- The *sum around* `x, y, z` is the sum of the differences at `(x, y)`,
  `(y, z)` and `(z, x)`. The other way round is the sum around `x, z, y`.
- A *member* of a result is a state that is that result.
- A result is *exact* when it is the same as the result with nothing asserted
  on as many terms, with the same terms filled. Otherwise it is a *survivor*.
- A result is *told apart* when some filled terms of it do not balance.
- The *direct reading* counts, going from `x` to `y`, only the assertions
  written `xry` or `xsy`. The *both-ways reading* also counts `yrx` and
  `ysx`.

## Predictions

**B0. The parent's question.** In the twenty-third, what is recorded for a
result names no term. `a b; ara` and `a b; arb` each record two terms, one
assertion in `r` and none in `s`. Yet they are different results: one is
shown not to be exact by its loop at `a`, the other by its return between
`a` and `b`. So the twenty-third's record does not show which terms keep a
result from being exact. [derived; computed witness]

**B1. Balance is kept by the sameness.** Under the direct reading, three
filled terms balance exactly when the sum around them, the way they are
read, is zero. Under the both-ways reading, they balance exactly when their
three returns sum to zero. Raising a term changes neither sum. A pair
asserted together changes no difference. So which filled terms balance is
the same on every member of a result, and it is recorded per result.
[derived, Lean]

**B2. The seed leaves the way round open.** It does not say whether, going
from `x` to `y`, the assertions written from `y` to `x` count. Nor does it
say whether filling fixes one way round the three terms or reads both. The
readings give different records. `a b c; arb brc cra`, filled at `a`, `b`,
`c`, does not balance going `a, b, c` (three in `r`, none in `s`). It
balances going `a, c, b` under the direct reading. So at least two readings
are kept, with different results. [derived, witness]

**B3. What three filled terms tell.**

- A told-apart result is a survivor, since exact results balance at every
  filling, under every reading.
- Under the direct reading, take a result whose loops and returns all sum
  to zero. It is exact exactly when it is not told apart with every three of
  its terms filled, each way round. That is the twenty-third's criterion: its
  sums around three terms decide.
- Under the both-ways reading, filling three terms reads only returns.
  `a b c; arb bsa` balances there, although it is a survivor.
- Some survivors are never told apart, whichever terms are filled, under
  either reading:
  - every survivor on one or two terms (`a; ara`, `a b; arb`);
  - a loop: `a b c; ara`;
  - returns that cancel around: `a b c; arb bra bsc csb`. Its returns sum
    to 2 and −2, and it balances both ways round `a, b, c`.

[derived, witnesses]

**B4. Identifying inside a filled triple.** Identifying two of three filled
terms leaves fewer than three different terms. No kept reading leaves a
filling on fewer than three different terms. [derived]

**B5. Fewest changes.** The fewest changes to a result are its terms, plus
its fillings, plus the fewest assertions of any member. The round of every
result is its fewest changes. A told-apart result takes at least five
changes: three terms, a filling, and an assertion between two different
terms. Under the direct reading, filled the way round it is read, five
suffice: `a b c; arb` with `a`, `b`, `c` filled. [derived; computed]

**B6. The exchange.** Exchanging `r` and `s` negates every sum. It keeps
which filled terms balance, under both readings. It is a symmetry of the
results, their fewest changes and what is recorded, with the relations
exchanged. [derived, Lean]

**B7. The pair of maps.** The source is the twenty-third.

- Its results map one to one into these results as the results with nothing
  filled, and each of its changes is carried to the same change.
- Forgetting what is filled sends every result here to a twenty-third result
  and returns every mapped result.
- A map back that returns only mapped results answers "none" exactly on the
  results with a filling. The smallest is three terms, filled, with nothing
  asserted: four changes.
- No two twenty-third results become one.

[derived, Lean]

**B8. The order, from this side.** Filling three terms tells apart no
survivor on one or two terms, and it never reads a loop. Its cheapest
told-apart result takes five changes. Under the direct reading, with every
three terms filled, it tells apart every survivor whose loops and returns
all sum to zero, such as `a b c; arb bsa`, which filling one term never
does. [derived]
