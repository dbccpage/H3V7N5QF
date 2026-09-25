# H3 twin 3A ("fill one") prediction, to be frozen before launch

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
  `(y, z)` and `(z, x)`.
- A *member* of a result is a state that is that result.
- A result is *exact* when it is the same as the result with nothing asserted
  on as many terms, with the same terms filled. Otherwise it is a *survivor*.
- A result is *told apart* when some filled term of it does not balance.

## Predictions

**A0. The parent's question.** In the twenty-third, what is recorded for a
result names no term. `a b; ara` and `a b; arb` each record two terms, one
assertion in `r` and none in `s`. Yet they are different results: one is
shown not to be exact by its loop at `a`, the other by its return between
`a` and `b`. So the twenty-third's record does not show which terms keep a
result from being exact. [derived; computed witness]

**A1. Balance is kept by the sameness.** A filled term balances exactly
when its loop's difference is zero. Raising adds no `xrx` and no `xsx`. A
pair asserted together leaves every difference as it was. So whether a
filled term balances is the same on every member of a result, and rewriting
carries it along. "Which filled terms balance" is recorded per result
without a choice of member. [derived, Lean]

**A2. Filling changes the states.** Filled terms are part of the state, and
the sameness names no filling. So `a` and `a` with `a` filled are two
results. The twenty-third's results are exactly the results here with
nothing filled. [derived]

**A3. What a filled term tells.**

- A told-apart result is a survivor, since exact results balance at every
  filled term.
- The converse fails. A survivor can have every term filled and every filled
  term balancing:
  - on two terms, `a b; arb` (its return sums to 1);
  - on three terms, `a b c; arb bsa` (every loop and return sums to zero,
    and the sum around `a, b, c` is 1).
- A survivor can be told apart, by filling some of its terms, exactly when
  one of its loops has a non-zero difference. A survivor whose loops are all
  zero is never told apart, whichever terms are filled.

[derived, witnesses]

**A4. Identifying brings returns onto a loop, and nothing more.** Identify
some terms into one. The merged term's loop has as its difference the sum of
the loops and the returns among the terms merged. That sum is the same on
every member, even where identifying does not respect the sameness.

- Identifying `a` with `b` in `a b; arb` gives a loop with difference 1.
  Filled, it does not balance.
- A sum around three terms never reaches a loop. Identifying any of `a`, `b`,
  `c` in `a b c; arb bsa`, then filling, always balances.

[derived]

**A5. Fewest changes.** The fewest changes to a result are its terms, plus
its filled terms, plus the fewest assertions of any member. This reads a term
as filled at most once; another reading counts fillings. The round of every
result is its fewest changes. The cheapest told-apart result takes three
changes: `a; ara`, with `a` filled. No result with two changes or fewer is
told apart. [derived; computed]

**A6. Readings the run must keep.** The seed does not say what identifying
does to a filled term. Identifying a filled term with an unfilled one gives
a filled term under one reading and an unfilled one under another, so the
results differ, and both are kept. Whether filling a filled term again is a
change is a second point the seed leaves open. [derived; computed]

**A7. The exchange.** Exchanging `r` and `s` negates every loop's difference.
It keeps which filled terms balance. It is a symmetry of the results, their
fewest changes and what is recorded, with the relations exchanged.
[derived, Lean]

**A8. The pair of maps.** The source is the twenty-third.

- Its results map one to one into these results as the results with nothing
  filled, and each of its changes is carried to the same change.
- Forgetting what is filled sends every result here to a twenty-third result
  and returns every mapped result.
- A map back that returns only mapped results answers "none" exactly on the
  results with a filled term. The smallest is one term, filled, with nothing
  asserted: two changes.
- No two twenty-third results become one.

[derived, Lean]

**A9. The order, from this side.** Filling one term tells apart the cheapest
survivors: every survivor on one term, at three changes. It reads loops
only. It never tells apart a survivor whose loops are all zero, such as
`a b; arb` or `a b c; arb bsa`. [derived]
