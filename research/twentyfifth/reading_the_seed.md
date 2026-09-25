# Reading the twenty-fifth seed (notes, not evidence)

Inputs: `prompt/twentyfifth/seed_prompt.md`, `prompt/twentyfifth/prompt.md`.
Parent: the twenty-third (`paper/twentythird/`); its parents (the
twenty-second, the ninth, the seventh, the eighth, the first) are cited through
it. The twenty-fourth is a sibling and is not read.

## 1. Sentence by sentence against the twenty-third seed

`git diff --no-index --word-diff prompt/twentythird/seed_prompt.md
prompt/twentyfifth/seed_prompt.md` shows one paragraph touched:

- "A change is exactly one of: identifying two terms; removing an assertion;
  adding a term; adding an ~~assertion.~~ **assertion; filling three different
  terms.**" — a fifth kind of change.
- "**Three filled terms `x`, `y`, `z` balance when, going from `x` to `y` to
  `z` and back to `x`, as many assertions are written with `r` as with `s`,
  each counted as often as it is asserted; for every result, record which
  filled terms balance.**" — new: what balancing is, and a record.

Every other sentence is the twenty-third's character for character, the
sameness sentence with raising included; "Nothing else is a change" and
"Identifying two terms replaces both by one term in every assertion" stay.

So: the seed names a new kind of change without saying what it does to a
state beyond the word "filled", and a property of filled terms (balance) with
a record. The states, the empty beginning, the four kinds and the sameness are
the twenty-third's.

## 2. What balance is, on the excess

Going from `x` to `y`, the assertions written are `xry` (with `r`) and `xsy`
(with `s`), each as often as asserted: the difference is the excess
`e(x, y) = M_r(x, y) − M_s(x, y)`. Around `x → y → z → x`: the triple balances
exactly when `e(x, y) + e(y, z) + e(z, x) = 0` — the twenty-third's *sum
around three terms*, which its sameness keeps (23:D2, `Same3.around`). So which
filled triples balance is the same on every state of a result: the record the
seed asks for is a record of the result. Going round the other way gives
`e(x, z) + e(z, y) + e(y, x)`; the two add up to the three two-way sums, so
they are different sums unless the two-way sums around add up to zero.

## 3. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| terms, letters, assertions, relations, multiplicity | given | the ninth's |
| state: terms, a multiplicity per ordered pair per relation | chosen (9:C1′), no change | |
| filled triples of a state | given (the word "filled"), chosen (C-F1) | C-F2 unchosen |
| filling three different terms | given (the fifth kind), chosen (C-F1, C-O1, C-M1) | C-O2–C-O4, C-M2 |
| identifying, with filled triples | given (G7) for assertions; chosen (C-I1) for filled triples | C-I2, C-I3 |
| balance of three filled terms | given, chosen (C-B1: the way round, `xqy` along `x → y`) | C-B2 |
| record of which filled terms balance | given | a record of the result (§2) |
| sameness of results | given (the twenty-third's sentence), chosen: a rewriting carries the filled triples | |
| result asserting nothing on as many terms | the task's words | the twenty-third's, with any filled triples |
| terms keeping a result from being that one | the task's words, chosen | least sets of terms whose restriction is not nothing |
| told from one by filled terms that do not balance | the task's words, chosen | the records differ |
| cost | to be derived | |
| an earlier seed mapped in; the map back; what a merge loses | the task's words | to be derived |

## 4. Readings

- **C-F1 (chosen)** / **C-F2**: filling marks three terms as filled, in the
  state / on the change only. C-F2 leaves every state as it was: its results
  and rounds are the twenty-third's (a filling is then a change that returns
  its state; no sequence is shortened by it), and "for every result, record
  which filled terms balance" has no filled terms of a result to read — kept,
  with that noted.
- **C-O1 (chosen)**: the order of going round is kept (`x, y, z` = `y, z, x`;
  `x, z, y` another triple). **C-O2**: a set, balancing both ways round.
  **C-O3**: a set, balancing either way round. **C-O4**: ordered, each start a
  different triple.
- **C-B1 (chosen)**: along `x → y` count `xry` and `xsy`. **C-B2**: count the
  assertions between `x` and `y` either way — balance is then "the two-way sums
  around add up to zero", which sees no loop and no part of the excess that
  raising can move.
- **C-M1 (chosen)** / **C-M2**: filled or not / counted.
- **C-I1 (chosen)**: identifying carries the filled triples, dropping the
  ones left without three different terms, merging the ones that become one.
  **C-I2**: drops every triple naming either term. **C-I3**: keeps the
  degenerate ones (then a filled triple is never lost, and the twenty-third's
  reachability fails).
- **C-A (chosen)**: fillings attempted with the changes adding nothing
  (after the removals, before a term); unchosen, last.
- **C-R (chosen)**: the twenty-third's record plus the balance record;
  unchosen, filled triples counted among what is added.

## 5. Which of the twenty-third's claims this touches

About states and the four kinds (no change or imported): the excess, the
sums kept by the sameness (23:D2), the cost of the assertions (23:D5), the
states asserting the fewest (23:D7), the record (23:D8), raising.

About results (re-examined): the sameness now carries filled triples; the
cost gains the filled triples; the parity of the cost (23:D6) — identifying
can drop filled triples, so the cost can move by an even number; reachability
(23:D12) — re-proved with filled triples (identifying down to one term drops
them all under C-I1); the exchange (23:D13) — negates every sum around, so a
triple balances in a state exactly when it does in its exchange; the map from
the twenty-third (D9 there found none of the earlier seeds one to one; here
the twenty-third itself maps in with nothing filled); the counts (23:D14).

## 6. First checks (`scratch_rank.py`)

- Ranks of the sums around every filled triple, on excess tables modulo the
  moves `g(x) − g(y)`: with 3 terms 2 (of 7 dimensions: 3 loops and 2 more
  unseen); with 4 terms 7 (of 13: 4 loops and 2 more unseen); with 5 terms 16
  (of 21: only the 5 loops unseen); with 6 terms 25 (of 31: only the loops).
  So a result that no filling can tell from nothing: with five terms or more,
  one differing from nothing only at loops.
- Antisymmetric excess (every two-way sum zero): the sums around decide it
  exactly when their rank is `C(n − 1, 2)`: with 3 terms one triple; with 4
  terms exactly the sets holding three of the four triples; with 5 terms 125
  of the 210 sets of six triples, and every set of eight.
- `a b c; arb arc csb csa` (two-way sums 1, −1, 0) balances both ways round:
  a three-term result with a non-zero two-way sum that no filling tells.

## 7. Timing (`time_explore.py`)

The exploration of states with filled triples, grouped: 5 terms and 8 rounds
9 573 results in 8 s; 3 terms and 10 rounds 29 883 results in 32 s; 2 terms
and 8 rounds 226 results (the twenty-third's figure: nothing can be filled with
two terms). Every round equals the cost by formula (the twenty-third's cost of
the assertions plus the filled triples). So the twenty-third's bounds (5/8,
3/10, 2/24) are used, above the plan's 4/7 and 3/9.
