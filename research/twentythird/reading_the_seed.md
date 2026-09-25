# Reading the twenty-third seed (notes, not evidence)

Inputs: `prompt/twentythird/seed_prompt.md`, `prompt/twentythird/prompt.md`.
Parent: the twenty-second (`paper/twentysecond/`); its parents (the ninth, the
seventh, the eighth, the first) are cited through it.

## 1. Sentence by sentence against the twenty-second seed

`git diff --no-index --word-diff prompt/twentysecond/seed_prompt.md
prompt/twentythird/seed_prompt.md` shows one paragraph touched:

- "Two results that differ only in how their terms are written, ~~or~~ only by
  an `xry` and an `xsy` asserted together, **or only by raising terms,** are the
  same result." — a third clause of sameness.
- "**Raising a term `x` adds `xry` and `ysx` once for every other term `y`.**" —
  new: what raising is.

Every other sentence is the twenty-second's character for character: terms
written with letters; assertions `xry`, `xsy` with multiplicities; adding and
removing move a multiplicity by one; nothing given; the four kinds of change
and "Nothing else is a change"; identifying replaces both terms in every
assertion; fewest additions first; record terms and assertions added; 100
changes per alternative, bound and frontier; any outcome valid.

So: states, the beginning and the changes are the ninth's and the
twenty-second's; only which states are one result changes. Raising is named
in the sameness sentence only; it is not one of the four kinds, and "Nothing
else is a change" keeps it out of the changes.

## 2. What raising does to the excess

The twenty-second showed (its D1) that at a fixed writing its sameness keeps
exactly the number of terms and the excess `e(x, y) = M_r(x, y) − M_s(x, y)` at
every ordered pair. Raising `x` adds one `xry` and one `ysx` for every term
`y ≠ x`: `e(x, y)` rises by one and `e(y, x)` falls by one, for every `y ≠ x`;
nothing else moves (no loop `xrx`, `xsx` is touched: "every other term").
Raising `x` `k(x)` times, for every `x`, moves `e(x, y)` by `k(x) − k(y)`
(for `x = y` this is zero, which is also what happens to loops). Differences
of the form `g(x) − g(y)` are closed under adding and negating, so the
equivalence the three clauses generate should be: equally many terms and,
after one rewriting, excesses differing by `g(x) − g(y)` for whole numbers
`g(x)` (negative `g` reached from the other side: raise the other state).

What is kept under this: every loop's excess; for two terms, `e(x, y) + e(y, x)`
(the two-way sum); for three terms, `e(x, y) + e(y, z) + e(z, x)` (the sum
around); in general the sum around any closed walk. Loops, two-way sums and
three-term sums already decide: if they all vanish on a difference `D`, then
`D(x, y) = D(x, 0) − D(y, 0)` (the sum around `x, y, 0` and the two-way sum at
`0, x`), so `g(x) = D(x, 0)` works.

## 3. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| terms, letters, assertions, relations, multiplicity | given | the ninth's |
| state: terms, a multiplicity per ordered pair per relation | chosen (9:C1′), no change | |
| beginning: no terms, nothing asserted | given | |
| four kinds of change; identifying | given | on states |
| multiplicities of merged pairs add up | chosen (9:C5⁗), no change | |
| a pair asserted together | given, chosen (22:C-J1) | C-J2, C-J3 re-examined |
| raising a term | given (the new sentence), chosen (C-H1) | C-H2, C-H3 |
| sameness of results | given, to be derived | three clauses, equivalence |
| excess | derived (22:D1) | imported |
| the result asserting nothing on `n` terms | the task's words | the class of the state `n` terms, nothing asserted |
| a sum showing a result is not that one | to be derived | loop, two-way, around three terms |
| exploration: states explored, results formed afterwards | the task's words, chosen (C-E) | C-E′ |
| a change of a result | chosen: a change of one of its states (the task's "performing changes on states") | the twenty-second's C-X fails |
| round of a result | chosen: the first round in which one of its states is reached | |
| cost (fewest changes) | to be derived | |
| states asserting the fewest | the task's words | to be characterized |
| record of a result | given (G11), chosen (C-R) | read on a state asserting the fewest |
| mapping an earlier seed in; the map back | the task's words | to be derived |

## 4. Readings

- **C-H1 (chosen).** Raising as the new sentence says; "differ only by raising
  terms": one state is the other with terms raised, any number of times each;
  the sameness is the equivalence the three clauses generate.
- **C-H2 (unchosen).** "Raising terms" as raising all the terms together.
  Raising every term once adds `xry` (from raising `x`) and `xsy` (from raising
  `y`) at every ordered pair of different terms: pairs asserted together. So
  C-H2 adds nothing: its results are the twenty-second's. Different results
  from C-H1 (`a b` and `a b; arb bsa` are one result under C-H1, two under
  C-H2), so kept and computed.
- **C-H3 (unchosen).** Each term raised at most once. Since raising `x` in a
  state that is `x` raised once is `x` raised twice, and sameness is an
  equivalence (transitive), the generated equivalence is C-H1's: eliminated by
  that proof.
- **Set aside.** Raising also adds `xrx` and `xsx`: "every other term" refuses
  it. Raising is a change: "Nothing else is a change" refuses it.
- **The twenty-second's readings of "asserted together".** C-J2 (any `xry`
  with any `usv`): raising adds as many `r` as `s` assertions, so it keeps
  C-J2's invariant `(n, Σ M_r − Σ M_s)` and C-J2 with raising has C-J2's
  results. C-J3 (loops not taken out): raising touches no loop, so loops keep
  both multiplicities and the pairs of different terms are taken modulo
  `g(x) − g(y)`; computed at a small bound.
- **C-E (chosen) / C-E′.** The task: "Explore by performing changes on
  states, as the twenty-second's exploration does, and form the results
  afterwards." The twenty-second's exploration performs changes on its plain
  states (its results). C-E: run it as it is and group what it reaches.
  C-E′: run the ninth's exploration (every state up to writing) and group.
  Expected equal on results and rounds: every result's states asserting the
  fewest are plain, and a plain state is reached by the twenty-second's
  exploration at the round of its size.
- **C-R (chosen).** What is recorded: read on a state of the result asserting
  the fewest. The number of assertions is the same on all of them by
  definition; the split between `r` and `s` is too, because on a plain state
  `Σ M_r − Σ M_s = Σ e`, and `Σ e` over all ordered pairs is kept by raising
  (`Σ (g(x) − g(y)) = 0`).

## 5. Which of the twenty-second's claims this touches

About states and changes, the sameness not mentioned (no change): 22:D3
(first change adds a term; the terms stay positive), the ninth's size moving by
one, `reach_plainSt`, `AddReach`, the undo facts at a fixed writing as
statements about states, the seventh's embedding `ofR` and its changes, the
exchange of relations on states (`Step.swap`, `excess_swap`).

About the twenty-second's results (re-examined): 22:D1 (the sameness — now
coarser), 22:D2 (a change of a result does not depend on the state taken —
expected to fail), 22:D4 (cost — expected to survive only where the plain
state asserts the fewest), 22:D6 (record moves), 22:D7 (which ninth results
stay apart), 22:D8 (the seventh maps one to one — expected to fail), 22:D9
(reachability — expected to survive), 22:D10 (exchange — expected to survive),
22:D11 (counts — expected to fail, new closed forms), 22:D12 (one shortest
sequence per one-term result — one term is untouched by raising), 22:D13
(completeness), 22:D15 (readings), 22:D16 (statements).

## 6. First expectations (to prove or refute)

- `a b; arb bsa` is `a b` raised at `a`: the result asserting nothing on two
  terms. In the twenty-second it was a different result (plain state asserting
  two assertions).
- `a b c; arb bsa` is not the result asserting nothing on three terms: the sum
  around `a b c` is one. So adding a term to two states of one result can give
  two results: the twenty-second's C-X fails.
- Fewest changes: `n` plus the fewest assertions among the result's states.
- `a b; arb arb` and `a b; arb bra` are one result (raise `a` in the second,
  then take out `bra bsa`): different seventh results, so the seventh does not
  map in one to one.
