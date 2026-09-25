# Reading the twenty-fourth seed (notes, not evidence)

Inputs: `prompt/twentyfourth/seed_prompt.md`, `prompt/twentyfourth/prompt.md`.
Parent: the twenty-third (`paper/twentythird/`); its parents (the
twenty-second, and through it the ninth, the seventh, the eighth, the first)
are cited through it. The twenty-fifth is a sibling, not an input.

## 1. Sentence by sentence against the twenty-third seed

`git diff --no-index --word-diff prompt/twentythird/seed_prompt.md
prompt/twentyfourth/seed_prompt.md` shows one paragraph touched:

- "A change is exactly one of: identifying two terms; removing an assertion;
  adding a term; adding an ~~assertion.~~ **assertion; filling one term.**" — a
  fifth kind of change.
- "**A filled term `x` balances when `xrx` and `xsx` are asserted equally
  often; for every result, record which filled terms balance.**" — new: when a
  filled term balances, and a record.

Every other sentence is the twenty-third's character for character: terms and
letters; assertions `xry`, `xsy` with multiplicities; adding and removing move
a multiplicity by one; nothing given; "Nothing else is a change"; identifying
replaces both terms in every assertion; fewest additions first; record the
terms and assertions added; the sameness sentence with its three clauses;
raising; 100 changes per alternative, bound and frontier; any outcome valid.

What the seed does not say: what filling does to a state beyond making the
term filled; whether a filled term can be filled again; what identifying does
to filled terms; whether two results differing in which terms are filled are
one result (the sameness sentence does not mention filled terms, so no clause
joins them); where filling stands among "fewest additions first".

## 2. What "balances" reads on a result

`x` balances when `M_r(x, x) = M_s(x, x)`: the loop's excess
`e(x, x) = M_r(x, x) − M_s(x, x)` is zero. The twenty-third showed that a
loop's excess is kept by every clause of its sameness (23:D2, `Same3.loop`):
pairs asserted together add one to both multiplicities, raising touches no
loop ("every other term"), and a rewriting carries the loop with its term. So
whether a filled term balances does not depend on which state of the result
is read, provided the filled terms are carried along by the rewriting — the
record is a record of the result.

## 3. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| terms, letters, assertions, relations, multiplicity | given | the ninth's |
| state: the twenty-third's (terms, a multiplicity per ordered pair per relation) and its filled terms | chosen (C-F1, C-S) | the filled terms are among the terms |
| beginning: no terms, nothing asserted, nothing filled | given | nothing is filled since there is no term |
| five kinds of change | given | "filling one term" new |
| what filling does | chosen (C-F1) | C-F1′, C-F2, C-F3, C-F4 |
| what identifying does to filled terms | chosen (C-I1) | C-I2, C-I3 |
| sameness of results | given (the twenty-third's sentence), chosen (C-S) | filled terms carried by the rewriting |
| a filled term balances | given | derived: a property of the result |
| the record of which filled terms balance | given, chosen (C-B) | at the least writing |
| the twenty-third's record | given (G11), chosen (23:C-R) | kept |
| "a result with nothing asserted on as many terms" | the task's words, chosen (C-N) | C-N0 |
| "the terms that keep it from being that result" | the task's words, chosen (C-K) | loops, two terms, three terms (23:D2) |
| told apart by filled terms that do not balance | the task's words | to be derived |
| exploration of states, results formed afterwards | the task's words, chosen (23:C-E) | C-E′ |
| order of the attempts | given ("fewest additions first"), chosen (C-O) | fillings with the changes that add nothing |
| cost (fewest changes) | to be derived | |
| mapping an earlier seed in; the map back; what a merge loses | the task's words | to be derived |

## 4. Readings

- **C-F1 (chosen).** Filling `x` makes `x` filled; nothing asserted changes.
  Filling a filled term changes nothing and is not a change (as removing what
  is not asserted is not, 9:C5⁗). **C-F1′**: it is a change whose outcome is
  its start — it reaches nothing new, so the results and rounds are C-F1's.
- **C-F2.** A term filled a number of times. Different results (filled once,
  filled twice). Kept; computed at a small bound. "A filled term" names a
  property, and the seed says "a number of times" of assertions only, which is
  why it is not chosen.
- **C-F3.** Filling `x` also asserts `xrx` and `xsx`, once each: a pair
  asserted together, so the outcome is C-F1's result. Eliminated by that proof.
- **C-F4.** Filling `x` makes it balance (adds the missing `xrx` or `xsx`).
  Then a filled term balances when it is filled, and can stop balancing when a
  loop is added later. Kept and computed; expected the same results and costs.
- **C-S (chosen).** A rewriting carries filled terms; the other clauses do not
  touch them; results differing in their filled terms are two results. Set
  aside: filled terms as a record of the sequence (refused by "for every
  result, record which filled terms balance").
- **C-I1 (chosen) / C-I2 / C-I3.** The one term of an identification is filled
  when either was / only when both were / never.
- **C-B (chosen).** The record: which filled terms balance, at the result's
  least writing, and the two numbers (balancing, not balancing).
- **C-N (chosen) / C-N0.** "A result with nothing asserted on as many terms":
  the same filled terms / none filled.
- **C-K (chosen).** The terms that keep a result from being the one asserting
  nothing: the smallest sets of terms on which it is not — a loop, two terms,
  three terms (23:D2).
- **C-O (chosen).** Fillings after the removals and before adding a term.

## 5. Which of the twenty-third's claims this touches

About states and changes, filled terms not involved (no change, or imported
through the embedding of the twenty-third's states with nothing filled): the
twenty-second's `phi`, `reach_plainSt`, `Step.phi_le`; the twenty-third's
raising and `Same3`, the sums kept (`Same3.loop`, `twoWay`, `around`),
`same3_nothing_iff`, `Cost3`, `cost3_iff`, `cost3_two`, the witnesses of D4 and
D9.

About results (re-examined): 23:D5 (cost — expected to gain the filled
count), 23:D6 (parity — expected to fail for identifications of two filled
terms under C-I1), 23:D12 (reachability — expected to fail under C-I1), 23:D13
(exchange — expected to hold), 23:D14 (counts — new with filled terms), 23:D8
(record — kept, and asked about by the task), 23:D9/D10 (maps — the
twenty-third itself now maps in one to one).

## 6. First expectations

- The twenty-third's record `(2, 1, 0)` is shared by `a b; ara` and `a b; arb`;
  the first is kept from the result asserting nothing by the loop at `a`, the
  second only by `a` and `b` together. So it does not show which terms.
- A filled term that does not balance has a loop of non-zero excess: a single
  term showing the result is not the one asserting nothing. Two terms or three
  terms never show up in balance.
- `a b; arb` with both terms filled: both balance, and it is not the result
  asserting nothing; identifying `a` and `b` gives `a; ara` with `a` filled,
  which does not balance.
- `a b` both filled costs 4; identified, `a` filled costs 2: an even move.
