# Reading the second seed against the first

Working notes for the second derivation. Nothing here is cited as evidence;
what survived is in `paper/second/paper.md` with its source status.

## The diff

`prompt/second/seed_prompt.md` against `prompt/seed_prompt.md`: one sentence
differs.

    - A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion.
    + A change is exactly one of: identifying two terms; adding a term; adding an assertion.

Every other sentence is identical, character for character (checked with
`diff`). So every reading of the first seed that does not mention removal
carries over word for word, and every proof of the first derivation that does
not use removal still stands — but "does not use removal" has to be checked
per claim, not assumed, because several first-derivation proofs use removal
in the *upper bound* direction (a path that removes what the target lacks).

## Sentence by sentence, only where the meaning moves

### "A change is exactly one of: identifying two terms; adding a term; adding an assertion. Nothing else is a change."

- Nothing un-asserts. Once `xry` is asserted, every later state asserts the
  image of `xry` under the replacements made since (identification maps
  assertions to assertions; additions keep them). So along any sequence of
  changes there is a map of terms `q` (composite of the identifications,
  extended by the identity on added terms) with `q(x) r q(y)` asserted
  whenever `xry` was. Call this the *carrying map* of the sequence. It is the
  single fact from which most of the second derivation follows.
- Consequences to prove:
  * `arb` given, so `q(a) r q(b)` asserted in every result; the result is
    legal, so `q(a) ≠ q(b)`: `a` and `b` are never identified, `arb` is never
    lost (with names). With `bra` given, `bra` is never lost either.
  * An obstruction to identifying `u`, `v` is `urv` or `vru` asserted; it is
    carried to every later state, so identifying the images of `u`, `v` stays
    obstructed for ever. "Remove the obstruction" is not available for any
    obstructed change (for adding `xrx` it never was, D4 of the first paper).
  * The one-term state is unreachable; every result has at least two terms.
  * Fewest classes of a split of the terms with no two related terms in one
    class: never decreases along a change (pull a split of the result back
    along `q`).
- What does *not* follow from monotonicity, and needs witnesses: the number
  of terms can go down (add `c`, identify `a` and `c`: back to what is given);
  the number of assertions can go down (`arc`, `ard`, then identify `c`, `d`);
  a result can be left and returned to (the same witness); reachability
  between results is not antisymmetric (with `bra`: what is given reaches the
  four-term state with `a`, `c` on one side and `b`, `d` on the other, every
  cross pair asserted both ways, and that state reaches what is given back by
  identifying `a`, `c` and `b`, `d`).

### "An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which; ..."

- The seed still names three dispositions (refuse, remove, build), but one of
  them names something no change can do. Readings:
  1. (kept) "remove the obstruction" means un-asserting the assertions that
     would become `xrx` (reading C7 of the first paper); under the second
     seed no change does this, so the answer is refuted for every obstructed
     change, and recorded as such in every attempt log.
  2. (listed, not chosen) "remove the obstruction" means withdrawing the
     change; then it coincides with refusal and adds no result.
  3. (listed, not chosen) "remove" by identification: identifying `u` with a
     third term does not un-assert `urv`, it moves it; the obstruction to the
     identification of the images persists (proved). So this reading has no
     instance either.
  Under any reading in which further changes are changes of the three kinds,
  the results are the same set (the D10 argument of the first paper, minus
  the removal case, which no longer exists).
- Builds for `xrx`: as before, additions only, so they carry over unchanged
  (`build_gives_back`, `build_needs_term_and_assertion` do not mention
  removal). Builds for an obstructed identification: the state itself (C7).

### "Attempt every change, fewest additions first."

- Identifications add nothing; adding a term and adding an assertion add one
  each. Order within a state: identifications, add a term, add assertions —
  the seed's order of kinds. Same protocol as the first derivation minus the
  removal group.

### "For every result, record how many terms and assertions it adds to what is given."

- Under the second seed nothing is ever below what is given: every result has
  at least the two terms and (with names) `arb`. So the recorded additions are
  never negative — a derived fact, where the first derivation had negative
  rows.

### "Two results that differ only in how their terms are written are the same result."

- Both readings (FREE, ANCHORED) kept as before. Under FREE the carrying map
  still exists (names dropped at the end): every result has an asserted pair
  (without `bra`) or a pair asserted both ways (with `bra`).

### "Attempt 100 changes along each alternative ..."

- Every round still has a new result (what is given plus `k` terms is first
  reached in round `k`), so a bound is declared as before. The results of
  round `k` are the legal states containing what is given with `n + m` equal
  to `size(given) + k`: a formula, so the count without bound can be computed
  for early rounds by orbit counting as before.

## Which first-derivation results are used, and how they are re-checked

| First | Used as | Re-check |
|---|---|---|
| D1 (`given_distinct`) | unchanged | statement about a relation, no change mentioned |
| D2 (`two_states_on_given_terms`, `two_states_differ`) | unchanged; "each is one change from the other" is now one-way | `givenA_to_givenB` is an addition (re-proved as a `Step3`); `givenB_to_givenA` is a removal and is refuted under the second seed |
| D3 (`identify_legal_iff`, `addAssertion_legal_iff`, `addTerm_legal`) | unchanged | statements about one state operation each, none is removal |
| D4 (`adding_xrx_always_obstructed`) | unchanged | as above |
| D5 (`obstruction_persists`, `identify_keeps_apart`) | strengthened to sequences | the single-change theorem restricts through the embedding; the sequence version is new (carrying map) |
| D6 (`Step.legal`, `Step.wf`, `Step.nonempty`) | inherited through the embedding `Step3 → Step` | Lean |
| D7 (`names_stay_merged`) | vacuous now (`a = b` never happens) | Lean: unreachable |
| D8 (cost) | replaced: destroyed givens are always zero on reachable states; lower bound `costA ≤ n + 3` still holds through the embedding and implies the new one, but the new one is proved directly | Lean |
| D9 (everything legal is a result) | refuted under the second seed | Lean: `reachable_iff` |
| D10 (answers reach nothing new) | holds, minus the removal answer, which no longer exists | Lean: builds are `Step3` sequences |
| D11 (builds) | unchanged | additions only |
| D12 (completeness, frontier) | same argument | the upper-bound path uses additions only, so it stays within `max(2, terms)` terms |
| K1 (counts) | reused; restricted to states containing what is given | `xry.orbits` unchanged |
| Rewriting step (O3) | needed again | attempted in Lean this time (`rename`) |

## Noticed on the way

- Under the second seed the exploration is contained in the first's: every
  attempt is an attempt of the first derivation, minus the removals. So every
  result within a bound is a first-derivation result within the same bound,
  and the first's per-state data (obstructed identifications etc.) coincide.
- In the concrete Lean model a term can still be "renamed" by two changes
  (add a fresh term, identify it with the old one, the fresh one written
  first). In the end the rewriting lemma (`rename`) was proved instead, so the
  statements are "from some writing of what is given", which is what a result
  up to sameness means.

## Noticed after the computation

- With `bra` given, "passing on" and "never both ways" hold in *no* result:
  `bra` cannot be removed, and `arb`, `bra` with passing on would give `ara`.
  First seen as a failing test expectation; became D15.
- Four terms each asserting the next around to the first (`arb`, `brc`, `crd`,
  `dra`) have no carrying map onto three terms so arranged (`arb`, `brc`, `cra`);
  six terms so arranged do. (Also first seen as a wrong test expectation.)
- Results that return to what is given are rare and shrink with the bound:
  14 of 1 090 (ANCHORED, without `bra`, 4 terms). They are exactly the results
  whose terms can be split into the classes "goes to `a`" and "goes to `b`"
  with every assertion running from the first class to the second (a carrying
  map onto `a b; arb`). Not pursued.
- The first derivation's FREE round-20 count without `bra` exceeds this
  derivation's by exactly one: the state with 22 terms and nothing asserted.
- An ANCHORED run at 5 terms takes 54 s here (90 562 results, 2.3 million
  attempts) and passes every check; its files would be about 90 000 rows per
  alternative, so only a census is recorded (change log item 5).
