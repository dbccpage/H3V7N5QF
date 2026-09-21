# Reading the fourteenth seed against the ninth

Working notes for the fourteenth derivation (Phase 1). Nothing here is cited as
evidence; what survived is in `paper/fourteenth/paper.md` with its source status.
Every notion below is exactly one of **given**, **chosen**, **derived**,
**computed**, **refuted**, **open**.

Inputs: `prompt/fourteenth/prompt.md`, `prompt/fourteenth/seed_prompt.md`. Parent
named by the prompt: `paper/ninth/paper.md` (collapses: cost is the size,
reachability is having a term, one sameness; independence: jointly free
results, cost a sum of the two totals with the terms counted once, count not
a product). The fourteenth seed is the ninth with one passage added: after
every change, record what that change leaves, as a leftover written neither
`xry` nor `xsy`, not an assertion and not an answer.

The tenth seed, if run, grades leftovers as three outcomes of the four kinds.
That grading is **not** in this seed.

## The diff

`prompt/fourteenth/seed_prompt.md` against `prompt/ninth/seed_prompt.md`: one
passage is inserted after the four kinds, nothing else.

    > After every change, record what that change leaves. A leftover is written
    > neither `xry` nor `xsy`. A leftover is not an assertion and is not an
    > answer.

Every other sentence is identical, character for character (`diff`). So the
fourteenth seed is the ninth's empty beginning, two relations, four kinds and
nothing forbidden, with a leftover writing recorded after every change. The
leftover is a third kind of writing (not `xry`, not `xsy`), not an assertion
of either relation, and not an answer to a change.

The task's question: can leftover be identified with an assertion of `r` or
of `s`; is clearing leftover one of the four kinds; is leftover of one
relation leftover of the other; which of the ninth's cost, reachability,
results and count survive once leftover is not an answer.

## Sentence by sentence

### (1)–(7) Identical to the ninth

Terms, assertions `xry` or `xsy` with multiplicity, nothing given, four
kinds, identifying replaces both by one term in every assertion. Given
(G1, G2⁗, G3″, G6, G7). Readings C1′, C3, C5⁗, C9 of the ninth paper,
unchanged. The state is the ninth's (`DState` with `names = None`; Lean
`NDSt`). The beginning is the empty state. One reading of sameness (9:D12).
No obstruction, no answer, no refusal (dropped from the sixth on; this seed
says leftover is not an answer, so it does not restore the first seed's
answers).

### (8) The new passage: leftover as a writing

Given (G15). Four claims in the seed's own words:

1. After every change, record what that change leaves.
2. A leftover is written neither `xry` nor `xsy`.
3. A leftover is not an assertion.
4. A leftover is not an answer.

The seed does not say leftover is a multiplicity, a third relation, or a
field of the result. It does not say leftover is counted among "terms and
assertions added to what is given". It does not name a fifth kind of change
that would act on leftover. It does not grade leftovers as the tenth's three
outcomes.

**Chosen (C-F1).** Leftover is recorded on the change (the attempt), not as
a field of the result. A result remains a two-relation state up to sameness
(C6, the ninth's). The leftover writing of a change from `S` to `T` is:

- If the change is an addition (a term, or an assertion of either relation):
  the added thing is a term or an assertion, so the leftover writing is
  **nothing** (not `xry`, not `xsy`).
- If the change is a removal of an assertion of a pair `(x, y)` in either
  relation: what is left is that pair, written `xℓy` with a third letter
  `ℓ` that is neither `r` nor `s`. The writing names no relation.
- If the change is an identification of terms `u` and `v`: what is left is
  those two terms, written `u∼v`, not an assertion.

**Unchosen, kept (C-F2).** The leftover writing is a field of the result,
replaced by each later change. The beginning is tagged nothing.

### Readings that do not change

C2 (nothing given), C4 (one sameness), C5⁗ (four kinds; leftover is not a
fifth), C8′ (bound on terms and rounds). C7 remains dropped (no obstruction).

## Expected consequences

- Leftover cannot be identified with an assertion of `r` or of `s` (given:
  written neither `xry` nor `xsy`; leftover is not an assertion).
- Clearing leftover is not one of the four kinds (leftover is not a term
  and not an assertion; leftover is not an answer; nothing else is a
  change). Adding the corresponding `xry` after a removal restores the
  *state* (the tenth's "clear", a fact about states, not about leftover
  writings) and does not act on leftover as leftover.
- Leftover of a removal in `r` of a pair is the same leftover writing as
  leftover of a removal in `s` of that pair (`xℓy` names no relation). So
  leftover of one relation *is* leftover of the other, as writings.
- Under C-F1 the ninth's cost, has-a-term criterion, jointly free results
  and non-product count survive (identity on states and changes).
- Under C-F2 they do not as a count of results (same state, different
  leftover writings; cost of a tagged one-term state can exceed its size).
