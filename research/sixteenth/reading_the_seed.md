# Reading the sixteenth seed against the fourteenth

Working notes for the sixteenth derivation (Phase 1). Nothing here is cited as
evidence; what survived is in `paper/sixteenth/paper.md` with its source status.
Every notion below is exactly one of **given**, **chosen**, **derived**,
**computed**, **refuted**, **open**.

Inputs: `prompt/sixteenth/prompt.md`, `prompt/sixteenth/seed_prompt.md`. Parent
named by the prompt: `paper/fourteenth/paper.md` (a leftover written with a
third letter `ℓ`, inert), and through it `paper/ninth/paper.md` (collapses:
cost is the size, reachability is having a term, one sameness; independence:
jointly free results, cost a sum of the two totals with the terms counted
once, count not a product).

## The diff

`prompt/sixteenth/seed_prompt.md` against `prompt/fourteenth/seed_prompt.md`:
one sentence is replaced, nothing else.

    < A leftover is not an assertion and is not an answer.
    > A recorded leftover `xℓy` may be admitted, adding the assertion `xry`
    > or the assertion `xsy`; an unadmitted leftover is not an assertion.

Every other sentence is identical, character for character (`diff`). So the
sixteenth seed is the ninth's empty beginning, two relations, four kinds and
nothing forbidden, with a leftover recorded after every change — and now a
recorded leftover `xℓy` may be admitted, becoming an assertion of either
relation. "Is not an answer" is gone with the sentence; the seed still has no
obstruction and no answer, so nothing is restored by its absence.

## Sentence by sentence

### (1)–(7) Identical to the fourteenth and the ninth

Terms, assertions `xry` or `xsy` with multiplicity, nothing given, four
kinds, identifying replaces both by one term in every assertion. Given
(G1, G2⁗, G3″, G6, G7). Readings C1′, C3, C5⁗, C9 of the ninth paper,
unchanged in wording — but the *state* cannot stay the ninth's, see (8).

### (8) The record passage, with the feedback

Given (G15′), in the seed's own words:

1. After every change, record what that change leaves.
2. A leftover is written neither `xry` nor `xsy`.
3. A recorded leftover `xℓy` may be admitted, adding the assertion `xry` or
   the assertion `xsy`.
4. An unadmitted leftover is not an assertion.

What the seed does not say: that a leftover has a multiplicity; that
admission is a fifth kind of change (it says the admission *adds the
assertion*, which is the fourth kind); that admission is free; what an
identification leaves (the fourteenth's merge writing is kept); whether an
admitted leftover stays recorded (4 says an unadmitted one is not an
assertion — the admitted one *is* the assertion it added).

**Why the record must be in the state.** Under the fourteenth's C-F1 the
leftover was recorded on the change and the result stayed a ninth state,
"true by construction". Here a recorded leftover may be admitted *later*, by
a change on the result; a writing recorded off the result cannot be reached
by a change on the result. So the unadmitted leftovers are part of the
state, and the question of what they are — a third multiplicity, an
assertion, a change — is no longer free.

**Chosen (C-R1).** A state is a ninth state with its record: a count of
unadmitted leftovers per ordered pair (each removal records one; "record
what that change leaves" is said of every change, so two removals record
two). An admission is a change of the kind "adding an assertion", performed
by admitting; it consumes one recorded leftover of its pair and adds one to
the multiplicity of `xry` or `xsy` — the leftover names no relation
(14:D5), so either. A removal lowers a multiplicity by one and raises the
record by one. An identification carries the record with the terms (the
record of the merged pairs adds up, the fifth's reading reused). The merge
writing of an identification stays on the change (14:C-F1) and is not
admissible (it is not written `xℓy`). An admission leaves nothing. Sameness
rewrites the record with the relations.

**Unchosen, kept, computed.** C-R2: the record is a set. C-R3: an
identification drops the leftovers naming a merged term.

**Set aside.** Admission is not a change (refused by the sentence: it adds
the assertion). An admitted leftover may be admitted again (refused: an
admitted leftover is the assertion it added; there is no unadmitted leftover
left to admit). The merge writing in the result (14:C-F2 cited, not
recomputed).

### Readings that do not change

C2 (nothing given), C4 (one sameness — now on three functions), C5⁗ (four
kinds; admission is of the fourth), C8′ (bound on terms and rounds), C6
(fewest additions first; admissions after the direct additions — an
ordering convention that fixes the log only). C7 stays dropped.

## Expected consequences (checked at the first smoke run)

- Same relation: remove then admit is the identity on the state. Confirmed
  on every removal within 3 terms and 6 rounds (0 failures); fails under
  C-R2 (10 witnesses at 2 terms and 6 rounds), holds under C-R3.
- Other relation: a result different from the start and from the direct
  addition; its ninth state is `asa` from `ara`. Confirmed.
- Potential `size + 2·record` moves by exactly one, up on direct additions
  and removals, down on admissions and identifications; the round of every
  result is its potential; explored counts equal the independent count with
  the third factor `1/(1 − x^{2L})` (2/6: 386; 3/6: 657; 3/8: 10 697).
- Mass and diagonal mass never fall. The carrying criterion agrees with
  search on all 15 876 ordered pairs at 2/5 and 27 889 at 3/5; the ninth's
  criterion admits 10 284 / 17 624 pairs the sixteenth refuses and never
  the reverse.
- The ninth's results are exactly the empty-record results at the same
  rounds with the same shortest-sequence counts.
- Cycles: a term added and identified away (every state with a term);
  remove then admit (every state with an assertion); the ninth's add then
  remove is not a cycle.
- One-term results of round `k`: 0, 1, 2, 4, 6, 9, 12 = the closed form.
- Under C-R3 the ninth's has-a-term criterion agrees with search on every
  pair (a leftover naming a merged term vanishes, so the record can be
  emptied by adding a term and identifying it away); under C-R2 neither
  the ninth's nor the carrying criterion agrees: its criterion is left open.
