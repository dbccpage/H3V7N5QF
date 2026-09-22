# Reading the fifteenth seed against the ninth

Working notes for the fifteenth derivation (Phase 1). Nothing here is cited as
evidence; what survived is in `paper/fifteenth/paper.md` with its source status.
Every notion below is exactly one of **given**, **chosen**, **derived**,
**computed**, **refuted**, **open**.

Inputs: `prompt/fifteenth/prompt.md`, `prompt/fifteenth/seed_prompt.md`. Parent
named by the prompt: `paper/ninth/paper.md` (collapses: cost is the size,
reachability is having a term, one sameness; independence: jointly free
results, cost a sum of the two totals with the terms counted once, count not
a product). The fifteenth seed is the ninth with one passage added: a result
of the changes is reached; whether it is admitted is not given by the
reaching; record for every result whether it is admitted; reaching a result
does not make it admitted.

The tenth leftover grading, the eleventh colliding writing, the twelfth
identification record, the thirteenth coarser writing and the fourteenth
leftover-as-writing are **not** in this seed.

## The diff

`prompt/fifteenth/seed_prompt.md` against `prompt/ninth/seed_prompt.md`: one
passage is inserted after the four kinds, nothing else.

    > A result of the changes is reached. Whether it is admitted is not given
    > by the reaching. Record for every result whether it is admitted.
    > Reaching a result does not make it admitted.

Every other sentence is identical, character for character (`diff`). So the
fifteenth seed is the ninth's empty beginning, two relations, four kinds and
nothing forbidden, with an admission record on every result that reaching
does not give.

The task's question: is admission independent of the two relations; can
every reached result be admitted; does an admitted result in one relation
constrain the other; which of the ninth's cost, reachability, results and
count survive once reaching does not admit.

## Sentence by sentence

### (1)–(7) Identical to the ninth

Terms, assertions `xry` or `xsy` with multiplicity, nothing given, four
kinds, identifying replaces both by one term in every assertion. Given
(G1, G2⁗, G3″, G6, G7). Readings C1′, C3, C5⁗, C9 of the ninth paper,
unchanged. The state is the ninth's (`DState` with `names = None`; Lean
`NDSt`). The beginning is the empty state. One reading of sameness (9:D12).
No obstruction, no answer, no refusal (dropped from the sixth on). Admitting
is not a fifth kind (G6: nothing else is a change).

### (8) The new passage: reaching does not admit

Given (G15). Four claims in the seed's own words:

1. A result of the changes is reached.
2. Whether it is admitted is not given by the reaching.
3. Record for every result whether it is admitted.
4. Reaching a result does not make it admitted.

The seed does not say admission is a multiplicity, a third relation, or a
field of the result. It does not say admission is counted among "terms and
assertions added to what is given". It does not name a fifth kind of change
that would admit. It does not say admission is of one relation rather than
of the result. It does not say a reached result cannot be admitted: it says
reaching does not *make* it admitted, so the record is independent of the
path.

**Chosen (C-A1).** Admission is recorded with the result as extra data, not
as a field of the two-relation state. A result remains a two-relation state
up to sameness (C6, the ninth's). Reaching leaves the record as
not-admitted. Every reached result can be admitted by a record that is not
one of the four kinds. Admission names no relation, so it is independent of
`r` and of `s`.

**Unchosen, kept (C-A2).** The admission record is a field of the result.
The unadmitted and admitted copies of one ninth state are different results.
Reaching still lands on the unadmitted copy; recording admission (not a
change of the seed) produces the admitted copy.

## Expected consequences

- Admission is not an assertion of `r` or of `s`.
- Admitting is not one of the four kinds.
- Every reached result can be admitted.
- Admission of one relation does not constrain the other (there is no
  per-relation admission).
- Under C-A1 the ninth's cost, has-a-term criterion, jointly free results
  and non-product count survive.
- Under C-A2 they do not as a count of results; the admitted one-term state
  costs 2 against size 1.
