# Reading the tenth seed against the ninth

Working notes for the tenth derivation (Phase 1). Nothing here is cited as
evidence; what survived is in `paper/tenth/paper.md` with its source status.
Every notion below is exactly one of **given**, **chosen**, **derived**,
**computed**, **refuted**, **open**.

Inputs: `prompt/tenth/prompt.md`, `prompt/tenth/seed_prompt.md`. Parent named
by the prompt: `paper/ninth/paper.md` (collapses: cost is the size,
reachability is having a term, one sameness; independence: jointly free
results, cost a sum of the two totals with the terms counted once, count not
a product). The tenth seed is the ninth with one passage added: after every
change, record what that change leaves.

## The diff

`prompt/tenth/seed_prompt.md` against `prompt/ninth/seed_prompt.md`: one
passage is inserted after the four kinds, nothing else.

    > After every change, record what that change leaves. A leftover is not
    > an assertion. Nothing left, a leftover that a later change of the four
    > kinds can clear, and a leftover that none of them can, are three
    > outcomes. Declare which, for every change.

Every other sentence is identical, character for character (`diff`). So the
tenth seed is the ninth's empty beginning, two relations, four kinds and
nothing forbidden, with a leftover outcome recorded on every change. The
first seed had a forbidden `xrx` and a binary obstruction; the sixth dropped
both. This seed does not restore a forbidden pair and does not restore an
answer. It records, after every performed change, one of three leftover
outcomes, and a leftover is not an assertion.

The task's question: is a leftover a third kind of record beside the two
relations; do the three outcomes split the ninth's changes; does a leftover
of one relation constrain the other; which of the ninth's cost,
reachability, results and count survive once every change carries an
outcome.

## Sentence by sentence

### (1)–(7) Identical to the ninth

Terms, assertions `xry` or `xsy` with multiplicity, nothing given, four
kinds, identifying replaces both by one term in every assertion. Given
(G1, G2⁗, G3″, G6, G7). Readings C1′, C3, C5⁗, C9 of the ninth paper,
unchanged. The state is the ninth's (`DState` with `names = None`; Lean
`NDSt`). The beginning is the empty state. One reading of sameness (9:D12).
No obstruction, no answer, no refusal (dropped from the sixth on; not
reintroduced by leftover).

### (8) The new passage: leftover

Given (G15). Four claims in the seed's own words:

1. After every change, record what that change leaves.
2. A leftover is not an assertion.
3. Three outcomes: nothing left; a leftover that a later change of the four
   kinds can clear; a leftover that none of them can.
4. Declare which, for every change.

The seed does not say leftover is a multiplicity, a third relation, or a
field of the result. It does not say leftover is counted among "terms and
assertions added to what is given". It does not name a fifth kind of change
that would act on leftover. "A later change of the four kinds" is one of
identifying, removing an assertion, adding a term, adding an assertion.

**Chosen (C-L1).** Leftover is recorded on the change (the attempt), not as
a field of the result. A result remains a two-relation state up to sameness
(C6, the ninth's). The leftover of a change from `S` to `T` is declared as
follows.

- If the change is an addition (a term, or an assertion of either relation):
  the added thing is a term or an assertion, so **nothing left**. (Even when
  a later change restores `S` — adding a term from a state with a term is
  often undone by identifying the new term with an old one — nothing was
  leftover: the effect is in the state as a term or an assertion.)
- If the change is a removal: what is gone is not an assertion (it is the
  lowering of a multiplicity). Adding that same assertion is a later change
  of the four kinds that restores `S`. So **a leftover that a later change
  can clear**. A change of the other relation does not restore `S`.
- If the change is an identification: the two terms as two are gone; that
  distinctness is not an assertion. If some one later change of the four
  kinds restores `S` (up to writing of the terms), the leftover **can be
  cleared**; otherwise **none of them can**. Expected: identifying two terms
  in a state that asserts nothing is cleared by adding a term (the result
  is the same up to writing); identifying two terms that had an assertion
  between them is not cleared by any one later change (adding a term does
  not un-merge the multiplicities).

Unchosen, kept (C-L2): leftover status is part of the result — a
three-valued tag, the leftover of the incoming change, the beginning tagged
"nothing left". Then a ninth state may be several results. Expected to give
different results, a cost that is not the size, and a count that is not the
ninth's. Computed separately; not chosen, because the seed records leftover
after every *change* and says a leftover is not an assertion, while a result
is still recorded by terms and assertions added to what is given.

Unchosen, not a third relation: reading leftover as a multiplicity function
on ordered pairs, a third copy of `r`. The seed says a leftover is not an
assertion, so this reading is eliminated (refuted as a reading of the seed,
not as a possible extra structure).

### (9)–(14) Identical to the ninth

Attempt every change, fewest additions first; record terms and assertions
added; sameness by writing; 100 changes, bound and frontier; any outcome is
valid. Given (G11–G14). C6, C8′ unchanged in kind. Leftover is not among
the terms and assertions recorded for a result (C-L1). Bounds: leftover
classification on the ninth's explorations at the tenth's declared bounds
(lower than the ninth's 5-term run if a run does not finish in minutes);
the unchosen tagged reading at a small bound.

## Expected consequences

To be proved or refuted.

1. Leftover is not a third multiplicity beside `r` and `s` under C-L1. It is
   a classification of the ninth's changes. (Task: "whether a leftover is a
   third kind of record beside the two relations" — no, under C-L1; yes as
   a tag, under C-L2, which is not a relation.)
2. The three outcomes split the ninth's changes: additions leave nothing;
   removals leave a clearable leftover; identifications leave a leftover
   that is clearable or not according as a later change restores the start.
   All three outcomes are inhabited.
3. A leftover of a removal in one relation is cleared only by adding that
   assertion in the same relation. It does not constrain later changes of
   the other relation (the ninth's list of changes on the other part is
   unchanged). An identification leftover is not of one relation
   (identification acts on both).
4. Under C-L1 the ninth's cost (the size), has-a-term reachability, jointly
   free results and non-product count survive: the states and the changes
   are the ninth's. Under C-L2 they do not (witnesses at the one-term state
   asserting nothing, reached with more than one tag, and at a tagged result
   whose fewest changes exceed its size).
5. The first seed's obstruction is not restored: every change is performed;
   leftover is three-way and is not a bar.
6. The exchange of the two relations carries leftover with the relations
   (a removal in `r` becomes a removal in `s`).
