# Reading the eleventh seed against the ninth

Working notes for the eleventh derivation (Phase 1). Nothing here is cited as
evidence; what survived is in `paper/eleventh/paper.md` with its source status.
Every notion below is exactly one of **given**, **chosen**, **derived**,
**computed**, **refuted**, **open**.

Inputs: `prompt/eleventh/prompt.md`, `prompt/eleventh/seed_prompt.md`. Parent
named by the prompt: `paper/ninth/paper.md` (collapses: cost is the size,
reachability is having a term, one sameness; independence: jointly free
results, cost a sum of the two totals with the terms counted once, count not
a product). The eleventh seed is the ninth with one passage added: a writing
of terms may give two terms the same letter while they remain two terms, and
assertions are read from the writing.

The tenth seed's leftover passage is not in this seed. The tenth is a
sibling, not a parent: both sit on the ninth.

## The diff

`prompt/eleventh/seed_prompt.md` against `prompt/ninth/seed_prompt.md`: one
passage is inserted after the four kinds, nothing else.

    > A writing of terms may give two terms the same letter while they remain
    > two terms. Assertions are read from the writing. If two terms are
    > written the same and their assertions differ, the writing does not
    > determine the assertions.

Every other sentence is identical, character for character (`diff`). So the
eleventh seed is the ninth's empty beginning, two relations, four kinds and
nothing forbidden, with a writing that can collide terms it does not
identify. Identifying is still a change of the four kinds; writing is not a
fifth kind.

The task's question: when the writing determines the assertions; what a
collision (same writing, different assertions) forbids of every coarser
writing; whether a collision in one relation constrains the other; which of
the ninth's cost, reachability, results and count survive once writing and
identifying are two different things.

## Sentence by sentence

### (1)–(7) Identical to the ninth

Terms, assertions `xry` or `xsy` with multiplicity, nothing given, four
kinds, identifying replaces both by one term in every assertion. Given
(G1, G2⁗, G3″, G6, G7). Readings C1′, C3, C5⁗, C9 of the ninth paper,
unchanged. The state is the ninth's (`DState` with `names = None`; Lean
`NDSt`). The beginning is the empty state. One reading of sameness (9:D12).
No obstruction, no answer, no leftover (the tenth's G15 is not here).

### (8) The new passage: writing

Given (G16). Four claims in the seed's own words:

1. A writing of terms may give two terms the same letter while they remain
   two terms.
2. Assertions are read from the writing.
3. If two terms are written the same and their assertions differ, the
   writing does not determine the assertions.
4. (implicit, from (1)) writing is not identifying: the two terms remain.

The seed does not say a writing is a multiplicity, a third relation, or a
field of the result. It does not name a fifth kind of change that would act
on a writing. It does not say a colliding writing is forbidden (G14: any
outcome is valid). "Assertions are read from the writing" means the written
form is letter–relation–letter.

**Chosen (C-W1).** A writing is a function from a result's terms to letters,
recorded as a reading of the result, not as a field of it. A result remains
a two-relation state up to sameness (C6, the ninth's). The writing
*determines* the assertions exactly when, in each relation, the multiplicity
is constant on every rectangle of pairs of terms that share a pair of
letters: the written assertion `L q K` then has one multiplicity. A
*collision* is a writing that does not determine (equivalently: two terms
the same letter whose assertions, read by letters, differ). A writing `w'`
is *coarser* than `w` when it writes together every pair `w` writes
together, and possibly more.

Unchosen, kept (C-W2): the writing (up to renaming letters) is part of the
result — a labeled state. Then a ninth state may be several results, one
per writing of its terms. Expected to give a larger count. Computed
separately; not chosen, because the seed says two results that differ only
in how their terms are written are the same result, and records the writing
as a reading ("assertions are read from the writing"), not as what a result
adds to what is given (terms and assertions).

Unchosen, not a third relation: reading a writing as a multiplicity function
on ordered pairs, a third copy of `r`. The seed says a writing of *terms*
(letters), and a leftover-style third assertion is not given; this reading
is eliminated.

Unchosen, not identifying: reading "written the same" as the identification
change. The seed says they remain two terms, so this reading is refuted.

### (9)–(14) Identical to the ninth

Attempt every change, fewest additions first; record terms and assertions
added; sameness by writing; 100 changes, bound and frontier; any outcome is
valid. Given (G11–G14). C6, C8′ unchanged in kind. A writing is not among
the terms and assertions recorded for a result (C-W1). Bounds: writing
classification on the ninth's explorations at the eleventh's declared
bounds; the unchosen labeled reading at a small bound.

## Expected consequences

To be proved or refuted.

1. An injective writing always determines the assertions (no two terms share
   a letter).
2. If a writing does not determine, neither does any coarser writing. That
   is what a collision forbids of every coarser writing.
3. A collision in one relation need not be a collision in the other: two
   terms written the same, `xry` asserted and nothing with `s`, fails to
   determine `r` and determines `s`. So a collision of one relation does
   not constrain the other.
4. Writing is not identifying: colliding two terms leaves both; identifying
   them leaves one.
5. Under C-W1 the ninth's cost (the size), has-a-term reachability, jointly
   free results and non-product count survive: the states and the changes
   are the ninth's. Under C-W2 the count of results is larger (one ninth
   state, several writings).
6. The first seed's obstruction is not restored: every change is performed;
   a colliding writing is not a bar.
