# Reading the ninth seed against the eighth and the seventh

Working notes for the ninth derivation (Phase 1). Nothing here is cited as
evidence; what survived is in `paper/ninth/paper.md` with its source status.
Every notion below is exactly one of **given**, **chosen**, **derived**,
**computed**, **refuted**, **open**.

Inputs: `prompt/ninth/prompt.md`, `prompt/ninth/seed_prompt.md`. Parents named
by the prompt: `paper/seventh/paper.md` (collapses: cost is the size,
reachability is having a term, one sameness — 7:D4, 7:D8, 7:D12) and
`paper/eighth/paper.md` (independence: results a product, cost a sum, count
not a product — 8:D5, 8:D4, 8:D10). The ninth seed turns both dials of the
sixth at once: the eighth's second relation with the seventh's empty
beginning.

## The diffs

`prompt/ninth/seed_prompt.md` against `prompt/eighth/seed_prompt.md`: one
passage changes, nothing else.

    < Given:
    <
    < - `arb` is asserted with multiplicity one.
    <
    < Whether `bra`, or anything written with `s`, is asserted is not given.
    > Nothing is given: to begin with there are no terms and nothing is asserted.

Against `prompt/seventh/seed_prompt.md` one sentence changes:

    < Terms are written with letters. An assertion is written `xry`, where `x` and `y` are terms; …
    > Terms are written with letters. An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; …

Every other sentence is identical, character for character (`diff`). Against
the sixth seed those two passages together are the only differences. So the
ninth seed is the sixth seed's counted states, four kinds of change and
nothing forbidden, with the eighth's second relation and the seventh's empty
beginning: no `a`, no `b`, no `arb`, no `bra`; two relations `r` and `s`,
neither given anything. The ninth seed never uses the words `a`, `b`, `arb`,
or `bra`. It has no residual "whether … is not given" list: it states that
nothing is given. The relations `r` and `s` appear only in the
assertion-writing sentence; they are not named as given data.

The task's question: do the seventh's collapses (cost = size, reachability =
has a term, one sameness) and the eighth's independence (results a product,
cost a sum, count not a product) hold together, and where do they interfere?

## Sentence by sentence

### (1) "Terms are written with letters."

Given (G1; every earlier seed). Terms are things that get written; the
writing is not the term (later: "differ only in how their terms are written").
Supply of letters: not capped (chosen, C3, as 1:C3 to 8:C3). Harmless: the
sequences used to reach a result never have more terms than the result, and
a sequence between two results with a term uses at most `max(terms) + 2` (the
eighth's path through the naming map).

### (2) "An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity."

Given (G2; the eighth's G2⁗, replacing the seventh's G2‴). An assertion has
a first term, a second term, and one of the two relations. Order matters
(derived, not chosen: `xry` and `yrx` are different writings; the seed
writes both). Multiplicity is given (the fourth's C1 replaced by the seed
and kept). `xrx` and `xsx` are assertions: `x` and `y` are any terms, and
nothing forbids the diagonal (as under the sixth, seventh and eighth).
Chosen (C1′): "asserted" is "multiplicity at least one" on each relation; a
state is terms, a multiplicity per ordered pair in `r` and one in `s`, no
names. Each *part* is a state of the seventh seed on the same terms
(derived: `proj`). Chosen (C9): `r` and `s` write assertions, not terms
(writing only; as 1:C9, 8:C9).

### (3) "Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one."

Given (G2 continued; either relation). Removing what is not asserted is not
a change (chosen, C5⁗: it would not lower a multiplicity that is already
zero). Adding what is already asserted is a change (it raises the
multiplicity).

### (4) "Nothing is given: to begin with there are no terms and nothing is asserted."

Given (G3″; word-identical to the seventh; replaces the eighth's G3′ and
G5′). One beginning: the empty state (`DState(0, (), ())`; Lean `NDSt`
empty). "Nothing is asserted" covers both relations (the only assertions
the seed names are `xry` and `xsy`). The eighth's C2″ (terms `a`, `b`; `arb`
once; `bra` once or not; nothing with `s`) has nothing to read. Unchosen
beginnings that already have terms or assertions are results of this one
(expected: D5 jointly free, empty included) and add no result; their cost
from a non-empty start is not the chosen beginning's formula (the eighth's
O4 is moot for the chosen beginning; left uncomputed).

What a result "adds to what is given" (sentence 9) when the given is empty:
the seed does not say. Chosen: record the terms and both totals (never
negative; the size split). That is the seventh's reading with a second
total.

### (5)–(7) "A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion."

Given (G6, G7; every seed from the fifth on, the eighth ranging over both
relations). Four kinds, no obstruction, no answer, no refusal (dropped from
the sixth on; not reintroduced). "Every assertion": both relations.
Chosen (C5⁗, unchanged from the eighth): an identification adds up the
multiplicities of the merged pairs in each relation separately; identifying
a term with itself is not a change; adding `xrx` or `xsx` is a change.
Unchosen: "the larger of the two" per relation — kept; expected to give the
same results, the same reachability and the same cost (no shortest sequence
identifies with anything asserted between the merged terms; 7:D15 / 8:D15
to re-check jointly). On the empty state the list is "add a term" alone
(the eighth's `changes` on `n = 0`; expected 7:D1 with two relations).

### (8) "Attempt every change, fewest additions first."

Given (G11). Chosen (C6): identifications, removals in `r`, removals in
`s`, a term, additions in `r`, additions in `s` — the eighth's order of
kinds and of relations among equals; round 0 is the empty state (the
seventh's C6). Unchosen: other orders among equals. Expected: the round of
a result is its size, so the order cannot move a result to another round.

### (9) "For every result, record how many terms and assertions it adds to what is given."

Given (G11). With nothing given, the record is the terms and both totals
(chosen above). A result is a two-relation state up to sameness (chosen,
C6).

### (10) "Two results that differ only in how their terms are written are the same result."

Given (G12). The earlier derivations read this two ways: any rewriting
(FREE) and rewritings keeping `a`, `b` (ANCHORED, 1:C4, 8:C4). With no `a`
and no `b` the second reading has nothing to keep: every rewriting keeps
the names. The two readings coincide — derived (7:D12), not chosen — and
the one rewriting still acts on both relations at once (8:C4). One
beginning and one reading: one exploration per bound.

### (11)–(13) "Attempt 100 changes along each alternative, finishing earlier changes on every alternative before later ones. Do not invent a change to reach 100. If the alternatives exceed what can be completed, declare a finite bound, export the exact frontier, and prove what is complete within it."

Given (G13). Breadth first, round by round. Without a bound every round has
a new result (the empty state plus `k` terms first appears in round `k`).
Within any bound on terms the results are infinite (multiplicities unbounded),
so the bound is on terms and on rounds together (chosen, C8′, as 4:C8′ to
8:C8′). Plan targets (to be declared as used, lowered rounds-first if a run
does not finish in minutes): 5 terms with 8 rounds; 3 terms with 9; 2 terms
with 12; a counts-only census at 6 terms with 8 rounds; full logs at 2 terms
and 3 rounds; reachability among the results of 3 terms and 5 rounds along
the changes among those of 3 terms and 7 rounds. Completeness within the
bound: the independent count (the eighth's `count_free` with the empty
state added). The seed's 100 rounds with two terms would hold about 10^11
results (expected closed form below) and are not run. No change is invented.

### (14) "Any outcome is valid."

Given (G14). Taken as: no particular structure is expected. Nothing was
steered.

## Notion table

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry` or `xsy`, the two relations, multiplicity | given (G1, G2) | eighth's writing, seventh's empty beginning |
| adding raises a multiplicity by one; removing lowers it by one | given (G2) | in either relation |
| asserted = multiplicity at least one; the two-relation state without names | chosen (C1′) | the eighth's `DState` with `names = None`; Lean `NDSt` |
| the `r` part, the `s` part | derived | each a state of the seventh (`proj`); the eighth's `proj` with names left out |
| a seventh state as a ninth state | derived | `ofR`: nothing in `s`; `ofS`: nothing in `r` (the exchange) |
| an eighth state as a ninth state | derived | `forget` the names; converse `name` (both names on one term) |
| a state with no terms | given (G3″) | the beginning; always representable, now a result |
| `xrx`, `xsx` are assertions | given (G2) | nothing forbids them |
| the names `a`, `b`; `arb`; `bra` | — (not in the seed) | without object; the naming map cites the eighth |
| what is given: nothing | given (G3″) | the empty state; one beginning; 8:C2″ has nothing to read |
| supply of letters not capped | chosen (C3) | harmless |
| `r`, `s` do not write terms | chosen (C9) | writing only; they are not given data |
| change, four kinds over two relations; what identifying does | given (G6, G7) | on the empty state one change: a term |
| the multiplicities of the pairs an identification merges add up, in each relation separately | chosen (C5⁗) | unchosen: the larger of the two; expected same results, reachability, cost |
| removing what is not asserted, identifying a term with itself: not changes; adding what is asserted is a change | chosen (C5⁗) | |
| obstruction, answer, refusal, build | — (not in the seed) | dropped from the sixth on; not reintroduced |
| the order of the changes of a result | chosen (C6) | identifications, removals in `r`, in `s`, a term, additions in `r`, in `s` |
| destroyed given, the eighth's cost with `lost` | — (not in the seed) | without object; the cost is the size |
| cost | derived (expected D4) | the size (terms + Σ`r` + Σ`s`); a sum of the two totals and one count of terms, not of two per-relation costs |
| result | chosen (C6) | a two-relation state up to sameness |
| the results, as a set | derived (expected D5) | every well-formed two-relation state, the empty one included; jointly free |
| sameness | given (G12) | one reading (7:D12); a rewriting rewrites both relations (8:C4) |
| terms and assertions added to what is given | given (G11), chosen | the terms and both totals; never negative |
| round; what counts as one change | chosen (C6) | the round of a result is its size |
| bound, frontier | given (G13) | bound on terms and on rounds: chosen (C8′) |
| the exchange of the two relations | derived (expected) | a symmetry the eighth's given broke |
| shortest sequences | derived / computed | additions only; one-term `C(p + q, p)`, not one |
| reachability between results | derived (expected D8) | has a term, or the start is empty; neither part imposes anything |
| counts of results by terms and total multiplicity | computed | the eighth's series, the empty state added; not a product for `n ≥ 2` |
| the one irreversible change | derived (expected D2) | leaving the empty state |
| separability (the task's word) | chosen reading | telling named terms apart is without object; replaced by having a term, jointly |
| what survives with nothing given *and* two relations | derived | composition table below; the paper's re-check column |

## Readings kept (C2, C4, C5, C6, C8, and the rest)

C1′ is 8:C1′ with the names left out (4:C1′ on each part). C3, C9 are the
earlier derivations', unchanged. C5⁗ and C6 are the eighth's, with the
seventh's empty round 0. C8′ is the fourth's to eighth's, bounds declared
from the independent count. The eighth's C2″ is replaced by the seed
(nothing). The eighth's C4 (two readings, both kept) is no longer a choice:
the seventh's D12, the rewriting still acting on both relations.

**C2. What is given.** Replaced by G3″: nothing; the empty state; one
beginning. Unchosen: a beginning that already has terms, or that asserts
something with `r` or with `s`. Every such beginning is a result of the
empty one (expected jointly free) and reaches the same results among the
states that contain it; it adds no result. Kept as alternatives that change
the cost measured from the start, not the set of results. The eighth's O4
(cost from a beginning with something in `s`) is moot for the chosen
beginning and is not computed.

**C4. Sameness.** Derived, not chosen: with no names, ANCHORED and FREE
coincide (7:D12). The one rewriting rewrites both relations at once
(8:C4). Two states whose parts are the same up to *separate* rewritings
need not be the same result — that is the eighth's non-product, and it
needs no names (the swap of two terms acts on both relations together).
Unchosen "separate rewritings of the two parts": eliminated as a reading of
the seed (the seed says the terms are written, not the relations; one
writing of the terms rewrites every assertion). Kept as the explanation of
why the count is not a product.

**C5⁗. What is a change.** Unchanged from the eighth: four kinds in either
relation; identification adds up, per relation; adding an asserted
assertion is a change; adding `xrx` / `xsx` is a change; removing what is
not asserted and identifying a term with itself are not. Unchosen: the
larger of the two, per relation. Kept; expected same results, reachability
and cost (7:D15 / 8:D15 jointly, no `bra` to make the costs differ).

**C6. Results and rounds.** A result is a two-relation state up to sameness;
every change counts one; round `k` performs the changes of the results first
reached in round `k − 1`, fewest additions first: identifications, removals
in `r`, in `s`, a term, additions in `r`, in `s`. Round 0 is the empty
state; round 1 is the one-term state asserting nothing. Unchosen: other
orders among equals; the order cannot move a result to another round if the
round is the size.

**C8′. Bound.** Terms and rounds together. Plan: 5×8, 3×9, 2×12, census
6×8; logs 2×3; reachability 3×5 along 3×7; eighth comparisons at four fewer
rounds, both beginnings, both readings. Lower rounds first, then terms, if
a run does not finish in minutes; declare the bounds used. Frontier: one
entry per result at the term bound (the term), and the results of the last
round whose changes await the next. Completeness: independent count.

**C9.** `r` and `s` write assertions, not terms.

**C10. Separability** (the task's word). The eighth read it as telling the
two named terms apart, a property of the terms shared by both relations.
The seventh had no names and replaced it by having a term. This seed has
neither names nor a given, and two relations: the same replacement, jointly
(the terms are shared). A second reading, the fewest classes of a split per
relation, is also answered on each part (the seventh's, which can now
decrease under identification). Neither reading is forced by the seed;
both kept as answers to the task's word, not as claims about the asserting.

## Ambiguities, every reading kept

| Ambiguity | Readings | Kept? |
|---|---|---|
| what is given | empty (seed); a beginning with terms or with assertions in `r` or `s` | empty chosen; others kept, add no result |
| "adds to what is given" on an empty given | terms and both totals (chosen); size alone; "zero, zero" | terms and both totals; the others are the same numbers |
| sameness | FREE; ANCHORED | coincide (derived); one reading |
| rewriting both relations vs separately | both at once (seed: the terms are written) | both at once; separate is why the count is not a product, not a reading of sameness |
| identification: add up vs larger, per relation | add up (C5⁗); larger | add up chosen; larger kept, expected same results / reachability / cost |
| order of kinds and of relations among equals | eighth's C6; any other | C6 chosen; others kept, expected same rounds |
| bound | plan targets; lowered if needed | declared when used |
| are `r`, `s` given data? | named only in the assertion-writing sentence | not given contents; C9 writing only |
| does "nothing is asserted" cover `s`? | yes (the seed's assertions are `xry` or `xsy`) | yes; no other reading |
| `bra` / something in `s` "not given" | the eighth's residual list | gone; the ninth has no such list |
| obstruction / answer | not in the seed | not introduced |

No reading is dropped without a proof. The two beginnings of the eighth
(`bra` or not) and its two sameness readings become, once the names are
forgotten, one set of results with a term (expected).

## What both dials change at once

### The state: two multiplicity functions, no names, possibly no terms

Terms, a multiplicity for each ordered pair in `r` and one in `s`. The
eighth's `DState` with `names = None` is exactly this; the eighth's
`canonical` with no names is sameness under any rewriting acting on both
relations at once — one reading (7:D12) that still rewrites both relations
together (8:C4). A state with no terms was always representable and is now
the beginning. In Lean a new structure `NDSt` (terms, a multiplicity
function indexed by the relation tag) with the eighth's operations minus
the names; four maps: `forget : DSt → NDSt`, `name : NDSt → ℕ → DSt` (both
names on one term), `proj : NDSt → Rel → NSt`, `ofR : NSt → NDSt` (and
`ofS` by the exchange).

### The changes: the eighth's four kinds, from a state that may be empty

Identify two terms (merges both relations, multiplicities adding up in each
separately); remove an assertion of `r` or of `s`; add a term; add an
assertion of `r` or of `s`. On the empty state the list is "add a term"
alone. A result with `n` terms and `d_r + d_s` asserted pairs has
`C(n, 2) + d_r + d_s + 1 + 2n²` changes, `1 + 2n²` of them additions; the
empty state has one (8:D3 with `n = 0`). Fewest additions first as C6.

### The cost: the size, which is a sum — with the terms counted once

Size = terms + Σ`r` + Σ`s`. Every change moves it by exactly one (8:D4(v)
`Step8.size_step` through `name` for the three kinds that need a term; the
term on any state directly, including empty). Nothing is given, so nothing
is destroyed: the eighth's potential `size + 2·lost` loses its second term,
and the cost of a result is its size (7:D4 survives). Additions reach every
well-formed state from the empty one in exactly its size: the terms, then
the `r` multiplicities, then the `s` ones (8:D4 `reach8_raise` through
`name`, once a term is there).

Is the cost "a sum per relation" as under the eighth? The eighth's
statement was `cost8 = cost6(r part) + Σ s`: the `r` part carried the terms
and the given, the `s` part only its total. Here the same *shape* holds
with the seventh's cost: `size = cost7(r part) + Σ s`, and by symmetry
`= cost7(s part) + Σ r`. But `cost7(r part) + cost7(s part) = size + n`:
the two per-relation costs each count the terms, which the relations share.
So "the cost is a sum" is true of the assertions (each relation's total is
added, and nothing else) and false of the terms (counted once, not twice).
The eighth's given hid this: it put the terms with `r`. **First
interference: the shared terms.**

Which changes raise the cost by exactly one: the additions (of a term, of
an `r` assertion, of an `s` assertion), and nothing else. Every shortest
sequence is additions only. Parity: every change moves the size by one; no
change keeps the round.

### The results: every well-formed state; jointly free; the exchange symmetry

From the empty state every well-formed two-relation state is reached by
additions, so the results are all of them, the empty one included. Jointly
free: for every well-formed `r` part and `s` part on the same terms the
pair is a result (8:D5's product survives; trivially, since every
well-formed state is a result). The seventh's results are exactly the
results asserting nothing with `s` (at the same rounds: the size agrees;
with the same shortest-sequence counts: a shortest sequence to such a
result never touches `s`), and — new — by the exchange of the two relations
also exactly the results asserting nothing with `r`. The eighth's results
under any rewriting (either beginning) are exactly the results with a term
(8:D5 `result8_iff_A`, `_B` say every well-formed state with a term;
forgetting the names, which under FREE were already placed freely); the
eighth's results with the names kept, once forgotten, are results.

The exchange of the relations (`swap`: `r ↔ s`) maps changes to changes,
results to results at the same round, and keeps reachability: a symmetry of
the ninth seed that the eighth seed did not have (its given lived in `r`).
The results left unchanged by the exchange are those with `r = s`
everywhere; their count with `n` terms and total `t` is the seventh's count
with `n` terms and total `t / 2` (a rewriting fixes `(r, r)` exactly when
it fixes `r`), zero for odd `t`.

### Reachability: a term decides, whatever either relation says

From a state with a term every state with a term is reached (8:D8
`reach8_of_names` through `name`, both names on one term of the start and
of the target, so the names condition is trivial); from the empty state
every well-formed state by additions; no state with a term reaches the
empty state (every change on a state with a term leaves a term). So `t` is
reachable from `s` exactly when `t` has a term or `s` is empty — 7:D8, on
the terms both relations share. The eighth's "the `s` part imposes
nothing" survives and so does its mirror: the `r` part imposes nothing
either, there being no names left for it to impose through. Mutual among
the states with a term, one-way out of the empty state, comparable, the
two-change cycle at every state with a term (none at the empty state).

### Counting: not a product, exactly as the eighth found

The results with `n` terms up to rewriting by total multiplicity of both
relations: the eighth's `count_free` (the orbit method with two
multiplicities on every cycle of the rewriting, off-diagonal and diagonal),
which mentions no name and no given; with `n = 0` it gives the empty state
alone. The count is not the product of the seventh's single-relation counts
for `n ≥ 2` (20 against 16 with two terms and total 2; 8 against 4 with one
assertion in each relation) and equals it for `n = 0` and `n = 1`: 8:D10's
non-product survives, and must be recomputed with one sameness and the
empty state — the eighth's count under any rewriting *is* this seed's
count. **Second interference: the shared rewriting.** The results of round
`r` are the well-formed states of size `r`: 1, 1, 3, 8, 29, 104, 420,
1 783, 8 115, 38 813, 194 888, … with no bound on terms (the independent
count; to be certified).

### Two terms, all rounds

Eight multiplicities (four in `r`, four in `s`) summing to `t`, up to the
swap of the two terms: `C(t + 7, 7)` writings plus the swap-fixed ones
(`p = q`, `i = j` in each relation: `t` even, `C(t/2 + 3, 3)`), halved:
`(C(t + 7, 7) + [t even]·C(t/2 + 3, 3)) / 2` = 1, 4, 20, 60, 170, 396, … .
The one-term states of total `t` number `t + 1` (`ara` `p` times, `asa`
`t − p` times). So the results of round `r` with at most two terms are
`[r = 0] + [r ≥ 1]·r + [r ≥ 2]·two_term_count(r − 2)`, i.e.
`[r = 0] + [r ≥ 1]·r + [r ≥ 2]·(C(r + 5, 7) + [r even]·C(r/2 + 2, 3)) / 2`:
1, 1, 3, 7, 24, 65, 176, … — of order `r^7`, so the seed's 100 rounds with
two terms would hold about 10^11 results. (The CLAUDE.md formula is this
one; the two-term contribution at `r = 4` is 20, not 19.)

### Shortest sequences: the two relations interleave

A shortest sequence is additions only and exact within any bound holding its
target. The seventh's "one-term results have one shortest sequence" fails:
the one-term state asserting `ara` `p` times and `asa` `q` times is reached
by `C(p + q, p)` shortest sequences (the term, then the `p + q` assertions
in any order). **Third interference: the additions of the two relations
interleave**, so the number of shortest sequences is not the product of the
single-relation numbers but a multinomial over the interleavings.

### Statements

Every earlier unnamed statement on each part (the eighth's `on_part`), the
eighth's joint ones, plus: nothing at all (true of the beginning alone), the
state unchanged by exchanging the relations. Every well-formed state is a
result, the empty one included, so *no* statement holds in every result:
8:D14 "at least one term" (on either part) fails at round 0. Witnesses for
what does not follow are listed below.

## Expected consequences (from the ninth plan in `CLAUDE.md`)

To be proved or refuted from this seed, not assumed from the seventh or the
eighth:

1. The first change adds a term and nothing else is a change on the empty
   state; round 1 is the one-term state asserting nothing.
2. A term once there stays, so the empty state is a result (round 0) never
   returned to.
3. The size (terms plus both totals) moves by exactly one per change, and
   additions alone reach every well-formed state, so the fewest changes to a
   result is its size — 7:D4 survives — and it is the seventh's cost of the
   `r` part plus the `s` total — 8:D4's additivity survives — while the sum
   of the seventh's costs of the two parts overcounts the terms, which the
   two relations share: the cost is a sum of the two relations' totals and
   one count of terms, not of two per-relation costs.
4. The results are every well-formed two-relation state, the empty one
   included, and they are jointly free (any two well-formed parts on the
   same terms make a result: 8:D5's product survives).
5. The seventh's results are exactly the results asserting nothing with
   `s`, and, by the exchange of the relations, exactly those asserting
   nothing with `r`.
6. The eighth's results (any rewriting, either beginning) are exactly the
   results with a term, and its results with the names kept, once forgotten,
   are results.
7. Reachability is "has a term, or the start is empty" — 7:D8 on the shared
   terms, which is 8:D8's "the `s` part imposes nothing" with nothing left
   for the `r` part to impose either; mutual among the results with a term,
   one-way out of the empty state.
8. The count of results with `n ≥ 2` terms is not the product of the
   seventh's single-relation counts — 8:D10 survives verbatim, since the
   eighth's count under any rewriting is this seed's count — and equals it
   for `n ≤ 1` (including the empty state).
9. The exchange of the two relations is a symmetry of the results, the cost
   and reachability (new: the eighth's given broke it).
10. The seventh's "one-term results have one shortest sequence" fails:
    the additions of the two relations interleave, `C(p + q, p)` sequences.
11. No tested statement holds in every result.
12. A result with `n` terms and `d_r + d_s` asserted pairs has
    `C(n, 2) + d_r + d_s + 1 + 2n²` changes and the empty state one.
13. The results of round `r` with at most two terms are the closed form
    above, so a lower bound on rounds is declared with the closed form
    proved for every round.

## Composition table (rule 5)

Whether the seventh's collapses and the eighth's independence compose.
"Survives" means the earlier statement holds as stated from this seed;
"survives as …" means the shape holds after the restatement named;
"does not survive" means it is false, with a witness; "without object"
means the seed has no referent for it.

| Earlier result | Expected under the ninth seed |
|---|---|
| 7:D4 cost = size; additions only | **survives** with both totals in the size |
| 7:D8 has-a-term criterion | **survives** on the shared terms; neither part imposes anything |
| 7:D12 one sameness | **survives**; the rewriting acts on both relations |
| 8:D5 jointly free; sixth's = nothing in `s` | **survives** with the seventh in place of the sixth; empty included; by the exchange also nothing in `r` |
| 8:D4 cost additive per relation | **survives as** `size = cost7(r) + Σ s = cost7(s) + Σ r`; **does not survive as** `cost7(r) + cost7(s)` (that is `size + n`; witness: the one-term state asserting nothing, 1 against 1+1) |
| 8:D10 count not a product | **survives** for `n ≥ 2` (20 against 16 with two terms and total 2; 8 against 4 with one assertion in each); **equals** the product for `n = 0` and `n = 1` |
| 8:D4 with `lost` on `r`; 6:D8 | **does not survive** (nothing given to destroy); witness: the one-term state, one change here, two under the eighth from `arb`; 4:D8's size difference **survives** with `size(given) = 0` |
| 8:D8 names criterion | **without object**; replaced by 7:D8 |
| 8:D14 at least one term everywhere | **does not survive**; fails at the empty state (round 0) |
| 8:D1, 8:D2 names; 8:D13 `s` adds nothing to what is given; `bra` | **without object** |
| 8:C2″ given `a`, `b`, `arb`; 8:C4 two readings both kept | C2″ replaced by G3″; C4 collapses (7:D12) |
| 8:D3 changes per result; `xrx`/`xsx` making | **survives**; the empty state has one change |
| 7:D1, 7:D2 first change a term; a term stays | **survive** with two relations |
| 7:D5 every well-formed state a result, empty included | **survives** with two relations |
| 7:D11, 8:D11 two-term forms | **new** closed form with eight multiplicities |
| 7:D11 / 7:K one-term results have one shortest sequence | **fails**: `C(p + q, p)` |
| 8:D12 interaction through terms and names | **through the terms alone** (an identification merges both; a rewriting rewrites both; an assertion of one leaves the other as it is) |
| 7:D3 `C(n,2)+d+1+n²` | **restated** as 8:D3: `+ d_s + n²` |
| 7:D10 seventh count | the nothing-in-`s` (and nothing-in-`r`) part of the ninth count |
| 6:D8 cost with `lost`; 6:D12 names criterion | do not survive (7:D13 already; names without object); size difference does |
| 6:D9 every wf state with a term | seventh extends by empty (7:D5); eighth by `s` (8:D5); jointly both |
| 7:K, 8:K computed claims | computed again on the nothing-in-`s` results and the results with a term |
| the two-relation state, sameness rewriting both (8:C4) | survives with no names: one reading |
| `remove`, `identify`, `perform` (5:C5″, 6:C5‴, 8:C5⁗) | survive (no name, no given); on the empty state the list is one change |
| `cycle2`, unbounded sequences | survive through `name` on states with a term; none at the empty state |

**Where they compose.** 7:D4, 7:D8, 7:D12 hold with two relations. 8:D5
holds with nothing given (empty included). 8:D4 holds as
`size = cost7(r) + Σ s`, not as a sum of two seventh costs. 8:D10 holds for
`n ≥ 2` with one sameness and with the empty state counted.

**Where they interfere.** (i) Shared terms in the cost: `cost7(r)+cost7(s)`
counts them twice. (ii) Shared rewriting in the count: the product of the
single-relation counts undercounts for `n ≥ 2`. (iii) Interleaving of
additions: `C(p+q, p)` shortest sequences to a one-term result, not 1×1.
(iv) Exchange symmetry, new: the two relations are interchangeable, which
the eighth's given forbade.

**What fails as stated.** 8:D4-with-`lost`, 8:D8 names, 8:D14 at-least-one
term, 7:K one-term-one-sequence, and every eighth claim about `a`, `b`,
`arb`, `bra`.

## What does not follow (expected witnesses)

Each item needs two legal witnesses (one where it holds, one where it
fails), or a proof of independence. Expected:

| Statement | Holds | Fails |
|---|---|---|
| at least one term | the one-term state (round 1) | the empty state (round 0) |
| nothing in `s` | the empty state; every seventh result read as `ofR` | the one-term state asserting `asa` once |
| nothing in `r` | the empty state; `ofS` of a seventh result | the one-term state asserting `ara` once |
| `r` and `s` agree everywhere | the empty state; any `(M, M)` | `ara` once, nothing in `s` |
| some pair asserted in both relations | `ara` and `asa` once | the empty state |
| the cost is `cost7(r) + cost7(s)` | the empty state (`0 = 0 + 0`) | the one-term state asserting nothing (`1 ≠ 1 + 1`) |
| the count with `n` terms is the product of the seventh's | `n = 0`, `n = 1` | `n = 2`, total 2 (20 against 16); one assertion in each (8 against 4) |
| one-term results have one shortest sequence | `p = 0` or `q = 0` (nothing in one relation) | `ara` once and `asa` once: `C(2,1) = 2` |
| a result once left is never returned to | the empty state | any state with a term (two-change cycle) |
| every sequence to a result has the same length | from empty to empty (length 0) | from empty to a state with a term (add then remove vs additions only) |
| the eighth's fewest changes from `arb` | — (without object as a formula on these results) | the one-term state: 1 here, 2 there |

Nothing about the asserting is forced from nothing. What *is* forced: the
first change (a term), the cost of every result (its size), the one-way
exit from the empty state, the number of changes of a result, joint
freedom of the two parts, and that the count up to writing is not a
product for `n ≥ 2`.

## Open items (not to be closed in these notes)

- O1. Bounds actually used, if a timed run lowers the plan's targets.
- O2. The two-term closed form and the unbounded round counts, certified by
  the independent count (computed, not assumed from the arithmetic above).
- O3. Whether every Lean target 1–4 closes; target 5 (`rename9`) attempted
  once.
- O4 of the eighth (cost from a beginning with something in `s`) remains
  uncomputed; it is moot for the chosen beginning.
- The unchosen identification reading (larger of the two): expected same
  results, reachability and cost; a written argument, as 7:D15 / 8:D15.

No blocker. The seed is readable; the maps to the seventh and the eighth
are the ones the plan names; nothing requires the network, a file outside
the repository, a change to `prompt/`, or a question.
