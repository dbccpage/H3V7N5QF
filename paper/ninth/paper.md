# What follows from nothing with two relations: counted assertions, four kinds of change, and an empty beginning

Ninth derivation. Input: `prompt/ninth/seed_prompt.md`. Task:
`prompt/ninth/prompt.md`. Claim IDs refer to `paper/ninth/claim_ledger.md`;
an ID written `7:D4` refers to the seventh derivation's ledger
(`paper/seventh/claim_ledger.md`, paper `paper/seventh/paper.md`), `8:D4` to
the eighth's (`paper/eighth/`), `6:D8` to the sixth's (`paper/sixth/`),
`4:D8` to the fourth's. Lean names in the namespace `Seed.Ninth` are in
`lean4/Ninth/`; names in `Seed.Eighth`, `Seed.Seventh`, `Seed.Sixth`,
`Seed.Fifth`, `Seed.Fourth`, `Seed` are the earlier derivations'
(`lean4/Eighth/`, `lean4/Seventh/`, `lean4/Sixth/`, `lean4/Fifth/`,
`lean4/Fourth/`, `lean4/H3V7N5QF/`). Where a short name exists in two
libraries the ninth's is meant unless the namespace is written. The axiom
report for every theorem cited here, of any of the nine libraries, is
`evidence/ninth/lean_axioms.txt`. Computed files are in `evidence/ninth/`,
written by `python code/generate_ninth.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; the unchosen
readings are listed), **derived** (proved), **computed** (output of `code/`),
**refuted** (proved impossible), **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the ninth seed, and the re-check says whether the result *survives with
nothing given and two relations* — in particular whether the seventh's
collapses (cost is the size, reachability is having a term, one sameness)
and the eighth's independence (results a product, cost a sum, count not a
product) hold together, and where they do not. The re-check is one of six
kinds. *(no change)*: the statement mentions neither the given, nor the
names, nor a second relation, so it stands as it is. *(through the maps)*: a
state of the eighth seed with its names forgotten is a state of the ninth
(`DSt.forget`), and every change of the eighth is a change of the ninth on
the forgotten states (`Step8.forget`, `Reach8.forget`); a state of the ninth
with a term, both names put on one of its terms, is a state of the eighth
(`NDSt.name`), and every change of the ninth on such a state is a change of
the eighth on the named states, the names following the merge (`Step9.name`,
`Reach9.name`). A ninth state has two *parts*, its `r` part and its `s`
part, each a state of the seventh seed on the same terms (`NDSt.proj`);
every change of the ninth is a change of the seventh on a part and leaves
the other part as it is, or is a change of the seventh on both
(`Step9.proj`); a seventh state read as a ninth state asserting nothing with
`s` (`NSt.ofR`) turns every change of the seventh into one of the ninth
(`Step7.ofR`, `Reach7.ofR`). So what the eighth proved about one change
holds here for every change that starts from a state with a term, and what
the seventh proved about one multiplicity function holds here for each part.
*(without object)*: the statement is about the given, the names, `bra`, or
the destroyed givens, none of which the ninth seed has. *(re-proved)*: the
earlier proof used the given, the names, or one relation, and a statement
covering the ninth's states is proved afresh. *(computed again)*: a computed
statement of the seventh is re-run beside the ninth exploration and compared
on the results asserting nothing with `s` (and, by the exchange, nothing
with `r`); a computed statement of the eighth is compared on the results
with a term. Results of the earlier derivations that fail, or change shape,
under the ninth seed are listed in §8.

## 0. Findings in brief

1. The ninth seed is the eighth (a second relation: an assertion is `xry` or
   `xsy`) with the seventh's beginning (nothing given: no terms, nothing
   asserted). There is no `a`, no `b`, no `arb`, no `bra`; two relations `r`
   and `s`, neither given anything; one beginning, the empty state; one
   reading of sameness (D12).
2. **The seventh's collapses survive with two relations.** The fewest
   changes to a result is its size (terms plus both totals) (D4,
   `fewest_changes9`); a result reaches another exactly when the other has a
   term or the first is empty (D8, `reach9_iff`); the two readings of
   sameness coincide (D12). The first change can only add a term (D1); a
   term, once there, stays, so the empty state is a result never returned to
   (D2).
3. **The eighth's independence survives in three of four respects, and
   fails as a sum of two seventh costs.** The results are every well-formed
   two-relation state, the empty one included, and they are jointly free:
   any well-formed `r` part and `s` part on the same terms make a result
   (D5, `results_pair9`). The count of results with `n ≥ 2` terms is not the
   product of the seventh's single-relation counts, and equals it for
   `n ≤ 1` (D10). The cost is additive *per relation's total*, with the
   terms counted once: `size = cost₇(r) + Σ s = cost₇(s) + Σ r` (D4,
   `cost_adds_up9`). It is *not* `cost₇(r) + cost₇(s)`, which is `size + n`
   (`cost_not_sum_of_parts9`; witness: the one-term state asserting nothing,
   1 against 1 + 1).
4. **Where the two dials interfere.** (i) Shared terms in the cost: each
   part's seventh cost counts the terms, which the relations share. (ii)
   Shared rewriting in the count: one rewriting must fix both relations at
   once (20 against 16 with two terms and total 2; 8 against 4 with one
   assertion in each). (iii) Interleaving of additions: a one-term result
   asserting `ara` `p` times and `asa` `q` times is reached by `C(p + q, p)`
   shortest sequences, not 1 × 1 (D11). (iv) Exchange symmetry, new: the two
   relations are interchangeable (`swap9`, `exchange_symmetry9`), which the
   eighth's given forbade.
5. **What fails as stated.** The eighth's cost with destroyed givens
   measured from `arb` (the one-term state: one change here, two there)
   (D13); the eighth's names criterion (without object, replaced by D8);
   "at least one term" in every result (fails at round 0) (D14); the
   seventh's "one-term results have one shortest sequence"; every eighth
   claim about `a`, `b`, `arb`, `bra`.
6. Nothing about the asserting is forced from nothing (D14). What is forced:
   the first change, the cost of every result, the one-way exit from the
   empty state, the number of changes of a result
   (`C(n, 2) + d_r + d_s + 1 + 2n²`, D3), joint freedom of the two parts,
   and that the count up to writing is not a product for `n ≥ 2`. With at
   most two terms the results of round `r` are
   `[r = 0] + [r ≥ 1]·r + [r ≥ 2]·(C(r+5, 7) + [r even]·C(r/2+2, 3))/2`
   (D11), of order `r⁷`, so the seed's 100 rounds would hold about
   1.5 · 10¹¹ results and 12 are run. Within the bounds the exploration is
   complete, certified by the eighth's independent count with the empty
   state added (D10). Everything claimed as derived is in Lean, the
   every-writing statements included (target 5 of the plan closed on the
   single attempt); proved in the paper and checked by computation only: the
   change-count formula (D3), the within-bound completeness (D10), the
   two-term closed form and the one-term binomial (D11), the coincidence of
   the two readings of sameness (D12), the unchosen reading of identification
   (D15), and the non-product count (D10).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2⁗ | An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G3″ | Nothing is given: to begin with there are no terms and nothing is asserted. |
| G6 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G11 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, prove what is complete within it. |
| G14 | Any outcome is valid. |

Against the eighth seed, G3″ replaces G3′ and G5′; against the seventh, G2⁗
replaces G2‴. Nothing else changes (`diff`;
`research/ninth/reading_the_seed.md`). Every other sentence is the sixth
seed's word for word. The ninth seed never uses the words `a`, `b`, `arb`,
or `bra`.

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry` or `xsy`, the two relations, multiplicity | given (G1, G2⁗) | eighth's writing, seventh's empty beginning |
| adding raises a multiplicity by one; removing lowers it by one | given (G2⁗) | in either relation |
| asserted = multiplicity at least one; the two-relation state without names | chosen (C1′) | the eighth's `DState` with `names = None`; Lean `NDSt` |
| the `r` part, the `s` part | derived (§4, `NDSt.proj`) | each a state of the seventh |
| a seventh state as a ninth state | derived (`NSt.ofR`) | nothing in `s`; `ofS` by the exchange |
| an eighth state as a ninth state | derived (`DSt.forget`; converse `NDSt.name`) | both names on one term |
| a state with no terms | given (G3″) | the beginning; always representable, now a result |
| `xrx`, `xsx` are assertions | given (G2⁗) | nothing forbids them |
| the names `a`, `b`; `arb`; `bra` | — (not in the seed) | without object; the naming map cites the eighth |
| what is given: nothing | given (G3″) | the empty state; one beginning; 8:C2″ has nothing to read |
| supply of letters not capped | chosen (C3) | harmless |
| `r`, `s` do not write terms | chosen (C9) | writing only; they are not given data |
| change, four kinds over two relations; what identifying does | given (G6, G7) | on the empty state one change: a term (D1) |
| the multiplicities of the pairs an identification merges add up, in each relation separately | chosen (C5⁗) | unchosen: the larger of the two; same results, reachability and cost (D15) |
| removing what is not asserted, identifying a term with itself: not changes; adding what is asserted is a change | chosen (C5⁗) | |
| obstruction, answer, refusal, build | — (not in the seed) | dropped from the sixth on; not reintroduced |
| the order of the changes of a result | chosen (C6) | identifications, removals in `r`, in `s`, a term, additions in `r`, in `s` |
| destroyed given, the eighth's cost with `lost` | — (not in the seed) | without object; the cost is the size (D4) |
| cost | derived (D4) | the size (terms + Σ`r` + Σ`s`); a sum of the two totals and one count of terms, not of two per-relation costs |
| result | chosen (C6) | a two-relation state up to sameness |
| the results, as a set | derived (D5) | every well-formed two-relation state, the empty one included; jointly free |
| sameness | given (G12) | one reading (D12); a rewriting rewrites both relations (8:C4) |
| terms and assertions added to what is given | given (G11), chosen | the terms and both totals; never negative |
| round; what counts as one change | chosen (C6) | the round of a result is its size (D4) |
| bound, frontier | given (G13) | bound on terms and on rounds: chosen (C8′) |
| shortest sequences reaching a result; sequences of every length | computed (K7); derived (D4, D9, D11) | additions only, exact within the bound; `C(p + q, p)` for one-term results; infinitely many sequences to every result with a term, one to the empty state |
| reachability between results | derived (D8) | a term decides; neither part imposes anything |
| parity of the cost | derived (D4) | every change moves it by one |
| counts of results by terms and total multiplicity | computed (K1) | the eighth's series, the empty state added; not a product for `n ≥ 2` |
| the exchange of the two relations | derived (D16) | a symmetry the eighth's given broke |
| the one irreversible change | derived (D2) | leaving the empty state |
| the interaction of the two relations | derived (D17, `interaction9`) | through the terms alone |
| separability (the task's word) | chosen reading (§7) | telling named terms apart is without object; replaced by having a term, jointly |
| what survives with nothing given and two relations | derived (§7; `Ninth/Compare.lean`) | see §8 for what does not |

## 3. Readings that had to be chosen

C1′ is 8:C1′ with the names left out (4:C1′ on each part). C3, C9 are the
earlier derivations', unchanged. C5⁗ and C6 are the eighth's, with the
seventh's empty round 0. C8′ is the fourth's to eighth's. The eighth's C2″
(what is given: `a`, `b`, `arb`, `bra` or not, nothing with `s`) has nothing
to read: the seed says what is given, and it is nothing. The eighth's C4
(two readings of sameness, both kept) is no longer a choice: D12, the
rewriting still acting on both relations.

**C3. No cap on the number of terms.** The sequences used in the proofs of
D4 and D5 never have more terms than the target; the sequence of D8 between
two results with a term, the eighth's through the naming map, uses at most
`max(terms) + 2`; as 8:C3, 7:C3.

**C5⁗. What is a change.** As 8:C5⁗: adding an assertion that is asserted
already is a change, and so is adding `xrx` or `xsx`; removing what is not
asserted and identifying a term with itself are not changes; the pairs an
identification merges have their multiplicities added up, in each relation
separately (`code/eighth/state.py` `identify`, imported; Lean
`NDSt.identify`). Unchosen: the larger of the two, per relation. Under the
ninth seed the two readings give the same results, the same reachability and
the same cost (D15). The unchosen reading is kept as an alternative that
changes nothing computed here.

**C6. Results and rounds.** As 8:C6 with the seventh's empty round 0: a
result is a two-relation state up to sameness; round `k` performs every
change on every result first reached in round `k − 1`; every change counts
one. Fewest additions first: identifications, removals in `r`, removals in
`s`, a term, then the additions in `r`, then in `s`. Round 0 is the empty
state; round 1 is the one-term state asserting nothing, the outcome of the
one change the empty state has (D1). Unchosen: other orders; the order
cannot move a result to another round (D4: the round of a result is its
size).

**C8′. Bound on terms and on rounds.** As 4:C8′ to 8:C8′: within any bound
on terms the results are infinite, so every exploration is bounded in terms
and in rounds. One beginning and one reading, so three explorations: 5 terms
with 8 rounds; 3 terms with 9; 2 terms with 12; a counts-only census at 6
terms with 8 rounds. Full attempt log at 2 terms and 3 rounds; reachability
among the results of 3 terms and 5 rounds, along the changes among those of
3 terms and 7 rounds. The plan's targets completed here and are the bounds
used (`summary.json` `plan`). The seed's 100 rounds with two terms would
hold about 1.5 · 10¹¹ results (D11) and are not run.

**C9.** `r` and `s` write assertions, not terms.

**C2. What is given.** Replaced by G3″. Unchosen: a beginning that already
has terms, or that asserts something with `r` or with `s`. Every such
beginning is a result of the empty one (D5) and reaches the same results
among the states that contain it; it adds no result. Kept as alternatives
that change the cost measured from the start, not the set of results. The
eighth's O4 (cost from a beginning with something in `s`) is moot for the
chosen beginning and is not computed.

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. The first change adds a term.** On the empty state the list of
changes has one entry, "add a term": there are no two terms to identify, no
assertion to remove, no terms between which to assert
(`first_change_adds_term9`; `code/eighth/changes.py` `changes` on the empty
state, imported; computed: `given.json`,
`the_first_change_can_only_add_a_term`). The outcome is the one-term state
asserting nothing, the only result of round 1
(`the_first_round_is_the_one_term_state_alone` true in every run). 7:D1
survives with two relations.

**D2. A term stays: the one irreversible change.** Every change on a state
with a term leaves a state with a term (`Step9.nonempty`: a term is added;
an assertion is between terms; a removal keeps the terms; an identification
of two terms keeps one), and so does every change on a well-formed state
(`Step9.nonempty_out`). Hence once a state has a term every later state has
a term (`Reach9.nonempty`), and the empty state is reached from a
well-formed state only from itself in zero changes (`reach9_empty_iff`,
`empty9_never_returned`, `no_cycle_at_empty9`). This is 7:D2 with two
relations. It replaces the eighth's D2 (the names once one term stay one
term): through the naming map the names of every state are one term, so
8:D2 holds vacuously along every sequence from a state with a term
(`names_merged_vacuous9`) and says nothing. Computed: in every run no change
loses the last term (`term_lost` empty), and exactly one result reaches what
is given — itself (`results_that_reach_what_is_given: 1`).

**D3. How many changes a result has.** A result with `n` terms and
`d_r + d_s` asserted pairs, diagonal pairs included, has
`C(n, 2) + d_r + d_s + 1 + 2n²` changes, `1 + 2n²` of them additions (8:D3,
no change: the count mentions no name; 7:D3 restated with `+ d_s + n²`); the
empty state has one. The four kinds (G6, C5⁗) enumerate it: `C(n, 2)`
identifications of two distinct terms, `d_r + d_s` removals of an asserted
pair in either relation, one new term, and `2n²` additions of an assertion
(every ordered pair, in each relation). Not in Lean: `Step9` is a relation
on states, not an enumeration of that list, and `Step9.proj` says only that
a ninth change is a seventh change on a part or leaves the part fixed (O3).
Computed: `attempts_equal_formula` true in every run
(`code/ninth/changes.py`, `tests/test_ninth_changes.py`). On a result
asserting no `xrx`, `n` plus the number of related pairs *in `r`* of its
changes make some `xrx` asserted, and likewise for `s` and `xsx` (8:D3 on
each part; computed with the eighth's own function,
`xrx_making_equal_eighth_formula`, `xsx_making_equal_eighth_formula` true in
every run).

**D4. Fewest changes (cost): the size, additive per relation's total, terms
counted once.** For a well-formed two-relation state `G` let `size(G)` be
its number of terms plus the sum of its multiplicities in both relations.
Then the fewest changes from what is given to `G` is

    size(G)

— the first to eighth derivations' `size − size(given) + 2·lost` with
`size(given) = 0` and nothing to destroy (7:D4 with both totals; 4:D8's size
difference). Equivalently

    size(G)  =  cost₇(G.r) + Σ(G.s)  =  cost₇(G.s) + Σ(G.r)

(`size9_eq`, `cost_adds_up9`, `cost_adds_up9_swapped`: the eighth's
additivity with the seventh's cost in place of the sixth's). The sum of the
two parts' seventh costs is *not* the cost:

    cost₇(G.r) + cost₇(G.s)  =  size(G) + n

(`cost_not_sum_of_parts9`): each part counts the terms, which the two
relations share. Witness: the one-term state asserting nothing, each part
size 1, the state size 1, not 2 (`one_term_parts9`; `given.json`,
`cost_of_the_one_term_state: 1`). *(i) Lower bound.* Every change moves the
size by exactly one: up for the two additions (a term, or an assertion of
either relation), down for a removal or an identification (`Step9.size_step`;
8:D4(v) `Step8.size_step` through the naming map for the three kinds that
need a term, and `size_addTerm9` for the term, since the empty state cannot
be named). So a state reached from the empty state in `n` changes has size
at most `n` (`Reach9.size_le`, `fewest_changes9_lower`). *(ii) Upper bound.*
From the empty state add the terms of the target one by one
(`reach9_addTerms`); then raise the `r` multiplicities, then the `s` ones
(`reach9_raise`: 8:D4's `reach8_raise` through the naming map, once a term
is there); together `reach9_by_additions`: every well-formed state is
reached in exactly its size. If the target has no term it is the empty
state (`eq_empty9_of_wf`) and zero changes do. Both bounds:
`fewest_changes9`; the one-term state costs one (`cost_oneTerm9`). *(iii)
Every writing.* Changes commute with one-to-one rewriting of both relations
(D7) and the size is the same in every writing (`size_rename9`), so the
fewest changes to a result is the size of any of its writings
(`fewest_changes9_every_writing`; target 5 of the plan closed). *(iv) Which
changes raise the cost by exactly one.* The additions of a term or of an
assertion of either relation, and nothing else (`Step9.lowers_or_adds`;
computed: `code/ninth/cost.py` `raises_by_one` agrees with the outcome on
every change within the bound of every run, `cost_rule_disagreements`
empty, `size_not_moved_by_one` empty). *(v) Parity.* The size and the length
of a sequence have a fixed parity (`Reach9.size_parity`); no change keeps
the round (`changes_keeping_the_round: 0` in every run). *(vi) Every
shortest sequence is additions only.* A sequence from the empty state whose
length is the size of its end contains no removal and no identification
(`shortest_are_additions9`). Computed: the round of every explored result
equals its size in all three runs and the census
(`round_equals_cost_formula_for_every_result`);
`cost_is_the_seventh_cost_of_either_part_plus_the_other_total` true;
`sum_of_the_part_costs_exceeds_the_cost_by_the_terms` true;
`cost_part_mismatches` empty.

**D5. Everything well formed is a result, the empty state included; the
results are jointly free.** Every well-formed two-relation state is reached
from the empty state (D4(ii)), and every reached state is well formed
(`Reach9.wf`): `result9_iff`; the empty state is the result of round 0
(`empty9_is_a_result`). For every well-formed `r` part and `s` part on the
same terms, the pair is a result (`results_pair9`): 8:D5's product survives,
empty included. **The seventh's results are the results asserting nothing
with `s`**, and by the exchange those asserting nothing with `r`: every
result of the seventh is a result of the ninth with nothing in `s` at the
same round (`results_ofR7`); among the states asserting nothing with `s` the
two seeds have the same results (`results_r_iff9`), and among those
asserting nothing with `r` likewise (`results_s_iff9`); both parts of every
result are seventh results (`proj_results9`). **The eighth's results are the
results with a term.** Every result of the eighth, from either beginning, is
a result of the ninth with its names forgotten (`results_forget8_A`, `_B`);
every result of the ninth with a term is a result of the eighth from either
beginning once named (`results_name8`; 8:D5's `result8_iff_A`, `_B` through
the naming map); and the empty state is a result of the ninth that no
sequence of the eighth reaches (`eighth_never_empty`, `empty9_is_new`;
8:D6's `Reach8.nonempty`). Computed on every run and the census
(`compare_with_seventh`, `compare_with_eighth`; 7:K1, 8:K1 computed again):
the results asserting nothing with `s`, read as their `r` parts, with their
rounds and their shortest-sequence counts, are exactly the seventh's at the
same bound and rounds, and so are those asserting nothing with `r`; under
any rewriting, the results with a term whose eighth-seed cost is within the
eighth's rounds (four fewer than the ninth's) are exactly the eighth's
results at the same bound on terms, each at the round its eighth-seed cost
formula gives; with the names kept, the eighth's results with their names
forgotten are results here. The independent counts agree too: the eighth's
counts of all well-formed two-relation states with `n ≥ 1` terms under any
rewriting are this derivation's, with 1 for `n = 0` (K1).

**D6. What every result has.** Every result is well formed and finite
(`Reach9.wf`); a result other than the empty state has a term (D2). Nothing
else is kept (N1, N6). 8:D6's "at least one term" fails at round 0.

**D7. Changes commute with one-to-one rewriting of both relations;
sequences keep their length; the empty state is its own only writing.**
`rename9` is the eighth's `rename8` with the names left out; naming and then
rewriting is rewriting and then naming (`rename8_name`, definitionally), so
8:D7's commutation lemmas give the ninth's by forgetting the names
(`rename9_addTerm`, …, `rename9_identify`), and `Step9.rename`,
`Reach9.rename`, `size_rename9`, `rename9_empty` follow (7:D7 on each part,
through `proj_rename9`). The exchange commutes with rewriting
(`rename9_swap`).

**D8. Reachability: a term decides; neither part imposes anything.** A
well-formed state `t` is reachable from a well-formed state `s` exactly when
`t` has a term or `s` is empty: `reach9_iff`. Necessity is D2. Sufficiency
(`reach9_of_nonempty`): with both `s` and `t` having a term, put both names
on a term of `s` and on a term of `t`; the eighth's criterion
(`reach8_of_names`, 8:D8) then applies with nothing to check, since the
names of a named state are one term at both ends, and its sequence forgets
to a sequence here. From the empty state additions reach everything
(D4(ii)). So 7:D8 survives on the shared terms; 8:D8's "the `s` part imposes
nothing" survives and so does its mirror (`criterion_survives7`:
reachability of two-relation states is reachability of either part under
the seventh seed; `criterion_survives8`: on states with a term the eighth's
criterion says "always"). Computed: the criterion agrees with a search along
the changes among the results within 3 terms and 7 rounds on every ordered
pair of the 140 results within 3 terms and 5 rounds (19 600 pairs; 19 461
reachable; the 139 unreachable are those into the empty state), the
seventh's criterion on either part agrees on every pair, and the eighth's
criterion agrees on every pair of results with a term (19 321 pairs).

**D9. Reachability is mutual among the results with a term, one-way out of
the empty state; any two results are comparable; every result with a term
reaches itself in two changes.** `reach9_symm`, `reach9_total`,
`empty9_never_returned`; the two-change cycle (`cycle2_9`, 8:D9's `cycle2_8`
through the naming map: add an assertion and remove it, or add a term and
identify it back), so the lengths of the sequences reaching a result with a
term are unbounded (`Reach9.cycles`, `Reach9.unbounded`) and infinitely many
sequences reach it; the empty state has no cycle (`no_cycle_at_empty9`) and
is reached by one sequence, the empty one. One-way reachability among the
results with a term is refuted (`no_return_fails9`, `antisymm_fails9`,
`length_not_unique9`). Computed: every result but the empty state has a
two-change cycle in every run (`results_with_a_two_change_cycle = results −
1`); 9 591 unordered pairs of different results reachable both ways among
the 139 results with a term of the reachability run — all of them.

**D10. Within the bound the exploration is complete; the frontier is exact;
the shortest-sequence counts are exact; the count is not a product.**
*Completeness.* Let the bound be `N` terms and `R` rounds. Every well-formed
state with at most `N` terms and size at most `R` lies at the end of the
sequence of D4(ii), whose states never have more terms than the target and
whose size rises by exactly one at each change; so every state on it is
within the bound and, by induction along it, found by the exploration in
round = size. Every explored state is a well-formed state within the bound
by construction. The results with `n` terms and total multiplicity `t`
(both relations) are counted independently by the eighth's orbit method
with two multiplicities on every cycle of the rewriting (8:D10, no change:
`count_free` mentions no name and no given), with `n = 0` giving the empty
state alone (`code/ninth/orbits.py`). **The count is not a product.** For
`n ≥ 2` the number of results with `n` terms exceeds the product of the
seventh's single-relation counts (`product_count`): the same rewriting must
fix both relations at once. With two terms and total 2 there are 20 results
and the product gives 16; with one assertion in each relation, 8 and 4 (K1;
`count_exceeds_product_for_two_or_more_terms`). For `n = 0` and `n = 1` the
two agree (`product_equals_count_for_at_most_one_term`). 8:D10 survives
verbatim, recomputed with one sameness and the empty state: the eighth's
count under any rewriting *is* this seed's count. The explored counts by
(terms, total) equal the independent counts restricted to `n + t ≤ R` in
every run and the census (`explored_equals_independent_count`), and the
counts agree with a listing of every writing for small `n` and `t`
(`tests/test_ninth_orbits.py`). *Frontier.* An attempt leaves the bound on
terms exactly when it is "add a term" on a result with `N` terms: one entry
per such result whose changes were attempted
(`frontier_entries_are_1_per_state_with_N_terms` true in every run); the
results of round `R` are the second part. *Shortest sequences.* A shortest
sequence is additions only (D4(vi)), so it never has more terms than its
target and the count is exact for every result within the bound
(`results_with_exact_sequence_count = results` in every run). *Rounds.* The
number of results of round `r` without any bound is the number of
well-formed states of size `r`, `Σ_{n ≤ r} count(n, r − n)`
(`layer_counts`); a result of round `r` has at most `r` terms, so rounds
`0 … N` of a run within `N` terms agree with it
(`rounds_agreeing_with_unbounded_formula` true in every run).

**D11. Two terms: the results of every round in closed form; one-term
results interleave.** With at most two terms the results of round `r` are:
the empty state (`r = 0`); the one-term states with `ara` `p` times and
`asa` `r − 1 − p` times, `r` of them (`r ≥ 1`); and, with two terms, the
eight multiplicities (four in `r`, four in `s`) summing to `t = r − 2`, up
to the swap of the two terms: the compositions of `t` into eight parts,
`C(t+7, 7)`, plus the ones the swap fixes (`ara = brb`, `arb = bra`, and the
same in `s`, so `t` even: `C(t/2+3, 3)` of them), halved —
`(C(t+7, 7) + [t even]·C(t/2+3, 3))/2`. Total
`[r = 0] + [r ≥ 1]·r + [r ≥ 2]·(C(r+5, 7) + [r even]·C(r/2+2, 3))/2` =
1, 1, 3, 7, 24, 65, 176, 403, 876, 1 725, 3 245, 5 731, 9 764, … : of
order `r⁷`, so 100 rounds would hold about 1.5 · 10¹¹ results. Proof: the
cost of each state with at most two terms is its size (D4), and the count
of two-term states of a given total is the orbit count under the one
non-trivial rewriting. Computed: `two_term_rounds_equal_closed_form` true on
all 12 rounds of the two-term run, and the closed form equals the
independent count for every total up to 10 (`two_term_closed_form_mismatches`
empty). **One-term results** asserting `ara` `p` times and `asa` `q` times
are reached by `C(p + q, p)` shortest sequences (the term, then the `p + q`
assertions in any order): 7:D11's "one shortest sequence" fails as soon as
both relations are used (`one_term_results_follow_the_binomial` true in
every run; 55 of the 78 one-term results of the two-term run have more than
one). For two or more terms the counts are computed per result (K7; O1).
The results whose two relations agree everywhere, with `n` terms and total
`t`, number the seventh's count with `n` terms and total `t / 2` for even
`t`, none for odd `t` (`agreeing_count`;
`relations_agreeing_equal_closed_form` true).

**D12. The two readings of sameness coincide.** The earlier derivations
read "differ only in how their terms are written" two ways: any rewriting
(FREE), or rewritings keeping the writing of `a` and of `b` (ANCHORED,
1:C4, 8:C4). With no `a` and no `b` there is nothing to keep: every
rewriting keeps the names, so the two readings give the same least writing
and the same results. 7:D12 survives; the one rewriting still acts on both
relations at once (8:C4). Not in Lean (the ANCHORED reading was never
formalised as a reading; `rename9` is the one rewriting); the proof is this
paragraph, and it is the reason there is one exploration per bound instead
of the eighth's four. Computed as a consequence: the eighth's ANCHORED
results with their names forgotten are exactly its FREE results (D5:
24 832 named results with `bra` forget to the 11 049 unnamed ones at 2
terms and 8 eighth rounds). Two states whose parts are the same up to
*separate* rewritings need not be the same result — that is the non-product
of D10, and it needs no names.

**D13. What the eighth's cost becomes.** The eighth's fewest changes,
`size − size(given) + 2·lost` measured from `arb`, does not survive: the
one-term state asserting nothing is one change from the empty state, while
under the eighth seed its named form has potential 5 and costs two changes
from `arb` (`eighth_cost_fails`, `costA8_oneTerm9`; 8:D4's `costA8`,
`fewest_changes8_lower_A` through the naming map); the eighth's beginnings
themselves cost 3 and 4 changes from here (`given.json`); `ara` once costs
2 here and 1 there; `asa` once costs 2 here and 3 there — the exchange keeps
the cost here and not under the eighth seed. Without `bra` the eighth's cost
equals this seed's on no result of the 3-term and 2-term runs
(`results_where_the_eighth_cost_equals_the_cost: 0`); at 5 terms, of the
10 415 results with a term, it equals on none, is below on 10 407
(`results_where_the_eighth_cost_is_below_the_cost`) and is above on the
remaining 8. With `bra` the two agree on 1 762 of those 10 415
(`results_where_the_eighth_cost_equals_the_cost`; below on 8 645, above on
the remaining 8), by coincidence of the numbers.
What survives is the size difference (4:D8, 8:D4 on states containing what
is given) with `size(given) = 0` (`size_difference_survives9`).

**D14. Nothing about the asserting holds in every result.** By D5 every
well-formed state is a result, so a statement holds in every result exactly
when it holds in every well-formed two-relation state; of the forty-two
statements tested (§6) each fails in some well-formed state — "at least one
term" (on either part) in the empty state, 8:D14's everywhere-true
statement — and each holds in some. Computed:
`statements_holding_in_every_result` is empty in every run.

**D15. The unchosen reading of identification.** Under the reading in which
a merged multiplicity is the *larger* of the parts instead of their sum, per
relation, the results are the same (every well-formed state: D4(ii)
identifies nothing), the reachability criterion is the same (D8's sequence
identifies terms only in states with nothing asserted at all, the eighth's
through the naming map), and the cost is the same (D4(i) needs only that a
change moves the size by at most one, which the larger-of-the-two reading
also gives: an identification then lowers the size by one or more). So the
two readings agree on everything computed here; 8:D15 / 7:D15 jointly, with
no `bra` to make the costs differ. Not in Lean; the proof is this
paragraph.

**D16. The exchange of the two relations is a symmetry.** Exchanging `r`
with `s` (`swap9`) carries every change to a change of the same kind in the
other relation (`Step9.swap`), every sequence to a sequence of the same
length (`Reach9.swap`), every result to a result at the same round
(`result9_swap`, `exchange_symmetry9`), and keeps the size (`size9_swap`)
and whether there is a term. A symmetry the eighth seed did not have: its
given lived in `r` (`asa` once costs 3 there and 2 here; `ara` once costs 1
there and 2 here). Computed: every exchange of an explored result is a
result at the same round with the same shortest-sequence count
(`every_exchange_is_a_result`, `every_exchange_has_the_same_round_and_sequence_count`
true in every run).

**D17. The interaction of the two relations is through the terms alone.**
An assertion of one relation leaves the other part exactly as it is
(`proj9_addAssertion_other`, `proj9_remove_other`); a term is added to both,
and an identification merges both, pair by pair (`proj9_addTerm`,
`proj9_identify`); a rewriting rewrites both (`proj_rename9`):
`interaction9`. There are no names. So the two relations share their terms
and their writing, and nothing else: the results are jointly free (D5), the
cost is a sum of the two totals and one count of terms (D4), the criterion
reads having a term (D8), and the count up to sameness is not a product
(D10). A sequence of the ninth projects to a sequence of the seventh on
either part, no longer (`Reach9.proj`). 8:D12 survives with the names
dropped.

## 5. What does not follow

Each item has two witnesses among the results, or a proof.

**N1. Anything about the asserting**, in either relation or jointly,
including "at least one term": every one of the forty-two statements tested
holds in some result and fails in another in every run
(`statements_that_do_not_follow`, `follows_*.csv`). In particular, nothing
in `s` (holds in the empty state and every seventh result read as `ofR`;
fails: the one-term state asserting `asa` once), nothing in `r` (the
exchange), `r` and `s` agree everywhere (holds in the empty state and any
`(M, M)`; fails: `ara` once, nothing in `s`), some pair asserted in both
relations (holds: `ara` and `asa` once; fails: the empty state), the state
unchanged by exchanging the relations (holds in the empty state; fails:
`ara` once), nothing at all (holds in the empty state alone).

**N2. That there is a term; that there are exactly two, or at least two.**
The empty state has none (round 0); the one-term state has one (round 1);
the two-term state has two (round 2); the three-term state three (round 3).

**N3. That the `s` part determines anything about the `r` part, or the
converse.** For every well-formed `r` part every well-formed `s` part on the
same terms makes a result (D5): the pairs `nothing | nothing`, `ara | nothing`,
`nothing | asa`, `ara | asa` on one term are all results of rounds 1, 2, 2, 3.

**N4. That a result is reached by one sequence only, or by finitely many;
that results of one round are reached by equally many shortest sequences.**
Every result with a term is reached by infinitely many sequences (D9). The
empty state is reached by one shortest sequence; the one-term state
asserting nothing by one; `a; ara asa` by two (`C(2, 1)`); `a; ara(2) asa`
by three. 20 of the 10 416 results of the 5-term run have one shortest
sequence; 25 of the 22 021 two-term results (K7).

**N5. That results of one round with equally many terms have equally many
changes.** `C(n, 2) + d_r + d_s + 1 + 2n²` depends on `d_r + d_s`: 3 for
`a; nothing asserted` and 5 for `a; ara asa`, both with one term; 10 for
`a b; nothing asserted` and 12 for `a b; arb asb`, both with two terms.

**N6. That a multiplicity never falls; that the number of terms, either
total, the size, or the fewest classes of a split in either relation never
falls; that no `xrx` or no `xsx` stays asserted.** All refuted by witnesses
(`changes_lowering` in every run; `tests/test_ninth_follows_invariants.py`).
In the 5-term run 6 984 changes lower the number of terms, 7 192 a
multiplicity, 14 176 the size, 4 809 make some `xrx` asserted and 4 809 some
`xsx` asserted.

**N7. That a state is contained in its outcome; that a sequence carries
every assertion somewhere.** Refuted, as 7:N7, 8:N7 through the maps: the
one-term state asserting `ara` once and its removal.

**N8. The eighth's notions of `bra`, the names, the given assertion and the
destroyed givens.** Without object: the seed names nothing and gives
nothing. 8:D1, 8:D2, 8:D8's names criterion, 8:C2″ have nothing to refer to.
8:D13 splits: the clause that `s` adds nothing to what is given (`asb`
added to `arb` is a result no sequence of the sixth reaches) is without
object, there being no `arb`; the clause that the `s` part costs exactly
its total (`s_costs_its_total`) survives jointly as `Σ s` (D4,
`cost_adds_up9`) — per-relation it is the seventh's cost of that part,
which here is the part's size (§7, §8).

**N9. That reachability among the results with a term is one-way, or that
two results are incomparable.** Refuted and derived respectively (D9).

**N10. That the beginning is returned to, or has a cycle.** Refuted (D2).

**N11. That the cost is the sum of the two parts' seventh costs.** Refuted
for every state with a term (D4, `cost_not_sum_of_parts9`); holds of the
empty state (`0 = 0 + 0`).

**N12. That the number of results with `n` terms is the product of the
seventh's single-relation counts.** Refuted for `n ≥ 2` (D10, K1); holds for
`n = 0` and `n = 1`.

**N13. That one-term results have one shortest sequence.** Refuted when both
relations are used (D11); holds when one of `p`, `q` is zero.

**Refuted** (each a proved impossibility): a change other than adding a term
on the empty state (R1, D1); a sequence from a state with a term to the
empty state, or a non-empty sequence from the empty state to itself (R2,
D2); a sequence of changes to a result shorter than its size (R3, D4); a
well-formed state that is not a result, or a pair of well-formed parts on
the same terms that is not (R4, D5); a change that keeps the size, or the
round, where it was (R5, D4(v)); a shortest sequence containing a removal or
an identification (R6, D4(vi)); two results with a term that do not reach
each other, or two results neither of which reaches the other (R7, D9); a
rewriting barred by the names — the two readings of sameness differing (R8,
D12); the eighth's cost as the fewest changes here (R9, D13); a result
reached by no sequence at all (R10, D5); the cost as the sum of two seventh
costs, on a state with a term (R11, D4); the count of results as the product
of the single-relation counts, for two or more terms (R12, D10).

## 6. The exploration

**Protocol.** From the empty state, under the one reading of sameness: round
by round, every change on every result first reached in the round before
(C6), each result's changes fewest additions first — identifications,
removals in `r`, removals in `s`, a term, then every ordered pair as an
addition in `r`, then in `s` (`C(n, 2) + d_r + d_s + 1 + 2n²` changes, every
one performed; one on the empty state). Each attempt records whether its
outcome asserts some `xrx`, and some `xsx`, while the state asserts none.
Three explorations (C8′): the main run (5 terms, 8 rounds), a deeper run (3
terms, 9 rounds), and the two-term run (12 rounds). Beside every run and the
census the seventh derivation's exploration is made at the same bound and
rounds, and the eighth derivation's explorations at the same bound on terms
with four rounds fewer, from both its beginnings under both its readings,
and compared (D5). Files per run (`evidence/ninth/`, tag
`bound{N}_rounds{R}`): `results_*.csv`, `added_*.csv`, `frontier_*.csv`,
`rounds_*.csv`, `follows_*.csv`; `reach_bound3_rounds5.csv`; the full
attempt log `attempts_bound2_rounds3.jsonl`; `counts.csv`, `given.json`,
`summary.json` (every check, per run), `lean_axioms.txt`, `MANIFEST.sha256`.

**Results within the bound** (K1, K2). Every check of every run passes
(`summary.json`; `python code/generate_ninth.py` prints one line per run).

| run | results | by terms | asserting nothing with `s` (the seventh's) | asserting some `xrx` | shortest sequences (total) |
|---|---|---|---|---|---|
| 5 terms, 8 rounds | 10 416 | 1 / 36 / 1 519 / 5 715 / 2 769 / 376 | 799 | 5 378 | 8 142 160 |
| 3 terms, 9 rounds | 25 965 | 1 / 45 / 3 235 / 22 684 | 1 056 | 15 931 | 75 802 736 |
| 2 terms, 12 rounds | 22 021 | 1 / 78 / 21 942 | 524 | 17 976 | 1 636 181 431 |
| census, 6 terms, 8 rounds | 10 458 | 1 / 36 / 1 519 / 5 715 / 2 769 / 376 / 42 | 813 | 5 389 | — |

In every run the results asserting nothing with `s` (and those asserting
nothing with `r`) are exactly the seventh derivation's at the same bound and
rounds, at the same rounds here, with the same shortest-sequence counts
(7:K1, 7:K2, 7:K7 computed again). The results with a term whose
eighth-seed cost is within the eighth's rounds are exactly the eighth's
under any rewriting — 1 467 / 1 690 (with / without `bra`) at 5 terms and 4
eighth rounds; 5 645 / 5 890 at 3 terms and 5; 11 049 / 10 581 at 2 terms
and 8 — each at the round the eighth's cost formula gives, and the eighth's
results with the names kept forget to the same states (8:K1, 8:K2 computed
again). Every count by terms and total multiplicity equals the independent
count (`explored_equals_independent_count`, D10), and every result's round
is its size (D4).

**Rounds** (K2). 5 terms (`rounds_bound5_rounds8.csv`): new results per
round 1, 1, 3, 8, 29, 104, 419, 1 778, 8 073; of which asserting nothing
with `s` 1, 1, 2, 4, 10, 24, 64, 177, 516 (the seventh's); without any bound
on terms 1, 1, 3, 8, 29, 104, 420, 1 783, 8 115 (`layer_counts`; rounds 0–5
agree with the run, as every round up to `N` must). 3 terms: 1, 1, 3, 8, 28,
99, 378, 1 433, 5 320, 18 694 (rounds 0–3 agree). Two terms: the closed form
of D11 on all 12 rounds. Every round of every run has a new result.

**Attempts** (K3). 57 919 changes attempted in the 5-term run (43 785 of
them additions), 4 809 making some `xrx` asserted and 4 809 some `xsx`
asserted; 1 in round 1 (the term), 4 in round 2 (a term; `ara`; `asa`;
identifying nothing yet). The totals equal
`C(n, 2) + d_r + d_s + 1 + 2n²` summed over the results whose changes were
attempted, in every run. Of the 57 919 changes checked in the 5-term run,
43 743 raise the round by one and 14 176 lower it by one; none keeps it
(D4(v)). 58 405 changes attempted in the census.

**Frontier** (K5). Every result with `N` terms whose changes were attempted
has one entry (the term): 42 in the 5-term run, 5 715 in the 3-term run,
12 190 in the two-term run, 5 in the census. The second part, the results of
the last round whose changes await: 8 073 results with 252 327 changes (5
terms), 18 694 with 477 053 (3 terms), 9 764 with 143 478 (2 terms), 8 110
in the census.

**Results by what they add to what is given** (K6;
`added_bound5_rounds8.csv`). A result of round `r` adds `n` terms and
`r − n` assertions, `n = 0 … min(r, 5)`: one result adds (0, 0) (the empty
state), `r` add (1, `r − 1`) (the one-term states, D11), the two-term counts
of D11 add (2, `t`), and so on; nothing is ever negative, since nothing is
given to lose.

**Statements** (K7; `follows_*.csv`). Forty-two statements tested: the
earlier unnamed ones on each part, the eighth's joint ones, nothing at all,
and unchanged by the exchange. None holds in every result (N1). First
failing rounds include: at least one term (either part) 0; every term
mentioned, every term first 1; no `xrx`, nothing asserted, some `xrx`, both
ways never 2; both ways always 3; passes on 4.

**Reachability within 3 terms and 5 rounds** (K8;
`reach_bound3_rounds5.csv`, `summary.json` `reachability`), along the
changes among the results of 3 terms and 7 rounds: 140 results (139 with a
term, 62 asserting some `xrx`, 62 some `xsx`); 19 600 ordered pairs, 19 461
reachable, 139 unreachable — exactly the pairs into the empty state; 9 591
unordered pairs of different results reachable both ways — every pair of
results with a term; the criterion agrees with the search on every pair; the
seventh's criterion on either part agrees on every pair; the eighth's
criterion agrees on every one of the 19 321 pairs of results with a term.

**Census** (6 terms, 8 rounds, counts only): 10 458 results (1 / 36 / 1 519
/ 5 715 / 2 769 / 376 / 42 by terms); 58 405 changes attempted, 4 834 making
some `xrx` asserted and 4 834 some `xsx`; the seventh's 813 results are the
results asserting nothing with `s` and those asserting nothing with `r`; the
eighth's 1 468 / 1 691 results (4 eighth rounds, with / without `bra`, any
rewriting) are the results with a term of eighth-seed cost at most 4; every
check passes.

**Independent counts** (K1; `counts.csv`): all well-formed two-relation
states with `n ≤ 5` terms by total multiplicity `0 … 10`, up to rewriting:
1, 66, 21 942, 2 190 216, 61 482 917, 633 609 381 for `n = 0 … 5`; beside
them the seventh's single-relation counts, their product, the two-term
closed form, and the count of results whose relations agree everywhere. The
product equals the count for `n ≤ 1` and is smaller from `n = 2` on (20
against 16 with two terms and total 2; 8 against 4 with one assertion in
each). The eighth's counts by destroyed givens add up to these for every
`n ≥ 1` (`eighth_counts_by_destroyed_givens_add_up_to_these`; 8:K1 computed
again).

**What is given** (`given.json`): the empty state, size 0; its one change,
a term, performed; its one result after one change, `a; nothing asserted`;
it reaches the one-term state, which does not reach it; it has no two-change
cycle; the one-term state costs 1 here (2 and 3 under the eighth seed, from
its two beginnings) and `a; ara` costs 2, `a; asa` costs 2 (the exchange);
the eighth's beginnings `a b; arb` and `a b; arb bra` cost 3 and 4 from here
(0 there); `a b; arb asb` costs 4 here and 1 there; the empty state has no
cost under the eighth seed.

**Reproducibility** (K9, K10). `python code/generate_ninth.py` rewrites
every computed file of `evidence/ninth/`; `--check` regenerates into a
temporary folder and compares byte for byte (matched); `MANIFEST.sha256`
lists every file's hash. `python code/lean_report_ninth.py` builds all nine Lean
libraries and rewrites `evidence/ninth/lean_axioms.txt` (every theorem
within `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit` or
declared axiom in `lean4/`). Tests of `code/ninth/` plus the eight earlier
derivations; line and branch coverage of all of `code/` above the gate,
every evidence module fully covered (`python code/xry/gate.py
coverage.json`); `mypy --strict` clean; the prose watchlist clean on the
tracked tree. This paper's three watched hits (one enumeration term, two
algorithm terms) are all in §10, pinned in `ci/prose_watchlist.json`.

## 7. What survives with nothing given and two relations

The task asks whether the seventh's collapses and the eighth's independence
compose, and where they do not: what the cost, the reachability, the results
and their count are when there is nothing given *and* two relations. In one
line each, with the Lean statements of `Ninth/Compare.lean`:

- **The seventh's cost = size survives**, with both totals in the size
  (`fewest_changes9`, `cost_survives7`). The eighth's additivity survives as
  `size = cost₇(r) + Σ s = cost₇(s) + Σ r` (`cost_adds_up9`) and **does not
  survive as** `cost₇(r) + cost₇(s)` (`cost_not_sum_of_parts9`,
  `one_term_parts9`). The eighth's cost with `lost` on `r` does not survive
  (`eighth_cost_fails`); the size difference does, with `size(given) = 0`
  (`size_difference_survives9`).
- **The seventh's has-a-term criterion survives** on the shared terms
  (`reach9_iff`, `criterion_survives7`); the eighth's "the `s` part imposes
  nothing" survives and so does its mirror. The eighth's names criterion is
  without object and is replaced by this one (`criterion_survives8` on
  states with a term as "always"; the empty-state clause is the seventh's).
- **The seventh's one sameness survives**; the rewriting still acts on both
  relations (D12, `rename9`).
- **The eighth's jointly-free results survive**, empty included
  (`results_pair9`, `result9_iff`); the seventh's results are exactly those
  asserting nothing with `s`, and by the exchange those asserting nothing
  with `r` (`results_ofR7`, `results_r_iff9`, `results_s_iff9`); the eighth's
  results are exactly those with a term (`results_forget8_A`, `_B`,
  `results_name8`); the ninth has one result no eighth sequence reaches, the
  empty state (`empty9_is_new`).
- **The eighth's count-not-a-product survives** for `n ≥ 2` and equals the
  product for `n ≤ 1` (D10), with one sameness and the empty state counted.
- **Separability**, read as telling the two named terms apart, has nothing
  to apply to. What replaces it is having a term, jointly (the terms are
  shared). Read as the fewest classes of a split per relation, it is a
  function of each part and can fall (N6).
- **The interaction is through the terms alone** (`interaction9`, D17): an
  identification merges both; a rewriting rewrites both; an assertion of one
  leaves the other as it is. The eighth's "through the terms and the names"
  drops the names.
- **The exchange of the two relations is a new symmetry**
  (`exchange_symmetry9`, D16), which the eighth's given forbade.

**Where they compose.** 7:D4, 7:D8, 7:D12 hold with two relations. 8:D5
holds with nothing given (empty included). 8:D4 holds as
`size = cost₇(r) + Σ s`, not as a sum of two seventh costs. 8:D13's
`s_costs_its_total` survives jointly as that `Σ s` (D4, `cost_adds_up9`);
its `asb`/`arb` clause is without object (N8). 8:D10 holds for `n ≥ 2` with
one sameness and with the empty state counted.

**Where they interfere.** Shared terms in the cost; shared rewriting in the
count; `C(p + q, p)` interleaving of additions; exchange symmetry.

**What fails as stated.** 8:D4-with-`lost`, 8:D8 names, 8:D14 at-least-one
term, 7:K one-term-one-sequence, and every eighth claim about `a`, `b`,
`arb`, `bra`.

## 8. Alternatives: kept, or eliminated by proof

| Alternative | Kept / eliminated |
|---|---|
| a beginning other than the empty state | eliminated as a starting point by the seed (G3″); every well-formed state is a result of the empty one (D5); kept as alternatives that change the cost measured from the start, not the set of results |
| FREE / ANCHORED sameness | one reading: the two coincide with no names (D12); nothing is computed twice |
| rewriting both relations vs separately | both at once (the seed writes the terms, not the relations); separate is why the count is not a product, not a reading of sameness |
| identification: multiplicities add up / the larger of the two, per relation | the first chosen and computed; the second kept as an alternative with the same results, reachability and cost (D15) |
| the other orders of attempts (relations, kinds) | not computed; same results and rounds (D4) |
| a bound on terms alone | eliminated: the results within it are infinite (D5) |
| every well-formed two-relation state within the bound, up to sameness | kept; none dropped (D10) |
| `bra` / something in `s` "not given" | gone: the ninth seed has no such list |

Earlier results that fail, or change shape, under the ninth seed, each with
the reason: 8:C2″, 8:C4's two readings, 8:D1, 8:D2, 8:N2 (`bra`) — without
object; 8:D4 with `lost` on `r`, 6:D8, 5:D8 — do not survive,
`eighth_cost_fails`; the size difference (4:D8) survives with
`size(given) = 0`; 8:D8 (the names criterion) — without object, replaced by
7:D8 (D8); 8:D5 (every well-formed state with a term) — extends by one
result, the empty state (D5); 8:D6 / 8:D14 "at least one term" everywhere —
fails at round 0 (D14); 8:D4 as a sum of two per-relation *costs* — the
terms are counted twice (`cost_not_sum_of_parts9`); 8:D13 splits: `asb`
added to `arb` (`s` adds nothing to the given) — without object; `s` costs
its total — survives jointly as `Σ s` (D4, `cost_adds_up9`), not as a
clause about `asb`; 8:D12 interaction through terms *and names* — through the terms
alone (D17); 7:D3 — restated as 8:D3, `+ d_s + n²`; 7:D11 / 7:K one-term
results have one shortest sequence — fails, `C(p + q, p)` (D11); 7:D4
survives with both totals; 7:D8, 7:D12 survive; 8:D5, 8:D10 survive as
stated above; 8:D3 survives; 7:D1, 7:D2, 7:D5 survive with two relations;
every K-claim of the seventh — computed again on the results asserting
nothing with `s` (and with `r`); every K-claim of the eighth — computed
again on the results with a term (§6). Everything else cited stands with
the re-check given at its citation.

## 9. Open

- O1. A closed form for the number of shortest sequences reaching a result
  with two or more terms: computed per result within the bound (K7), exact
  there (D10); with one term it is `C(p + q, p)` (D11).
- O2. Results beyond the declared bounds, listed: the frontier is exported
  (both parts); the census counts at 6 terms; the seed's 100 rounds with two
  terms are given in closed form (D11), not listed.
- O3. Lean statements of D3's change-count formula, of D10's completeness,
  of D11's closed form and binomial, of D12 (the coincidence of the two
  readings of sameness), of D15 and of the non-product count (D10): proved
  in the paper and checked by computation. (`Step9.proj` is not a statement
  of the formula.)
- O4. The eighth paper's O4 (cost from a beginning asserting something with
  `s`) remains uncomputed; it is moot for the chosen beginning.
- O5. The earlier papers' O1 (multiplicity) stays closed by the fourth seed;
  their O2 (the number of new results beyond the bound) is given by the
  series and the size for any round (D10, `layer_counts`) and not listed.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Two-coloured directed multigraphs with loops, unlabelled, under vertex
  insertion, vertex identification, and arc insertion and deletion,
  generated from the empty graph.** D5 is that every finite such two-coloured
  multidigraph is generated, including the empty one, and that the colour
  classes are independent as sets: any `r`-graph and any `s`-graph on the
  same vertex set combine. D8 is that the edit graph on them is strongly
  connected except for the empty graph, which is a source: contraction never
  removes the last vertex, jointly for both colours.
- **Graph edit distance from the empty graph, with two arc colours.** D4 is
  the observation that, with unit cost per edit and contraction allowed, the
  edit distance from the empty two-coloured multigraph to any two-coloured
  multigraph is its number of vertices plus its number of arcs of either
  colour (with multiplicity), attained by insertions alone — the
  potential-function argument of the first derivation with no marks to
  destroy, the eighth's additive form with the seventh's cost on each colour
  and the vertices counted once. The failure of `cost₇(r) + cost₇(s)` is the
  observation that adding the two one-colour distances from empty double-counts
  the vertices.
- **Pólya enumeration of two-coloured multigraphs.** The independent count
  (D10) is the eighth's cycle-index computation with the empty vertex set
  added; the departure of the count from the product of the single-colour
  counts is the familiar fact that the cycle index of a group acting on a
  product of two sets is not the product of the cycle indices. With two
  vertices (D11) the count is `(C(t + 7, 7) + [t even]·C(t/2 + 3, 3)) / 2`.
- **Free generation of a pair of binary relations on a common carrier from
  nothing.** That the first move from nothing is forced (D1), that nothing
  about the generated structure is forced (D14) and that every structure is
  reached (D5) is the statement that the four operations generate all finite
  two-relation states from the empty one, with the vertex count as the one
  quantity that only insertion raises and only contraction lowers and that
  never returns to zero (D2), shared by both relations.

What appears to be specific to this seed: that turning the seventh's dial
(nothing given) and the eighth's (a second relation) at once lets the
seventh's three collapses and three of the eighth's four independence
claims hold together, the one failure being that a sum of two seventh costs
counts the shared terms twice; that the eighth's given, which had broken
the exchange of the two relations, being gone, the exchange is a symmetry
of the results, the cost and reachability; that the seventh's one-term
"one shortest sequence" fails by the interleaving of the two relations'
additions; and that the seventh's and eighth's results, criteria, costs and
counts are recovered exactly on the results asserting nothing with `s` and
on the results with a term, through four definitional maps
(`Ninth/Compare.lean`), the whole difference from the eighth being one
state and the collapse of the cost, and from the seventh being a second
multiplicity function on the same terms.
