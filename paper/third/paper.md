# What follows from `arb`, no `xrx`, and two kinds of change

Third derivation. Input: `prompt/third/seed_prompt.md`. Task:
`prompt/third/prompt.md`. Claim IDs refer to `paper/third/claim_ledger.md`;
an ID written `1:D8` refers to the first derivation's ledger,
`paper/claim_ledger.md`, and its paper `paper/paper.md`; one written `2:D8`
to the second derivation's, `paper/second/claim_ledger.md` and
`paper/second/paper.md`. Lean names in the namespace `Seed.Third` are in
`lean4/Third/`; names in `Seed.Second` are the second derivation's
(`lean4/Second/`), names in `Seed` the first's (`lean4/H3V7N5QF/`). The axiom
report for every theorem cited here, of any of the three libraries, is
`evidence/third/lean_axioms.txt`. Computed files are in `evidence/third/`,
written by `python code/generate_third.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; the unchosen
readings are listed), **derived** (proved), **computed** (output of `code/`),
**refuted** (proved impossible), **open**.

Where a result of the first or second derivation is used it is cited and
re-checked from the third seed. The re-check is one of four kinds. *(no
change)*: the statement mentions no change of state, only relations, states,
the state operations `addTerm`, `addAssertion` (shared by all three seeds) or
a rewriting of terms, so the statement and its proof stand as they are.
*(embedding)*: the statement is about the second seed's changes `Step3` or
sequences `Reach3`, or the first seed's `Step`, `Reach`; every change of the
third seed is a change of the second (`Step2.toStep3`, `Reach2.toReach3`) and
hence of the first (`Step2.toStep`, `Reach2.toReach`), so the statement
restricts to the third seed, and the restriction is itself a Lean theorem.
*(re-proved)*: the earlier proof went through an identification, or the
earlier statement is replaced by a stronger one proved from the third seed.
*(computed again)*: a computed statement re-run from the third seed's own
exploration and compared with the earlier one. Results of the earlier
derivations that fail under the third seed are listed in §7.

## 0. Findings in brief

1. The third seed is the second with one kind of change struck out:
   identifying two terms. Both remaining kinds add; nothing is ever taken away
   (given, §1).
2. `a` and `b` are two terms; there are exactly two beginnings, with and
   without `bra`; the one without reaches the one with in one change, and the
   one with never reaches the one without (D1, D2, R8) — as under the second
   seed.
3. Every change leaves its state contained in its outcome: every term, every
   asserted `xry` and both names stay in place (D5). This is the second
   derivation's carrying map with the identity as the map, and it says more:
   the assertions themselves persist, not only their images. Hence what is
   given survives (D6), no obstruction is ever cleared (D7), the numbers of
   terms and of assertions never decrease (D6; the second derivation's N8 now
   follows), and the fewest classes of a split never decreases (D13).
4. The only obstructed changes are the additions of some `xrx` (D3). The
   obstruction is the assertion the change itself would add, so "remove the
   obstruction" is impossible under one reading and coincides with refusal
   under the other (R3, C7); an obstructed change is refused or built around
   (N6).
5. The results are exactly the legal states containing what is given — the
   same set as under the second seed, in the same rounds (D9). The second
   derivation's run without identifications, made there as a check, is here
   the whole exploration; the two agree result by result, round by round and
   attempt by attempt in all four runs and both census runs.
6. Size rises by exactly one per change. So every sequence of changes from
   what is given to a result has the same length, the size difference (D8): a
   result is met in one round only, no order of attempts can move it to
   another round, and the first derivation's term for destroyed givens is zero
   on every result. The number of sequences reaching a result is computed for
   every result within the bound; it is not one in general (N9).
7. Reachability between results is containment, up to rewriting under FREE
   (D12), and it is one-way (D13): two results reachable from each other are
   the same result, a result once left is never returned to, and only what is
   given reaches what is given. The second seed's cycles are gone: within 3
   terms (names kept, without `bra`) it reached 439 of 1 156 ordered
   pairs where this seed reaches 294, and no pair of different results is
   reachable both ways where the second had 34 such pairs.
8. 100 rounds cannot be listed: every round has a new result. Bounds as in the
   second derivation: 5 terms (any rewriting), 4 terms (names kept; a
   counts-only census at 5). Within the bound the exploration is complete,
   certified by an independent count; the frontier is exported exactly (D14).
   Both directions of the reachability criterion are in Lean, one of which the
   second derivation left open (2:O3); the within-bound completeness (D14) and
   the FREE-reading characterizations (D8, D9) are proved in the paper and
   checked by computation, as the seed's Lean model does not reach them.

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2 | An assertion is written `xry`, where `x` and `y` are terms. |
| G3 | `arb` is asserted. |
| G4 | For no term `x` may `xrx` be asserted. |
| G5 | Whether `bra` is asserted is not given. |
| G6″ | A change is exactly one of: adding a term; adding an assertion. Nothing else is a change. |
| G8 | A change that makes some `xrx` asserted is obstructed. |
| G9 | An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which; record the change, the obstruction, the answer. |
| G10 | A refused change is recorded and changes nothing. |
| G11 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, prove what is complete within it. |
| G14 | Any outcome is valid. |

G6″ is the only sentence that differs from the second seed, and the second
seed's sentence on what identifying does (the earlier G7) is gone with it
(`diff` of the two files; `research/third/reading_the_seed.md`). G1–G5 and
G8–G14 are the earlier derivations' G1–G5, G8–G14 word for word.

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry`, asserted | given (G1–G3) | |
| an assertion has a first and a second term | derived (1:§2, no change) | the seed treats `arb` and `bra` as different |
| asserted is yes/no, no multiplicity | chosen (C1) | unchosen: multiplicity; open O1 |
| legal state (no `xrx`) | given (G4) | |
| `a`, `b` are two terms | derived (D1) | |
| what is given has exactly the terms `a`, `b` | chosen (C2) | unchosen: more to begin with; harmless (D9) |
| two alternatives for what is given | derived (D2) | given C2 |
| supply of letters not capped | chosen (C3) | harmless for results and fewest changes; not claimed for builds |
| `r` does not write a term | chosen (C9) | writing only |
| change, two kinds | given (G6″) | |
| non-changes; a new term has no assertion; an added assertion is between terms there | chosen (C5) | |
| the order of the two kinds | chosen (C6) | both add one; the seed's order of kinds |
| obstructed change | given (G8) | characterised: derived (D3) |
| the obstruction of a change | chosen (C7) | the assertion that would be `xrx`: the one the change adds |
| refuse / remove the obstruction / build structure | given (G9, G10) | content: chosen (C7); removal impossible or refusal: refuted (R3); results independent of the choice: derived (D10) |
| containment of a state in its outcome | derived (D5) | the second derivation's carrying map, restricted |
| result | chosen (C6) | a legal state up to sameness |
| the results, as a set | derived (D9) | legal states containing what is given; the second derivation's set |
| sameness | given (G12) | two readings, both kept: chosen (C4) |
| terms and assertions added to what is given | given (G11) | counted against `a`, `b`, `arb` for both beginnings, as in 1:§2; never negative, never decreasing (D6) |
| round; what counts as one change | chosen (C6) | the round of a result does not depend on the order of attempts (D8) |
| bound, frontier | given (G13) | bound on terms: chosen (C8) |
| size, cost, length of a sequence | derived (D8) | size = terms + assertions; every sequence has the same length |
| number of sequences reaching a result | computed (K7) | exact within the bound; no closed form sought (O5) |
| reachability between results | derived (D12) | containment, one-way (D13) |
| fewest classes of a split | derived (D13) | never decreases (2:D13, embedding) |
| counts of results | computed (K-claims) | the second derivation's (2:K1), computed again |

## 3. Readings that had to be chosen

The readings C1–C4, C8, C9 are the earlier derivations', unchanged in wording;
C5–C7 are restated where the third seed changes what they imply.

**C1. Asserted is yes or no.** As 1:C1. Unchosen: multiplicity (O1).

**C2. To begin with there are exactly the terms `a` and `b`.** As 1:C2.
Unchosen: further terms or assertions to begin with. Every such beginning is a
legal state containing `arb`; by D9 it is a result of the chosen beginning,
reached by additions, and its own results (the legal states containing it) are
among the chosen beginning's results. So the unchosen reading moves the
starting point and adds no result.

**C3. No cap on the number of terms.** As 1:C3. Under this seed no sequence
of changes ever has more terms than its last state (D5), so a cap `L ≥ 2`
leaves every statement about results with at most `L` terms, their fewest
changes and their sequences unchanged. Builds need one term more than the
state (D10); nothing is claimed for them under a cap.

**C4. Sameness, two readings, both kept.** FREE and ANCHORED as 1:C4. All
computations are done under both.

**C5. Non-changes.** Adding what is asserted changes nothing, so by G6″ it is
not a change; a new term comes with no assertion; an added assertion is
between terms already there. This is 1:C5 without its clauses on removal and
on identifying a term with itself, which have no object under this seed.

**C6. Results and rounds.** As 1:C6: a result is a legal state up to sameness;
round `k` attempts every change on every result first reached in round
`k − 1`; a performed change counts one; a refused change is an attempt of its
round that changes nothing; the further changes of an answer count one each.
Both kinds add one, so "fewest additions first" does not order them; each
result's changes are attempted in the seed's order of kinds — adding a term,
then adding an assertion. Unchosen: the other order; an obstructed change and
its answer counted as one. The order cannot move a result to another round:
every sequence of changes reaching a result has the same length (D8), so the
round of a result is derived, and the order fixes only which attempt is
recorded first. Counting an answered change as one would change the rounds
(a build's two additions would count as one, so `a b c; arb arc` would be met
in round 1 instead of 2) but not the results (D10), as under the second seed
(2:C6, 2:§7).

**C7. Obstruction and answers.** The obstruction of a change is the set of
assertions that would become some `xrx` (as 1:C7). Under this seed only adding
`xrx` is obstructed (D3), so the obstruction is the one assertion the change
itself would add. *Refuse*: recorded, nothing changes. *Remove the
obstruction*: two readings, both kept. (i) Un-assert `xrx` after asserting it,
then the change stands — no change un-asserts (D7), so this answer is recorded
as impossible on every obstructed attempt:
`"remove the obstruction": "impossible: the obstruction is the assertion the
change itself adds; no change un-asserts it, and not adding it is refusal"`.
(ii) Do not assert it — that is to withdraw the change, which coincides with
refusal and adds no result. The second derivation's third reading, moving the
obstruction by identifying one of its terms with a third, has no object here.
*Build structure*: by additions, reach a legal state that stands for the
would-be outcome — read with the added term as `x`, it is exactly that outcome
— fewest additions first: add a term `t` and `xrt` or `trx` (D10). The earlier
derivations said "identifying the added term back gives the outcome";
identification is not a change here, so the same criterion is kept as a
relation between states (`is_build_of` in `code/xry/changes.py` computes it
from the map of terms alone). Unchosen: any further additions at all count as
a build; by D10 the results are the same set under any reading in which the
further changes are changes of the two kinds. "Declare which" is read as in
1:C7: every answer is recorded with its kind and all are kept; the seed does
not fix one (N6).

**C8. Bound.** As 2:C8: at most 5 terms under FREE and 4 under ANCHORED for
the exported files (9 841 / 9 212 and 1 090 / 545 results); under ANCHORED a
census at 5 terms (90 562 / 45 281 results) records counts and the same checks
but writes no per-result file and does not export its frontier. The same
bounds as the second derivation's were kept so that the two explorations can
be compared file by file; the third attempts fewer changes per result and
completes faster.

**C9.** `r` writes assertions, not terms.

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. `a` and `b` are two terms.** If they were one, `arb` would be `xrx`.
Lean: `given_distinct` (1:D1, no change).

**D2. Exactly two beginnings, one way between them.** On the terms `a`, `b`
alone a legal state containing `arb` asserts `arb` only or `arb` and `bra`,
and these differ: `two_states_on_given_terms`, `two_states_differ` (1:D2, no
change); computed, `evidence/third/given.json` (`count: 2`). The beginning
without `bra` reaches the one with it by adding `bra`: `givenA_to_givenB2`
(2:D2's `givenA_to_givenB3`, re-proved as a change of this seed). The other
direction is impossible: `givenB_never_givenA2` (2:D2's `givenB_never_givenA`,
embedding; R8).

**D3. Which changes are obstructed.** On a legal state an attempt makes some
`xrx` asserted exactly when it is the addition of some `xrx`; adding a term,
or `xry` with `x` and `y` two terms, is never obstructed. Lean:
`Try2.obstructed_iff`, `Try2.legal_iff` (an unobstructed attempt is exactly a
performed change), `addTerm_unobstructed`; from the first derivation
`addAssertion_legal_iff`, `addTerm_legal`, `adding_xrx_always_obstructed`
(1:D3, 1:D4, no change: each is about one state operation); the earlier
`identify_legal_iff` has no object here. Computed on every change of all 69
legal states written on at most 3 terms:
`tests/test_third_changes.py::test_obstructed_exactly_when_xrx_is_added`. So
a result with `n` terms and `m` assertions has `1 + n² − m` changes, `n` of
them obstructed (computed against the exploration in every run:
`attempts_equal_formula_1_plus_n_squared_minus_m`, `obstructed_equal_formula_n`
in `summary.json`).

**D4. Adding `xrx` is obstructed in every state**, and stays so after every
sequence of changes. Lean: `adding_xrx_always_obstructed` (1:D4, no change),
`Reach2.xrx_still_obstructed`.

**D5. Containment.** Every change leaves its state contained in its outcome:
every term is still a term, every asserted `xry` is still asserted, the names
are where they were (`Step2.contains`; the structure `Contains`). Containment
composes, so every sequence of changes leaves its start contained in its end
(`Reach2.contains`), and it is one-way: two states contained in each other are
one state (`Contains.antisymm`). Containment is the second derivation's
carrying map with the identity as the map (`Contains.carries`; 2:D5, embedding
— every sequence of this seed is a sequence of the second, `Reach2.toReach3`,
and carries by `Reach3.carries`), and it says more than the carrying map did:
the assertions themselves persist, where the second seed kept only their
images under the identifications made since.

**D6. What is given survives; nothing decreases.** After any sequence of
changes every term and every assertion of the start is still there
(`Reach2.term_persists`, `Reach2.asserted_persists`), the names are unchanged
(`Reach2.name_a`, `Reach2.name_b`), so with names kept `a` and `b` are two
terms (`Reach2.names_apart`), `arb` is asserted (`Reach2.arb_persists`), `bra`
if it was given (`Reach2.bra_persists`), and there are at least two terms
(`Reach2.two_terms`, `reach2_givenA_two_terms`, `reach2_givenB_two_terms`).
The persistence of the terms, assertions and names themselves is new (from
D5; the second seed kept only images); the four statements about `a`, `b`,
`arb`, `bra` and the two terms are 2:D6, embedding. The numbers of terms and
of assertions never decrease
(`Reach2.card_T_le`, `Reach2.card_A_le`; new: the second seed's N8 refuted
this). Every result is legal, well formed and has at least one term:
`Step2.legal`, `Step2.wf`, `Step2.nonempty`, `Reach2.legal`, `Reach2.wf`,
`Reach2.nonempty` (1:D6 and 2:D6, embedding); sequences compose
(`Reach2.trans`).
Under FREE the names are dropped at the end and what survives is: some `xry`
asserted; with `bra` given, some pair asserted both ways; at least two terms.
Computed: `evidence/third/follows_*.csv` — `arb_asserted`, `names_apart`,
`something_asserted`, `at_least_two_terms`, `at_least_one_term`, `no_xrx` hold
in every result within the bound in both ANCHORED runs, `bra_asserted` in the
run with `bra`; the last four without names in both FREE runs
(`statements_holding_in_every_result`; K6, 2:K6 computed again). What is added to
what is given is never negative (`additions_never_negative` true in all four
runs), and on every one of the 97 633 + 89 432 + 5 923 + 2 689
unobstructed changes within the bounds neither count fell and the size rose by
exactly one (`counts_lowered_by` empty; R12).

**D7. No obstruction is ever cleared.** What is asserted stays asserted
(`Reach2.obstruction_persists`: if `urv` is asserted then `urv` itself, not
only its image, is asserted after any sequence of changes — 2:D7 re-proved in
a stronger form). For the one obstructed kind of change, adding `xrx`: it is
obstructed after every sequence of changes (D4), no state reached from a legal
state asserts any `xrx` (`no_change_asserts_xrx`), and the would-be outcome of
the obstructed attempt is itself unreachable (`xrx_outcome_unreachable`). No
change of this seed has the outcome of a removal (`Step2.ne_remove`, through
`Step3.ne_remove`) or of an identification of a term that is there
(`Step2.ne_identify`); conversely every change of the second seed is an
identification or a change of this one (`Step3.identify_or_step2`). Hence
"remove the obstruction" is realised by no sequence of changes for any
obstructed change (R3).

**D8. Every sequence has the same length: the size difference.** Let what is
given have size `2 + m0` (`m0 = 1` without `bra`, `2` with). Every sequence of
changes from what is given to a result `G` has exactly

    terms(G) + assertions(G) − (2 + m0)

changes, and there is one.
*Each change raises the size by exactly one* (`Step2.size_eq`; 2:D8 had "at
most one" because an identification lowered it), so a sequence of `n` changes
raises it by `n` (`Reach2.size_eq`) and any two sequences between the same two
states have the same length (`Reach2.length_unique`). In particular reaching
`G` from what is given takes exactly the size difference
(`fewest_changes2_lower_A`, `fewest_changes2_lower_B`: equalities, where the
second derivation's were inequalities). The earlier lower bounds hold by
embedding and are implied (`Reach2.size_le_inherited`,
`Reach2.costA_le_inherited`, `Reach2.costB_le_inherited`; 1:D8, 2:D8); on a
result the first derivation's "destroyed givens" are zero
(`lostA_eq_zero_of_reach2`, `lostB_eq_zero_of_reach2`,
`costA_eq_size_of_reach2`, `costB_eq_size_of_reach2`; 2:D8, embedding).
*A sequence exists.* Add the missing terms, then the missing assertions:
`reach2_by_additions`, with the count `additions_count` (2:D8, no change: a
statement about finite sets; the path is re-proved as changes of this seed —
the second derivation's path was additions only, so it is literally a sequence
of this seed). Both together, for states written with `a = 0`, `b = 1`:
`fewest_changes2_A`, `fewest_changes2_B`; for every writing, by D11:
`fewest_changes2_every_writing_A`, `fewest_changes2_every_writing_B` — from
some writing of what is given `G` is reached in the size difference, and from
every writing every sequence has that length.
*Under FREE* the names may be placed anywhere; a placement exists exactly when
`G` has some assertion (without `bra`) or some pair asserted both ways (with
`bra`), and every placement gives the same size difference (2:D8, no change:
the closed form in `code/second/cost.py` mentions no change and is reused,
`code/third/cost.py`). Computed: closed form equals best placement on all 476
legal states with at most 4 terms (`free_cost_closed_form_mismatches` empty);
the round of first appearance equals the formula for every explored result in
all four runs and both census runs
(`round_equals_cost_formula_for_every_result`); and on every unobstructed
change within the bound the outcome's round is the state's plus one
(`round_not_raised_by_one` empty), so within the bound every sequence to a
result has the length of its round — the computed form of
`Reach2.length_unique`. Consequence for the protocol: the order in which
changes are attempted cannot move a result to another round (C6).

**D9. The results are the legal states containing what is given.** With
names: a state is reached from some writing of what is given exactly when it
is legal, well formed, `a` and `b` are two terms, and `arb` is asserted (and
`bra`, if given). Lean: `result2_iff_A`, `result2_iff_B`;
`reach2_givenA_contains`, `reach2_givenB_contains` for the concrete writing
(2:D9, embedding for necessity; sufficiency re-proved by D8's path after
rewriting, D11). Under FREE: the legal states with at least one assertion
(without `bra`), or with a pair asserted both ways (with `bra`). This is the
second seed's set of results, and the rounds are the same (D8). Computed: in
all four runs and both census runs the explored results equal, by number of
terms and assertions, the legal states with those properties counted up to
sameness by an independent method (`explored_equals_independent_count`;
`code/second/orbits.py`, 2:K1, no change: it counts states); and the third
exploration equals the second derivation's exploration with identifications
left out — the same results in the same rounds, the same attempts and the
same obstructed attempts in every round — in all four runs and both census
runs (`same_results_rounds_and_attempts_as_second_derivation_without_identifications`;
2:D10's computed check, computed again as this seed's whole exploration).

**D10. Answers reach nothing new.** A refusal changes nothing; a build is two
additions (`build_answer2`, `build_answer2_reverse`; reading the added term as
`x` gives the would-be outcome, and no build does with less:
`build_gives_back`, `build_reverse_gives_back`,
`build_needs_term_and_assertion`, 1:D11, no change); "remove the obstruction"
is impossible (D7). So every answer is a sequence of unobstructed changes and
the results are those of unobstructed changes alone, under any reading of G9
whose further changes are changes of the two kinds. Computed: for all
48 952, 45 863, 4 324 and 2 162 obstructed attempts within the
bounds every answer within the bound reaches an explored result no later than
the state's round plus the answer's changes (`answers_reaching_something_new`
empty; answers beyond the bound belong to the frontier and are not checked);
no recorded answer removes an obstruction (`answers_removing_the_obstruction:
0`).

**D11. Changes commute with rewriting.** For a one-to-one rewriting `π` of the
terms, every change becomes a change of the same kind on the rewritten state
and every sequence a sequence of the same length: `Step2.rename`,
`Reach2.rename` (2:D11, re-proved for the two kinds; the lemmas about
`rename` on states — `size_rename`, `legal_rename`, `wf_rename`,
`exists_perm_of_ne`, `rename_symm_apply`, and the membership lemmas — mention
no change and are cited). It carries D8 and D9 from the writing `a = 0`,
`b = 1` to every writing.

**D12. Reachability between results is containment.** A result `t` is
reachable from a result `s` exactly when `s` is contained in `t` — names in
place, every term of `s` a term of `t`, every assertion of `s` asserted in `t`
(`reach2_iff`; *only if* D5, *if* `reach2_of_contains`, which is D8's path).
Up to sameness: exactly when some writing of `s` is contained in `t`
(`reach2_iff_some_writing`), that is, when the terms of `s` map one-to-one
into those of `t` carrying assertions to assertions and, with names, the names
to the names — an embedding. Both directions are in Lean; the second
derivation's criterion (2:D12, a carrying map) had its "if" direction open in
Lean where the map merged terms (2:O3), and here no map merges. Every
embedding is a carrying map, so whatever this seed reaches the second reached
(computed: `pairs_reachable_here_but_not_under_second_seed: 0` in all four
runs), and not conversely (§6). Computed: for every ordered pair of results
within 3 terms the embedding test (`code/third/reach.py`, backtracking) agrees
with a breadth-first search along the changes within the same bound — 289,
100, 1 156 and 289 pairs in the four runs, no disagreement
(`embedding_agrees_with_search`; `evidence/third/reach_bound3_*.csv`).

**D13. Reachability is one-way; a number that never decreases.** If `t` is
reached from `s` and `s` from `t`, both sequences have length zero and `s`
is `t` (`Reach2.antisymm`, from D8's size equation); a state once left is
never returned to (`Reach2.no_return`); the same up to rewriting
(`reach2_antisymm_writing`). So the only result that reaches what is given is
what is given (computed: `results_that_reach_what_is_given: 1` in all four
runs, column `reaches_what_is_given` of `results_*.csv`), and no two different
results reach each other (`unordered_pairs_reachable_both_ways: 0` in all four
runs). The fewest classes of a split of the terms with no two related terms in
a class never decreases along a change (`Reach2.split_mono`; 2:D13,
embedding); computed on every unobstructed change within the bound
(`fewest_classes_lowered_by` empty; column `fewest_classes`).

**D14. Completeness within the bound.** Let `N` be the bound on terms. (i)
The results within the bound are exactly the legal states with at most `N`
terms that contain what is given: each explored state is one by construction;
conversely D8's path is additions only and never has more terms than its
target, and the exploration applies every change to every result and drops
only outcomes with more than `N` terms, so by induction along that path every
such state is found (2:D14, re-proved with `reach2_by_additions`; the same
argument). Certificate: the independent count (D9). (ii) The round of first
appearance within the bound is the fewest changes without bound — here the
length of every sequence (D8). (iii) The frontier is exact: only adding a term
raises the number of terms, so the attempts that leave the bound are, for each
result with `N` terms, "add a term" and its `N` obstructed `xrx`, each with two
builds: `1 + N` attempts and `1 + 2N` entries per such result (computed true
in all four runs; `evidence/third/frontier_*.csv`). Rounds `0 … N − 2` within
the bound agree with the counts without bound (a result of round `k` has at
most `k + 2` terms): `rounds_agreeing_with_unbounded_formula` all true. (iv)
Sequences: a sequence reaching a result never has more terms than the result
(D5), so for every result within the bound the number of sequences reaching
it, and their common length, are exact, not bounded (K7).

**D15. With `bra` given, passing on holds in no result.** `bra` persists
(D6), and `arb`, `bra`, passing on would give `ara`: `passing_on_refutes_bra`
(1:R7, no change; 2:D15). Likewise "never both `xry` and `yrx`" holds in no
result of that beginning. Computed: `follows_anchored_with_bra.csv` and
`follows_free_with_bra.csv`, `passes_on` and `both_ways_never` with no
`first_holds`.

**D16. Two sequences to one result.** From what is given without `bra`, the
result `a b c; arb bra` is reached by adding the term first and by adding
`bra` first: two different sequences, of the same length (`two_sequences`,
with `Reach2.length_unique`). So the sequence reaching a result is not unique
(N9), though its length is (D8).

## 5. What does not follow

Each item has two legal witnesses among the results, or a proof.

**N1. `bra`. N2. Not `bra`.** Both beginnings are legal and contain what is
given. Lean: `bra_not_refuted`, `bra_not_derived` (1:N1, 1:N2, no change).

**N3. Anything on which the two beginnings differ, from the beginning
without `bra`.** "Never both `xry` and `yrx`": holds in what is given, fails
after adding `bra` (round 1). "Whenever `xry` and `yrz` then `xrz`": holds
(vacuously), fails after adding `bra`. "Every term is first in some
assertion": fails in what is given, holds after adding `bra`. "Whenever `xry`
then `yrx`": fails, then holds. (`follows_anchored_without_bra.csv`,
`follows_free_without_bra.csv`; 2:N3, computed again.) From the beginning with
`bra` the first two statements are refuted in every result (D15) and the last
two are independent.

**N4. That there are exactly two terms.** Holds in what is given, fails after
one change (add a term) (2:N4, computed again).

**N5. Anything about the asserting that is not true of every legal state
containing what is given.** By D9 every such state is a result, so a
statement that holds in one of them and fails in another does not follow. Of
the fourteen statements tested, those holding in every result within the bound
are exactly "no `xrx`", "at least one term", "at least two terms", "something
is asserted", and with names "`arb` is asserted", "`a` and `b` are two terms",
plus "`bra` is asserted" when `bra` is given; each is proved for all results
(D6). Every other statement has a result where it holds and one where it
fails, except the two of D15 under the beginning with `bra` (2:N5, no
change; the witnesses computed again, K6).

**N6. Which answer an obstructed change gets.** Refusal is always possible;
removal never, or is refusal (R3, C7); a build always (adding a term is never
obstructed, D3). No result needs a build, and no result needs an obstructed
change to be attempted at all (D10). "Must be answered" does not determine
the answer.

**N7. Growth.** Nothing forces terms to be added: what is given adds no term,
and one change gives a result that adds one (§6). That every result is finite
is derived (D6); whether terms can be added without end is not given (C3).

**N8. That any two results are comparable — that one reaches the other.**
The two results of round 1 without `bra`, `a b c; arb` and `a b; arb bra`,
reach neither each other (neither contains the other; `reach_bound3_*.csv`),
while what is given reaches both. Reachability is one-way (D13) but not total.

**N9. That a result is reached by one sequence only, or that results of one
round are reached by equally many.** What is given is reached by one sequence
(the empty one) and `a b c; arb bra` by two (D16); `a b c; arb arc`, in the
same round as the latter, by one (the term must come before `arc`). Column
`sequences_of_changes` of `results_*.csv`; 8 of 1 090 results
(ANCHORED, without `bra`) are reached by one sequence only, and the numbers
of sequences over all results within the bound add up to 201 509 831 (K7).

**N10. That the number of attempts on a result is the same for results of one
round.** It is `1 + n² − m` (D3), which differs between `a b c; arb` (9) and
`a b; arb bra` (3), both of round 1.

**Refuted** (each a proved impossibility): `a` and `b` one term to begin with
(R1, D1); an answer that makes adding `xrx` performable (R2, D4); removing the
obstruction of any obstructed change, and any change with the outcome of a
removal or of an identification (R3, D7); a result with fewer than two terms,
in particular the one-term state (R4, D6, `oneTerm_unreachable2_A`,
`oneTerm_unreachable2_B`); identifying `a` and `b`, or un-asserting `arb`,
ever (R5, D6); an answer that reaches a result additions do not reach (R6,
D10); `bra` together with passing on, and, with `bra` given, passing on in any
result (R7, D15); the beginning with `bra` reaching the beginning without (R8,
D2); a result that does not contain what is given (R9, D9); a sequence of
changes to a result whose length is not the size difference — fewer or more
(R10, D8); a change that lowers the fewest classes (R11, D13); a change that
lowers the number of terms or of assertions, or that leaves the size where it
was or raises it by more than one (R12, D6, D8); a result returned to after
being left, and any result other than what is given that reaches what is given
(R13, D13); two different results reachable from each other (R14, D13).

## 6. The exploration

**Protocol.** From each beginning, under each reading of sameness (four
runs): round by round, every change on every result first reached in the round
before (C6), each result's changes in the seed's order of kinds (adding a
term, then adding an assertion; both add one). Refusal and every build are
kept as alternatives; "remove the obstruction" is recorded as impossible on
every obstructed attempt. For every attempt within the bound of 3 terms the
change, the obstruction and every answer are recorded:
`evidence/third/attempts_bound3_*.jsonl` (109, 58, 215 and
99 attempts). Within the declared bounds attempts are counted and their
answers checked (D10), not recorded one by one. Attempts on what is given:
`evidence/third/given.json`.

**The four attempts on what is given, without `bra`** (names kept):

| change | adds | obstruction | outcome or answers |
|---|---|---|---|
| add a term | 1, 0 | — | `a b c`; `arb` (1, 0) |
| add `ara` | 0, 1 | `ara` | refused · remove the obstruction: impossible · build: add `c`, add `arc` (1, 1); or add `c`, add `cra` (1, 1) |
| add `bra` | 0, 1 | — | the other beginning (0, 1) |
| add `brb` | 0, 1 | `brb` | refused · impossible · build: add `c`, add `brc`; or add `c`, add `crb` |

With `bra` the list is: add a term, add `ara`, add `brb` (both obstructed):
three attempts. The second derivation had five and four (one identification
more), the first six and five.

**Results by what they add to what is given** (ANCHORED, without `bra`, bound
4; `evidence/third/added_*.csv`; K5). The table is the second derivation's
(2:K5, computed again: the same results in the same rounds, D9). No number is
negative, and every group appears in one round only, the round being terms
added plus assertions added (D8).

| terms added | assertions added | results | round |
|---|---|---|---|
| 0 | 0 | 1 | 0 |
| 0 | 1 | 1 | 1 |
| 1 | 0 | 1 | 1 |
| 1 | 1 | 5 | 2 |
| 2 | 0 | 1 | 2 |
| 1 | 2 | 10 | 3 |
| 2 | 1 | 6 | 3 |
| 1 | 3 | 10 | 4 |
| 2 | 2 | 30 | 4 |
| 1 | 4 | 5 | 5 |
| 2 | 3 | 85 | 5 |
| 1 | 5 | 1 | 6 |
| 2 | 4 | 170 | 6 |
| 2 | 5 … 11 | 236, 236, 170, 85, 30, 6, 1 | 7 … 13 |

**Rounds.** New results per round within the bound, and without any bound
(the latter from D8 and D9 by counting states up to sameness, exact, to round
20; `evidence/third/rounds_*.csv`; K2, K3). The numbers are the second
derivation's (2:K2, 2:K3, computed again); the column
`new_results_second_derivation_without_identifications` of each file repeats
the second derivation's run beside this one, and the two are equal in every
round.

| round | FREE, no `bra`: bound 5 / no bound | FREE, `bra`: bound 5 / no bound | ANCHORED, no `bra`: bound 4 / no bound | ANCHORED, `bra`: bound 4 / no bound |
|---|---|---|---|---|
| 0 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| 1 | 2 / 2 | 1 / 1 | 2 / 2 | 1 / 1 |
| 2 | 5 / 5 | 3 / 3 | 6 / 6 | 5 / 5 |
| 3 | 10 / 10 | 8 / 8 | 16 / 17 | 11 / 12 |
| 4 | 22 / 23 | 19 / 20 | 40 / 47 | 29 / 35 |
| 5 | 44 / 50 | 49 / 53 | 90 / 134 | 61 / 99 |
| 6 | 100 / 123 | 120 / 145 | 171 / 402 | 110 / 303 |
| 10 | 1 168 / 6 511 | 1 445 / 11 984 | 85 / 40 203 | 25 / 30 936 |
| 20 | 5 / 2 007 940 773 | 1 / 6 422 479 070 | 0 / 27 270 015 509 | 0 / 22 096 992 409 |
| last round with a new result within the bound | 22 | 21 | 13 | 12 |
| rounds after that, to 100 | none new | none new | none new | none new |

The census at bound 5 (ANCHORED) has its last new result in round 22 (without
`bra`) and 21 (with). No change was invented: after the last round with a new
result, every attempt on every known result repeats a known result or leaves
the bound. Without a bound every round has a new result (what is given plus
`k` new terms is reached in round `k` and in no other), so 100 rounds cannot
be listed; the set of results of round `k` is determined for every `k` by D8
and D9 — membership is a formula — and only its size beyond round 20 is left
open (O2).

**Totals** (K1, K2, K4). Results within the bound: 9 841 (FREE, no `bra`: 2, 15, 217,
9 607 by number of terms), 9 212 (FREE, `bra`: 1, 9, 176, 9 026), 1 090
(ANCHORED, no `bra`: 2, 32, 1 056), 545 (ANCHORED, `bra`: 1, 16, 528); census
at 5 terms: 90 562 and 45 281 — the second derivation's totals. Changes
attempted: 156 192, 144 321, 11 303, 5 379 (census 1 398 119 and
676 419), of which obstructed 48 952, 45 863, 4 324, 2 162
(census 451 684, 225 842); the second derivation attempted 253 611,
235 665, 17 737, 8 596 (census 2 299 273, 1 126 996), the difference being
its identifications. Each total is the sum over the results of `1 + n² − m`,
and each obstructed total the sum of `n` (D3; checked in every run).

**Frontier** (K4). Every result with `N` terms, each with `1 + N` attempts leaving
the bound and `1 + 2N` frontier entries: 9 607 results, 57 642 attempts,
105 677 entries (FREE, no `bra`); 9 026, 54 156, 99 286 (FREE, `bra`); 1 056,
5 280, 9 504 and 528, 2 640, 4 752 (ANCHORED) — the second derivation's
frontier, since the attempts that leave the bound are additions there too.
The census counts 89 472 and 44 736 frontier results (984 192 and 492 096
entries) and does not export them. `evidence/third/frontier_*.csv`,
`summary.json`.

**Reachability within 3 terms** (K8). For every ordered pair of results
`reach_bound3_*.csv` lists whether the second is reachable from the first, the
embedding if so, and whether the second seed reached it (2:D12's carrying
map). Of the 1 156 ordered pairs (ANCHORED, without `bra`) 294 are
reachable here and 439 were under the second seed, 145 under the
second only; with `bra`, 98 of 289 here, 161 there; FREE:
117 of 289 here and 153 there, 46 of 100 here and
62 there. No pair is reachable here and not there, and no two different
results are reachable both ways here, where the second seed had 34, 28, 16 and
10 such pairs. Every result reaches itself; no other result reaches what is
given.

**Sequences** (K7). For every result within the bound `results_*.csv` gives the
number of sequences of changes reaching it (exact, D14 (iv)): a sequence is a
chain of attempted changes, each taken from the list of changes of the result
it is applied to (C6), and two changes of that list that differ count as two
even when their outcomes are the same result. Every sequence has the length
of the result's round (D8). Over all results within the bound
the numbers add up to 1 010 367 312 842 021 002, 45 925 786 953 001 262, 201 509 831, 15 500 787; 7,
4, 8, 7 results are reached by one sequence only. At
one and the same bound the FREE and ANCHORED totals agree for each beginning
(393 and 66 at bound 3, `tests/test_third_explore.py`), since a sequence is
counted by its changes, which are the same however the states along it are
written; the exported runs use different bounds, so their totals differ.

**Reproducibility** (K9, K10). `python code/generate_third.py` rewrites every computed
file of `evidence/third/`; `MANIFEST.sha256` lists their hashes;
`python code/generate_third.py --check` regenerates into a temporary folder
and compares every computed file, in both directions (it matched).
`python code/lean_report_third.py` rebuilds all three Lean libraries and
rewrites `evidence/third/lean_axioms.txt`, refusing if the build warns of
`sorry` or a cited theorem depends on an axiom other than `propext`,
`Classical.choice`, `Quot.sound`. The first and second derivations'
`--check` and Lean reports were re-run after this work and their evidence
regenerates unchanged. Tests: 264 passed, three derivations; line coverage
100.00 %, branch coverage 99.13 % of all of `code/` (`python
code/xry/gate.py coverage.json`); `mypy --strict` clean; the prose watchlist
clean, with every pinned hit of this paper in §9.

## 7. Alternatives: kept, or eliminated by proof

| Alternative | Status |
|---|---|
| `bra` asserted / not asserted to begin with | both kept (N1, N2); all runs done for both |
| FREE / ANCHORED sameness | both kept (C4); all runs done for both |
| `a`, `b` one term to begin with | eliminated (D1) |
| a third legal beginning on the given terms | eliminated (D2) |
| more terms or assertions to begin with | kept as results of the chosen beginning (D9) |
| refuse / build for each obstructed change | both kept in the records; as results they coincide with additions (D10) |
| "remove the obstruction" as un-asserting | eliminated (R3, D7); recorded as impossible on every obstructed attempt |
| "remove the obstruction" as withdrawing the change | kept as a reading; coincides with refusal (C7) |
| the order of the two kinds within a result | kept as a convention; cannot change any round (D8) |
| builds with more than one added term or assertion | kept as results (D9); not listed as answers beyond the fewest (C7) |
| every legal state containing what is given, within the bound | kept; none dropped (D14) |
| counting an answered change as one | not computed; same results (D10), rounds differ (C6) |
| assertions with multiplicity | neither computed nor eliminated: open (O1) |

**Results of the earlier derivations that do not hold under this seed** (each
with the claim that replaces it). From the second derivation: 2:D5's carrying
map may merge terms (here it is the identity, D5); 2:D8's "at most one per
change" and "fewest" (exactly one, every sequence, D8); 2:D12's reachability
by any carrying map (by an embedding, D12); 2:N8 "counts can decrease" (they
cannot, D6, R12); 2:N9 "a result can be left and returned to; some results
return to what is given" (never, D13, R13); 2:N10 "reachability is not
antisymmetric" (it is, D13, R14); 2:D3's obstructed identifications (no
object, D3); 2:C7's third reading of removal (no object). From the first:
exactly those the second derivation already listed in 2:§7 (1:D2, 1:D5,
1:D7–1:D10, 1:N4–N6, 1:R4, 1:R5), for the same reasons. Everything else cited
stands with the re-check given at its citation.

## 8. Open

- O1. Assertions with multiplicity (C1 unchosen).
- O2. The number of results of rounds 21–100 (finite and determined by D8,
  D9; the second derivation's O2, unchanged, since the sets are the same).
- O3. Results beyond the declared bounds, listed (the frontier says where to
  continue; the census gives the counts at 5 terms with names).
- O4. Readings of "build structure" other than C7: by D10 they cannot change
  the results; they could change which records count as answers.
- O5. A closed form for the number of sequences reaching a result (computed
  per result within the bound, K7; no formula sought).

Closed, relative to the second derivation: 2:O3 (the "if" direction of the
reachability criterion in Lean) — here both directions are in Lean
(`reach2_iff`, `reach2_iff_some_writing`), because no map merges terms. The
earlier derivations' files are not changed by this, so their ledgers keep
their own items.

## 9. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **The subgraph order, and embeddings of directed graphs.** A state is a
  loopless digraph with two marked vertices; containment (D5) is the subgraph
  relation with the marks fixed, and an embedding (D12) is an injective
  homomorphism. D12 says the process reaches `t` from `s` exactly when `s` is
  isomorphic to a subgraph of `t` with the marks in place: reachability is the
  subgraph order on marked loopless digraphs, a partial order on isomorphism
  classes (D13 is its antisymmetry). Striking identifications from the second
  seed restricts its homomorphism preorder (2:§9) to injective homomorphisms,
  which is why the preorder's cycles (homomorphic equivalence, cores) vanish
  and only the identity classes remain; the pairs the second seed reached and
  the third does not (§6) are exactly the non-injective homomorphisms.
- **Graded posets; the subgraph poset is graded by size.** D8 says every
  maximal chain from what is given to a result has the same length, the
  difference in vertices plus arcs: the subgraph order restricted above a
  fixed element is a graded poset with rank function `|V| + |A|`, and the
  rounds of the exploration are its rank levels. The number of sequences to a
  result (K7) is the number of maximal chains from the bottom, equivalently
  the number of linear extensions of the poset of missing pieces ordered by
  "an arc after both its endpoints"; counting linear extensions is #P-complete
  in general (Brightwell and Winkler), which is why no closed form was sought
  (O5).
- **Insertion-only edit distance.** When only insertions are allowed, every
  edit script between two structures has the same length, the size
  difference; D8 is that remark, now with nothing left that could shorten or
  lengthen a script (the second seed's identifications could not shorten one,
  2:D10, but could lengthen one).
- **Extensions of a fixed structure; enumeration.** The results (D9) are the
  loopless digraphs into which the given arc embeds with its endpoints marked,
  the same set as under the second seed, with the same Pólya counts (2:K1);
  nothing is new in the counting.
- **Irreflexive plus transitive gives asymmetric** (strict partial orders):
  `passing_on_refutes_bra`, as before (D15).
- **Independence by two models**: N1, N2, as before.

What appears to be specific to this seed: that of the seed's two named
answers to an obstruction one is realisable for no obstructed change and the
other collapses into refusal (R3, C7); that the number of changes to a result
is not merely least but the same along every sequence (D8), so the seed's
"fewest additions first" and "earlier changes before later ones" cannot affect
any result's round; that the given is never diminished and never returned to
(D6, D13); and that the reachability criterion is now proved in both
directions in Lean, closing the second derivation's open item for this seed.
