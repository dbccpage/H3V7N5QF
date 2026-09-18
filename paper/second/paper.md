# What follows from `arb`, no `xrx`, and three kinds of change

Second derivation. Input: `prompt/second/seed_prompt.md`. Task:
`prompt/second/prompt.md`. Claim IDs refer to `paper/second/claim_ledger.md`;
an ID written `1:D8` refers to the first derivation's ledger,
`paper/claim_ledger.md`, and its paper `paper/paper.md`. Lean names in the
namespace `Seed.Second` are in `lean4/Second/`; names in the namespace `Seed`
are the first derivation's, in `lean4/H3V7N5QF/`. The axiom report for every
theorem cited here, of either library, is `evidence/second/lean_axioms.txt`.
Computed files are in `evidence/second/`, written by
`python code/generate_second.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; the unchosen
readings are listed), **derived** (proved), **computed** (output of `code/`),
**refuted** (proved impossible), **open**.

Where a result of the first derivation is used it is cited and re-checked
from the second seed. The re-check is one of three kinds. *(no change)*: the
statement mentions no change of state, only relations, states, or one of the
state operations `addTerm`, `addAssertion`, `identify`, all of which the second
seed shares, so the statement and its proof stand as they are. *(embedding)*:
the statement is about the first seed's changes `Step` or sequences `Reach`;
every change of the second seed is a change of the first
(`Step3.toStep`, `Reach3.toReach`), so the statement restricts to the second
seed, and the restriction is itself a Lean theorem. *(re-proved)*: the first
proof used a removal and has been replaced. Results of the first derivation
that fail under the second seed are listed in §7.

## 0. Findings in brief

1. The second seed is the first with one kind of change struck out: removing
   an assertion. Every other sentence is the same (given, §1).
2. `a` and `b` are two terms; there are exactly two beginnings, with and
   without `bra`; the one without reaches the one with in one change, and the
   one with never reaches the one without (D1, D2, R8).
3. Nothing is ever un-asserted. Every sequence of changes comes with a map of
   terms that carries each asserted `xry` to an asserted `q(x) r q(y)` and the
   names to the names (D5). Hence what is given survives in every result:
   `arb` stays asserted, `bra` too if it was given, `a` and `b` stay two terms,
   every result has at least two terms and asserts something (D6). Three of
   the four "does not follow" items of the first derivation's N4 now follow.
4. Exactly the same two kinds of change can be obstructed as before (D3, D4),
   and no obstruction is ever cleared (D7). "Remove the obstruction" names an
   answer that no sequence of changes realises (R3); an obstructed change is
   refused or built around (N6).
5. The results are exactly the legal states that contain what is given, names
   in place (D9); without names, the legal states with some assertion (or,
   with `bra` given, with some pair asserted both ways). The first
   derivation's "everything legal is a result" is refuted (R9); the one-term
   state is unreachable (R4).
6. The fewest changes to a result is its size minus the size of what is given
   (terms plus assertions), and additions alone reach it in that many; an
   identification never reaches anything new (D8, D10). The first derivation's
   term "two for each destroyed given" is always zero on a result.
7. Reachability between results is the existence of a carrying map (D12). It
   has cycles: what is given is left and returned to in two changes (N9), 14
   of the 1 090 results within the bound return to it; but it is not
   symmetric, and the fewest classes of a split of the terms never decreases
   (D13).
8. 100 rounds cannot be listed: every round has a new result. Declared bounds:
   5 terms (any rewriting), 4 terms (names kept; a counts-only census at 5).
   Within the bound the exploration is complete, certified by an independent
   count; the frontier is exported exactly (D14). The rewriting step that the
   first derivation left open in Lean (1:O3) is proved in Lean for this seed
   (D11).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2 | An assertion is written `xry`, where `x` and `y` are terms. |
| G3 | `arb` is asserted. |
| G4 | For no term `x` may `xrx` be asserted. |
| G5 | Whether `bra` is asserted is not given. |
| G6′ | A change is exactly one of: identifying two terms; adding a term; adding an assertion. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G8 | A change that makes some `xrx` asserted is obstructed. |
| G9 | An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which; record the change, the obstruction, the answer. |
| G10 | A refused change is recorded and changes nothing. |
| G11 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, prove what is complete within it. |
| G14 | Any outcome is valid. |

G6′ is the only sentence that differs from the first seed (`diff` of the two
files; `research/second/reading_the_seed.md`). G1–G5 and G7–G14 are the first
derivation's G1–G5, G7–G14 word for word.

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
| change, three kinds | given (G6′, G7) | |
| non-changes; a new term has no assertion; an added assertion is between terms there | chosen (C5) | |
| obstructed change | given (G8) | characterised: derived (D3) |
| the obstruction of a change | chosen (C7) | the assertions that would become `xrx` |
| refuse / remove the obstruction / build structure | given (G9, G10) | content: chosen (C7); removal never realisable: refuted (R3); results independent of the choice: derived (D10) |
| carrying map of a sequence of changes | derived (D5) | new to this seed |
| result | chosen (C6) | a legal state up to sameness |
| the results, as a set | derived (D9) | legal states containing what is given |
| sameness | given (G12) | two readings, both kept: chosen (C4) |
| terms and assertions added to what is given | given (G11) | counted against `a`, `b`, `arb` for both beginnings, as in 1:§2; never negative under this seed (D6, R10) |
| round; what counts as one change | chosen (C6) | |
| bound, frontier | given (G13) | bound on terms: chosen (C8) |
| size, cost | derived (D8) | size = terms + assertions |
| reachability between results | derived (D12) | the carrying-map criterion |
| fewest classes of a split | derived (D13) | never decreases |
| counts of results | computed (K-claims) | |

## 3. Readings that had to be chosen

The readings C1–C4, C6, C9 are the first derivation's, unchanged in wording;
they are restated only where the second seed changes what they imply.

**C1. Asserted is yes or no.** As 1:C1. Unchosen: multiplicity (O1).

**C2. To begin with there are exactly the terms `a` and `b`.** As 1:C2.
Unchosen: further terms or assertions to begin with. Every such beginning is a
legal state containing `arb`; by D9 it is a result of the chosen beginning,
reached by additions alone, and its own results (the legal states containing
it) are among the chosen beginning's results. So the unchosen reading moves the
starting point and adds no result.

**C3. No cap on the number of terms.** As 1:C3. Every sequence used in the
proofs of D8, D9, D10 is a sequence of additions that never has more terms
than its target, so a cap `L ≥ 2` leaves every statement about results with at
most `L` terms and their fewest changes unchanged. Builds need one term more
than the state (D10); nothing is claimed for them under a cap.

**C4. Sameness, two readings, both kept.** FREE and ANCHORED as 1:C4. All
computations are done under both.

**C5. Non-changes.** Adding what is asserted and identifying a term with
itself change nothing, so by G6′ they are not changes; a new term comes with no
assertion; an added assertion is between terms already there. This is 1:C5
without its clause about removing what is not asserted, which has no object
under this seed.

**C6. Results and rounds.** As 1:C6: a result is a legal state up to
sameness; round `k` attempts every change on every result first reached in
round `k − 1`, each result's changes fewest additions first (identifications,
then adding a term, then adding an assertion); a performed change counts one;
a refused change is an attempt of its round that changes nothing; the further
changes of an answer count one each. Unchosen: an obstructed change and its
answer count as one. By D10 the results are the same under both.

**C7. Obstruction and answers.** The obstruction of a change is the set of
assertions that would become some `xrx` (as 1:C7). *Refuse*: recorded, nothing
changes. *Remove the obstruction*: un-assert those assertions, then perform the
change — under this seed no change un-asserts anything, so this answer is
recorded as impossible for every obstructed change (R3, D7); every obstructed
attempt in `evidence/second/` carries the record
`"remove the obstruction": "impossible: no change un-asserts an assertion"`.
*Build structure*: by additions only, reach a legal state from which
identifying the added terms back gives exactly the would-be outcome of the
obstructed change, fewest additions first; for an obstructed identification the
state itself (no addition); for adding `xrx`, add a term `t` and `xrt` or
`trx` (D10). Unchosen readings of "remove the obstruction" under this seed:
(i) withdrawing the change — then it coincides with refusal and adds no
result; (ii) moving the obstruction by identifying one of the two terms with a
third — refuted, the obstruction persists between the images (D7). Under any
reading in which the further changes are changes of the three kinds, the
results are the same set (D10). "Declare which" is read as in 1:C7: every
answer is recorded with its kind and all are kept; the seed does not fix one
(N6).

**C8. Bound.** At most 5 terms under FREE and 4 under ANCHORED for the
exported files (9 841 / 9 212 and 1 090 / 545 results, seconds each); under
ANCHORED a census at 5 terms (90 562 / 45 281 results, about a minute each)
records counts and the same checks but writes no per-result file and does not
export its frontier.

**C9.** `r` writes assertions, not terms.

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. `a` and `b` are two terms.** If they were one, `arb` would be `xrx`.
Lean: `given_distinct` (1:D1, no change).

**D2. Exactly two beginnings, one way between them.** On the terms `a`, `b`
alone a legal state containing `arb` asserts `arb` only or `arb` and `bra`,
and these differ: `two_states_on_given_terms`, `two_states_differ` (1:D2, no
change); computed, `evidence/second/given.json` (`count: 2`). The beginning
without `bra` reaches the one with it by adding `bra`: `givenA_to_givenB3`
(1:D2's `givenA_to_givenB`, re-proved as a change of this seed). The other
direction of 1:D2 was a removal; under this seed it is impossible:
`givenB_never_givenA` (R8; proof in D6).

**D3. Which changes are obstructed.** In a legal state: identifying `u` and
`v` is obstructed exactly when `urv` or `vru` is asserted; adding `xry` is
obstructed exactly when `x` and `y` are one term; adding a term is never
obstructed. Lean: `identify_legal_iff`, `addAssertion_legal_iff`,
`addTerm_legal` (1:D3, no change: each is about one state operation); the
first derivation's `remove_legal` has no object here. Computed on every change
of all 69 legal states written on at most 3 terms:
`tests/test_second_changes.py::test_obstructed_exactly_when_some_xrx_would_be_asserted`.

**D4. Adding `xrx` is obstructed in every state.** Lean:
`adding_xrx_always_obstructed` (1:D4, no change).

**D5. The carrying map.** Every change comes with a map of terms — the
identity for adding a term or an assertion, the replacement `merge u v` for an
identification — that carries every term to a term, every asserted `xry` to
an asserted `q(x) r q(y)`, and the names `a`, `b` to the names. Carrying maps
compose, so every sequence of changes has one. Lean: `Step3.carries`,
`Reach3.carries` (the structure `Carries`). This is the one fact of the second
seed from which D6, D7, D9, D12, D13 follow; it is false under the first seed,
where a removal carries nothing.

**D6. What is given survives.** In every result, names kept: `a` and `b` are
two terms (`Reach3.names_apart`: the carrying map sends `arb` to
`q(a) r q(b)`, which is asserted, so `q(a) ≠ q(b)` by legality); `arb` is
asserted (`Reach3.arb_persists`); `bra` is asserted if it was given
(`Reach3.bra_persists`); there are at least two terms (`Reach3.two_terms`,
`reach3_givenA_two_terms`, `reach3_givenB_two_terms`); something is asserted
(from `arb`). Every result is legal, well formed and has at least one term:
`Reach3.legal`, `Reach3.wf`, `Reach3.nonempty` (1:D6 `Step.legal`, `Step.wf`,
`Step.nonempty`, `Reach.legal`, `Reach.wf`, `Reach.nonempty`, embedding). Under
FREE the names are dropped at the end, and what survives is: some `xry`
asserted; with `bra` given, some `xry` and `yrx` both asserted; at least two
terms. Computed: `evidence/second/follows_*.csv` — `arb_asserted`,
`names_apart`, `something_asserted`, `at_least_two_terms`, `at_least_one_term`,
`no_xrx` hold in every result within the bound in both ANCHORED runs,
`bra_asserted` in the run with `bra`; the last four without names in both FREE
runs (`statements_holding_in_every_result` in `summary.json`). What is added to
what is given is therefore never negative under this seed (computed:
`additions_never_negative` true in all four runs; R10).

**D7. No obstruction is ever cleared.** If `urv` is asserted, then after any
sequence of changes the images `q(u)`, `q(v)` of `u`, `v` are still related
that way, so identifying them is still obstructed. Lean:
`Reach3.obstruction_persists`, `Reach3.identify_images_obstructed`. This is the
sequence version of 1:D5, which the first derivation proved for one change only
(`obstruction_persists`, embedding) and left open for sequences (1:O6); under
this seed the carrying map gives it at once, and the conclusion is stronger:
nothing clears an obstruction, where under the first seed a removal did. For
adding `xrx`, D4 applies. Hence "remove the obstruction" is realised by no
sequence of changes for any obstructed change (R3); concretely, no change of
this seed has the outcome of a removal (`Step3.ne_remove`; conversely every
change of the first seed is a removal or a change of this one,
`Step.remove_or_step3`), and the outcome of the first derivation's removal
answer to "identify `a` and `b`" is unreachable
(`removal_answer_outcome_unreachable`).

**D8. Fewest changes (cost).** Let what is given have size `2 + m0` (`m0 = 1`
without `bra`, `2` with). The fewest changes from what is given to a result
`G` is

    terms(G) + assertions(G) − (2 + m0).

*Lower bound.* Size rises by at most one per performed change: adding raises it
by one, an identification lowers it by at least one (`Step3.size_le`,
`Reach3.size_le`, `fewest_changes3_lower_A`, `fewest_changes3_lower_B`). The
first derivation's lower bound `size + 2·lost ≤ n + size(given)` also holds
here by embedding (`Reach3.costA_le_inherited`, `Reach3.costB_le_inherited`,
1:D8) and implies this one, since `lost ≥ 0`; on a result `lost` is in fact
zero (`lostA_eq_zero_of_reach3`, `lostB_eq_zero_of_reach3`,
`costA_eq_size_of_reach3`, `costB_eq_size_of_reach3`), so 1:D8's formula
collapses to the size difference, and every state on which it would be larger
is unreachable (R9).
*Upper bound.* Add the missing terms, then the missing assertions:
`reach3_by_additions`, `additions_count` (1:D8's `reach_by_edits` began with
removals; re-proved without them). Both bounds together, for states written
with `a = 0`, `b = 1`: `fewest_changes3_A`, `fewest_changes3_B`; for every
writing, by D11: `fewest_changes3_every_writing_A`,
`fewest_changes3_every_writing_B` — there is a writing of what is given from
which `G` is reached in exactly the size difference, and from no writing in
fewer.
*Under FREE* the names may be placed anywhere; a placement exists exactly when
`G` has some assertion (without `bra`) or some pair asserted both ways (with
`bra`), and every placement gives the same size difference. Computed: closed
form equals best placement on all 476 legal states with at most 4 terms
(`free_cost_closed_form_mismatches` empty), and the round of first appearance
equals the formula for every explored result in all four runs and in both
census runs (`round_equals_cost_formula_for_every_result`).

**D9. The results are the legal states containing what is given.** With
names: a state is reached from some writing of what is given exactly when it
is legal, well formed, `a` and `b` are two terms, and `arb` is asserted (and
`bra`, if given). Lean: `result_iff_A`, `result_iff_B`;
`reach3_givenA_contains`, `reach3_givenB_contains` for the concrete writing.
Necessity is D6; sufficiency is D8's upper bound after rewriting (D11). Under
FREE: the legal states with at least one assertion (without `bra`), or with a
pair asserted both ways (with `bra`) — place the names on such a pair. Computed:
in all four runs and both census runs the explored results equal, by number of
terms and assertions, the legal states with those properties counted up to
sameness by an independent method (`explored_equals_independent_count`,
`code/second/orbits.py` on top of `code/xry/orbits.py`, 1:K1 no change).

**D10. Answers and identifications reach nothing new.** A refusal changes
nothing; a build is two additions (`build_answer3`, `build_answer3_reverse`;
identifying the added term back gives the would-be outcome, and no build does
with less: `build_gives_back`, `build_reverse_gives_back`,
`build_needs_term_and_assertion`, 1:D11, no change); "remove the obstruction"
is impossible (D7). So every answer is a sequence of unobstructed changes, and
the results are those of unobstructed changes alone, under any reading of G9
whose further changes are changes of the three kinds. More: by D8's upper
bound every result is reached by additions alone, in the same round.
Computed: the exploration re-run with identifications left out reaches the
same results in the same rounds in all four runs
(`additions_alone_reach_the_same_results_in_the_same_rounds`); for all
121 777, 114 691, 9 414 and 4 707 obstructed attempts within the bounds every
answer within the bound reaches an explored result no later than the state's
round plus the answer's changes (`answers_reaching_something_new` empty;
answers beyond the bound belong to the frontier and are not checked); no
recorded answer removes an obstruction (`answers_removing_the_obstruction: 0`).

**D11. Changes commute with rewriting.** For a one-to-one rewriting `π` of
the terms, every change becomes a change of the same kind on the rewritten
state, every sequence a sequence of the same length, and the size is unchanged:
`Step3.rename`, `Reach3.rename`, `size_rename`. This is the step the first
derivation proved on paper and left open in Lean (1:O3); it is now in Lean for
the changes of this seed, and it carries D8 and D9 from the writing `a = 0`,
`b = 1` to every writing. The same lemma for the first seed would need one
more case (removal) and was not added, since the first derivation's files are
changed only for defects.

**D12. Reachability between results.** A result `t` is reachable from a
result `s` exactly when a carrying map from `s` to `t` exists. *Only if*: D5.
*If*: let `q` carry `s` to `t`. While `q` sends two terms `u ≠ v` of `s` to
one term, identify them: this is unobstructed, since `urv` or `vru` asserted
would make `q(u) r q(u)` asserted in `t`; the same `q` carries the outcome
(`merge u v x` is `x` or `u`, and `q(u) = q(v)`). Terms decrease, so this
ends with `q` one-to-one on the terms; rewrite each term `x` as `q(x)` (D11;
under ANCHORED the names go to the names); now the state is contained in `t`,
and additions finish (`reach3_by_additions`). The sequence never has more terms
than `s` or `t`. In Lean the two last steps are formal (`Reach3.rename`,
`reach3_by_additions`); the identifications along `q` are proved here only
(O3). Computed: for every ordered pair of results within 3 terms, the
carrying-map test (`code/second/reach.py`, backtracking) agrees with a
breadth-first search along the changes within the same bound — 1 156, 289,
289 and 100 pairs in the four runs, no disagreement
(`carrying_map_agrees_with_search`; `evidence/second/reach_bound3_*.csv`).

**D13. A number that never decreases.** Split the terms into classes so that
no class holds two related terms. The fewest classes of such a split never
decreases along a change: a split of the outcome pulls back along the carrying
map. Lean: `Reach3.split_mono` (every `k` that splits the outcome splits the
state). Adding a term keeps the number, adding an assertion or identifying can
raise it. Computed: on every unobstructed change within the bound (122 227,
111 948, 7 267, 3 361 changes) the number never fell
(`fewest_classes_lowered_by` empty; column `fewest_classes` in
`results_*.csv`). Consequence: a result whose terms need three classes (first
in round 3: `a b c; arb arc brc`) never reaches a result that needs two, so it
never returns to what is given.

**D14. Completeness within the bound.** Let `N` be the bound on terms. (i)
The results within the bound are exactly the legal states with at most `N`
terms that contain what is given: each explored state is one by construction;
conversely D8's path is additions only and never has more terms than its
target, and the exploration applies every change to every result and drops only
outcomes with more than `N` terms, so by induction along that path every such
state is found (1:D12, re-proved with the new path). Certificate: the
independent count (D9). (ii) The round of first appearance within the bound is
the fewest changes without bound (D8; both directions as in 1:D12 (ii)).
(iii) The frontier is exact: only adding a term raises the number of terms, so
the attempts that leave the bound are, for each result with `N` terms, "add a
term" and its `N` obstructed `xrx`, each with two builds: `1 + N` attempts and
`1 + 2N` entries per such result (computed true in all four runs;
`evidence/second/frontier_*.csv`). Rounds `0 … N − 2` within the bound agree
with the counts without bound (a result of round `k` has at most `k + 2`
terms): `rounds_agreeing_with_unbounded_formula` all true.

**D15. With `bra` given, passing on holds in no result.** `bra` persists
(D6), and `arb`, `bra`, passing on would give `ara`: `passing_on_refutes_bra`
(1:R7, no change). Likewise "never both `xry` and `yrx`" holds in no result of
that beginning. Computed: `follows_anchored_with_bra.csv` and
`follows_free_with_bra.csv`, `passes_on` and `both_ways_never` with no
`first_holds`. Under the first seed both held in results of that beginning
after removing `bra`.

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
`follows_free_without_bra.csv`.) From the beginning with `bra` the first two
statements are refuted in every result (D15) and the last two are independent
("every term first": holds in what is given, fails after adding a term;
"always both ways": holds, fails after adding a term and `arc`, round 2).

**N4. That there are exactly two terms.** Holds in what is given, fails after
one change (add a term). This is the one item of 1:N4 that still does not
follow; the other three — `arb` stays asserted, `a` and `b` stay two, something
is asserted — now follow (D6).

**N5. Anything about the asserting that is not true of every legal state
containing what is given.** By D9 every such state is a result, so a
statement that holds in one of them and fails in another does not follow. Of
the fourteen statements tested, those holding in every result within the bound
are exactly "no `xrx`", "at least one term", "at least two terms", "something
is asserted", and with names "`arb` is asserted", "`a` and `b` are two terms",
plus "`bra` is asserted" when `bra` is given; each is proved for all results
(D6). Every other statement has a result where it holds and one where it
fails, except the two of D15 under the beginning with `bra`.

**N6. Which answer an obstructed change gets.** Refusal is always possible;
removal never (R3); a build always (adding a term is never obstructed, D3).
No result needs a build, and no result needs an obstructed change or an
identification to be attempted at all (D10). "Must be answered" does not
determine the answer.

**N7. Growth.** Nothing forces terms to be added: what is given adds no term,
and one change gives a result that adds one (§6). That every result is finite
is derived (D6); whether terms can be added without end is not given (C3).

**N8. That the counts never decrease.** Terms: from what is given, add `c`,
then identify `a` and `c` (unobstructed, nothing is asserted between them):
back to what is given; terms 2, 3, 2
(`attempts_bound3_anchored_without_bra.jsonl`, state `3:01:0-1`, change
"identify a and c", outcome `2:01:0-1`). Assertions: add `c`, `arc`, `d`,
`ard`, then identify `c` and `d`: assertions 3 then 2. Size: the same
witnesses. What is monotone is not a count but the carrying map (D5) and the
fewest classes (D13).

**N9. That a result once left is never returned to; that every result
returns to what is given.** The first fails by the witness of N8. The second
fails: the beginning with `bra` never reaches the beginning without (R8), and
within the bound only 14 of 1 090 (ANCHORED, without `bra`), 83 of 545 (with
`bra`), 32 of 9 841 and 363 of 9 212 (FREE) results reach what is given
(`results_that_reach_what_is_given`; column `reaches_what_is_given`).

**N10. That reachability among results is symmetric, or that it is
antisymmetric.** Neither. Within 3 terms (ANCHORED, without `bra`): of the
1 156 ordered pairs 439 are reachable, and 34 unordered pairs of distinct
results reach each other both ways (for instance what is given and
`a b c; arb arc`); with `bra`, 161 of 289 and 28; FREE: 153 of 289 and 16,
62 of 100 and 10 (`summary.json`, `reachability`).

**Refuted** (each a proved impossibility): `a` and `b` one term to begin with
(R1, D1); an answer that makes adding `xrx` performable (R2, D4); removing the
obstruction of any obstructed change, and any change with the outcome of a
removal (R3, D7); a result with fewer than two terms, in particular the
one-term state (R4, D6); identifying `a` and `b`, or un-asserting `arb`, ever
(R5, D6); an answer, or an identification, that reaches a result additions do
not reach (R6, D10); `bra` together with passing on, and, with `bra` given,
passing on in any result (R7, D15); the beginning with `bra` reaching the
beginning without (R8, D6); a result that does not contain what is given
(R9, D9); a result reached in fewer changes than its size difference, or with
fewer terms or assertions than what is given (R10, D8, D6); a change that
lowers the fewest classes (R11, D13).

## 6. The exploration

**Protocol.** From each beginning, under each reading of sameness (four
runs): round by round, every change on every result first reached in the round
before (C6), each result's changes fewest additions first (identifications add
nothing; then adding a term; then adding an assertion — the seed's order).
Refusal and every build are kept as alternatives; "remove the obstruction" is
recorded as impossible on every obstructed attempt. For every attempt within
the bound of 3 terms the change, the obstruction and every answer are
recorded: `evidence/second/attempts_bound3_*.jsonl` (156, 86, 313 and 148
attempts). Within the declared bounds attempts are counted and their answers
checked (D10), not recorded one by one. Attempts on what is given:
`evidence/second/given.json`.

**The five attempts on what is given, without `bra`** (names kept):

| change | adds | obstruction | outcome or answers |
|---|---|---|---|
| identify `a` and `b` | 0, 0 | `arb` | refused: nothing changes · remove the obstruction: impossible · build: the state itself |
| add a term | 1, 0 | — | `a b c`; `arb` (1, 0) |
| add `ara` | 0, 1 | `ara` | refused · impossible · build: add `c`, add `arc` (1, 1); or add `c`, add `cra` (1, 1) |
| add `bra` | 0, 1 | — | the other beginning (0, 1) |
| add `brb` | 0, 1 | `brb` | refused · impossible · build: add `c`, add `brc`; or add `c`, add `crb` |

With `bra` the list is: identify (obstructed by `arb` and `bra`), add a term,
add `ara`, add `brb` (both obstructed): four attempts. The first derivation
had six and five, the difference being the removals.

**Results by what they add to what is given** (ANCHORED, without `bra`, bound
4; `evidence/second/added_*.csv`). No number is negative, and every group
appears in one round only: the round is terms added plus assertions added
(D8), where the first derivation's table had groups spread over several rounds
by destroyed givens.

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
20; `evidence/second/rounds_*.csv`):

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
`k` new terms costs `k`), so 100 rounds cannot be listed; the set of results
of round `k` is determined for every `k` by D8 and D9 — membership is a
formula — and only its size beyond round 20 is left open (O2). For comparison,
the first derivation's round 20 without bound had 2 007 940 774 results under
FREE without `bra`: one more, the state with 22 terms and nothing asserted,
which is not a result here.

**Totals.** Results within the bound: 9 841 (FREE, no `bra`: 2, 15, 217,
9 607 by number of terms), 9 212 (FREE, `bra`: 1, 9, 176, 9 026), 1 090
(ANCHORED, no `bra`: 2, 32, 1 056), 545 (ANCHORED, `bra`: 1, 16, 528); census
at 5 terms: 90 562 and 45 281. Changes attempted: 253 611, 235 665, 17 737,
8 596 (census 2 299 273 and 1 126 996), of which obstructed 121 777, 114 691,
9 414, 4 707. Results with at least two terms in which every identification is
obstructed: 633, 614, 272, 136; what is given is one under either beginning.

**Frontier.** Every result with `N` terms, each with `1 + N` attempts leaving
the bound and `1 + 2N` frontier entries: 9 607 results, 57 642 attempts,
105 677 entries (FREE, no `bra`); 9 026, 54 156, 99 286 (FREE, `bra`); 1 056,
5 280, 9 504 and 528, 2 640, 4 752 (ANCHORED). The census counts 89 472 and
44 736 frontier results (984 192 and 492 096 entries) and does not export
them. `evidence/second/frontier_*.csv`, `summary.json`.

**Reachability within 3 terms.** For every ordered pair of results the
carrying map (or its absence) is listed in `reach_bound3_*.csv`, and agrees
with the search along the changes (D12).

**Reproducibility.** `python code/generate_second.py` rewrites every computed
file of `evidence/second/`; `MANIFEST.sha256` lists their hashes;
`python code/generate_second.py --check` regenerates into a temporary folder
and compares every computed file, in both directions (it matched).
`python code/lean_report_second.py` rebuilds both Lean libraries and rewrites
`evidence/second/lean_axioms.txt`, refusing if the build warns of `sorry` or a
cited theorem depends on an axiom other than `propext`, `Classical.choice`,
`Quot.sound`. The first derivation's `python code/generate.py --check` and
`python code/lean_report.py` were re-run after this work and its evidence
regenerates unchanged. Tests: 193 passed, both derivations; line coverage
100.00 %, branch coverage 99.24 % of all of `code/`
(`python code/xry/gate.py coverage.json`); `mypy --strict` clean.

## 7. Alternatives: kept, or eliminated by proof

| Alternative | Status |
|---|---|
| `bra` asserted / not asserted to begin with | both kept (N1, N2); all runs done for both |
| FREE / ANCHORED sameness | both kept (C4); all runs done for both |
| `a`, `b` one term to begin with | eliminated (D1) |
| a third legal beginning on the given terms | eliminated (D2) |
| more terms or assertions to begin with | kept as results of the chosen beginning (D9) |
| refuse / build for each obstructed change | both kept in the records; as results they coincide with additions (D10) |
| "remove the obstruction", for any obstructed change | eliminated (R3, D7); recorded as impossible on every obstructed attempt |
| "remove the obstruction" read as withdrawing the change | kept as a reading; coincides with refusal (C7) |
| builds with more than one added term or assertion | kept as results (D9); not listed as answers beyond the fewest (C7) |
| every legal state containing what is given, within the bound | kept; none dropped (D14) |
| counting an answered change as one | not computed; same results (D10), rounds differ |
| assertions with multiplicity | neither computed nor eliminated: open (O1) |

**Results of the first derivation that do not hold under this seed** (each
with the claim that replaces it): 1:D2's "each beginning is one change from
the other" (one way only, D2, R8); 1:D5's "cleared by removing the assertions
between the two terms" (nothing clears it, D7); 1:D7's "under FREE every result
is reachable from every result" (fails, R8, N9, D13); 1:D8's formula with
destroyed givens (collapses to the size difference on results, D8; states with
a destroyed given are unreachable, R9); 1:D9 "everything legal is a result"
(refuted, R9; replaced by D9); 1:D10's removal answers (not available, R3);
1:N4 (three of its four items now follow, D6); 1:N5 (narrowed, N5); 1:N6's
"removal is possible exactly for identifications" (never, N6); 1:R4 and 1:R5
are strengthened (R4, R5). Everything else cited stands with the re-check
given at its citation.

## 8. Open

- O1. Assertions with multiplicity (C1 unchosen).
- O2. The number of results of rounds 21–100 (finite and determined by D8, D9).
- O3. Lean: the "if" direction of D12 for carrying maps that merge terms (the
  identifications along the map). Proved on paper; the one-to-one case and
  the additions are in Lean; checked by computation within 3 terms.
- O4. Listing results beyond the declared bounds (the frontier says where to
  continue; the census gives the counts at 5 terms with names).
- O5. Readings of "build structure" other than C7: by D10 they cannot change
  the results; they could change which records count as answers.

Closed, relative to the first derivation: 1:O3 (rewriting) for the changes of
this seed (D11); 1:O6 (persistence for sequences) for this seed, in the
stronger form D7. The first derivation's files are not changed by this, so
its ledger keeps both items open for the first seed.

## 9. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Homomorphisms of directed graphs, and the homomorphism order** (Hell and
  Nešetřil, *Graphs and Homomorphisms*). A carrying map (D5) is a homomorphism
  of loopless digraphs that also fixes two marked vertices; D12 says that the
  process reaches `t` from `s` exactly when such a pointed homomorphism
  exists, so reachability is the homomorphism preorder on pointed digraphs.
  Mutual reachability (N10) is homomorphic equivalence, whose classes are
  represented by cores; that the chromatic number is monotone under
  homomorphisms is textbook, and D13 is that fact stated for the underlying
  undirected graph; that a directed cycle maps to a directed cycle exactly when
  the length of the second divides the length of the first is a standard
  exercise (used in `tests/test_second_reach.py`). Different here: under the
  first seed the process was not confined to homomorphisms (a removal is not
  one), and every state was reachable from every state; striking one kind of
  change from the seed turns the process into the homomorphism preorder, with
  the two given terms as marked vertices, and the seed does not name any of
  this.
- **Extensions of a fixed structure; enumeration.** The results (D9) are the
  loopless digraphs into which the given arc embeds with its endpoints marked;
  their numbers by size (K1: 2, 32, 1 056, 89 472, 22 638 656 for 2–6 points
  with the two endpoints marked; 2, 15, 217, 9 607, 1 540 943 unmarked, the
  digraph counts minus one) come from the same Pólya counting as in the first
  derivation, restricted. Counts of digraphs with a marked arc are not recalled
  as a published sequence.
- **Insertion-only edit distance.** When only insertions are allowed, edit
  distance is the size difference; D8 is that remark, with the twist that the
  seed also allows identifications, which turn out never to shorten a path
  (D10) because they lower the size while every path must raise it by at least
  the size difference.
- **Identification of non-adjacent vertices** (Harary and Hedetniemi's
  achromatic number, and elementary homomorphisms): as in the first paper;
  now every change is a homomorphism or an inclusion, so nothing leaves the
  homomorphism order.
- **Irreflexive plus transitive gives asymmetric** (strict partial orders):
  `passing_on_refutes_bra`; under this seed it becomes D15, a statement about
  every result of one beginning, because `bra` cannot be removed.
- **Independence by two models**: N1, N2, as before.

What appears to be specific to this seed: that "remove the obstruction", one
of the two answers the seed names, is realisable for no obstructed change
(R3); that the fewest changes is the plain size difference with identifications
never on a shortest path (D8, D10); that the given is never diminished and yet
can be returned to (D6, N9); and that the rewriting step is now formal (D11).
