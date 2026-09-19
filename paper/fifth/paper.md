# What follows from `arb` once, no `xrx`, counted assertions, and four kinds of change

Fifth derivation. Input: `prompt/fifth/seed_prompt.md`. Task:
`prompt/fifth/prompt.md`. Claim IDs refer to `paper/fifth/claim_ledger.md`;
an ID written `1:D8` refers to the first derivation's ledger
(`paper/claim_ledger.md`, paper `paper/paper.md`), `2:D8` to the second's
(`paper/second/`), `3:D8` to the third's (`paper/third/`), `4:D8` to the
fourth's (`paper/fourth/`). Lean names in the namespace `Seed.Fifth` are in
`lean4/Fifth/`; names in `Seed.Fourth`, `Seed.Third`, `Seed.Second`, `Seed`
are the earlier derivations' (`lean4/Fourth/`, `lean4/Third/`,
`lean4/Second/`, `lean4/H3V7N5QF/`). Where a short name exists in two
libraries (`identify_legal_iff`, `remove_legal`) the fifth's is meant unless
the namespace is written. The axiom report for every theorem cited here, of
any of the five libraries, is `evidence/fifth/lean_axioms.txt`. Computed
files are in `evidence/fifth/`, written by `python code/generate_fifth.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; the unchosen
readings are listed), **derived** (proved), **computed** (output of `code/`),
**refuted** (proved impossible), **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the fifth seed, and the re-check says whether the result *survives
removal lowering a multiplicity and identification merging terms*. The
re-check is one of five kinds. *(no change)*: the statement mentions no
change, or only the state, so it stands as it is. *(through the embedding)*:
the statement is about the fourth seed's changes; every change of the fourth
seed is a change of the fifth (`Step4.toStep5`, `Reach4.toReach5`), and a
change of the fifth is a removal, an identification, or a change of the fourth
(`Step5.cases4`); so what the fourth proved for *every* sequence of its
changes holds for the fifth's sequences of additions, and what it proved
*from* "a change only adds" must be looked at on removals and
identifications — where it is either re-proved or refuted by a witness.
*(on supports)*: the statement is the first derivation's, about states
asserting nothing twice; between such states a change of the fifth seed is a
change of the first on the supports (`Step5.toStep`, with `toSt_remove`,
`toSt_identify`), so the first's statement is the restriction of the new one.
*(re-proved)*: the earlier proof used something the fifth seed changes, and a
statement covering the four kinds on counted states is proved afresh.
*(computed again)*: a computed statement of the fourth derivation is re-run
beside the fifth exploration and compared on the results containing what is
given. Results of the earlier derivations that fail under the fifth seed are
listed in §8.

## 0. Findings in brief

1. The fifth seed is the fourth (assertions counted) with the first seed's
   four kinds of change restored: identifying two terms and removing an
   assertion are changes again, and removing lowers a multiplicity by one
   (given, §1). So the state is the fourth's and the changes are the
   first's; everything the fourth derivation argued from "a change only
   adds" had to be looked at again, and most of it does not survive (§7).
2. `a` and `b` are two terms; there are two beginnings, with and without
   `bra`, and now each is one change from the other in both directions
   (D1, D2). What is given is not kept: `arb` can be removed, its
   multiplicity can fall to zero and rise again, and `a` and `b` can be
   identified once nothing is asserted between them (N13, N15).
3. The obstructed changes are exactly the additions of some `xrx` and the
   identifications of two related terms (D3). A result with `n` terms and
   `d` asserted pairs has `C(n, 2) + d + 1 + n²` changes, `n` plus the number
   of related pairs of them obstructed. "Remove the obstruction" is now a
   real answer for an obstructed identification — `M(u,v) + M(v,u)`
   removals, then the identification — and it, refusal and the builds reach
   nothing the unobstructed changes do not reach (D5, D10).
4. **The cost does not survive as the size difference.** The fewest changes
   to a result is the first derivation's formula with size counting
   multiplicities: *size minus the size of what is given, plus two for each
   destroyed given* (D8). The size difference survives exactly on the
   results that contain what is given. Every change moves the cost by an odd
   amount, so no change keeps the round, and a result is reached by
   sequences of every length of the right parity (D8, D13).
5. **The results extend from "everything containing what is given" to
   everything.** Every legal state with at least one term is a result of
   either beginning, its names anywhere (D9). The fourth seed's results are
   exactly the results with no destroyed given, at the same rounds, reached
   by the same shortest sequences (D9, computed again on every run).
6. **The reachability criterion does not survive.** Containment is still
   sufficient but no longer necessary. A result reaches another exactly when
   the names, if one term at the start, are one term at the end (names
   kept); always (any rewriting) (D12).
7. **One-way reachability does not survive.** Every result with `a` and `b`
   two terms reaches what is given; two different results reach each other;
   every result reaches itself in two changes; any two results are
   comparable (D13). What is left of one-way reachability is the first
   derivation's: once `a` and `b` are one term they stay one term (D7).
8. Within the bound (terms and rounds) the exploration is complete, certified
   by an independent count by terms, total multiplicity and destroyed givens
   (D14); the frontier is exported in two parts; 100 rounds complete with the
   given terms only, where round `r` has `2r` results for `r ≥ 3` (D17).
   Everything claimed as derived is in Lean, including the every-writing
   statements (target 6 of the plan closed), the answers, and the comparison
   with the fourth derivation (`Fifth/Compare.lean`); proved in the paper and
   checked by computation only: the within-bound completeness (D14), the
   characterisation of the changes that raise the cost by exactly one
   (D8(iv)), the exactness of the shortest-sequence counts (D14), and the
   two-term closed forms (D17).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2‴ | An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G3′ | `arb` is asserted with multiplicity one. |
| G4 | For no term `x` may `xrx` be asserted. |
| G5 | Whether `bra` is asserted is not given. |
| G6 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G8 | A change that makes some `xrx` asserted is obstructed. |
| G9 | An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which; record the change, the obstruction, the answer. |
| G10 | A refused change is recorded and changes nothing. |
| G11 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, prove what is complete within it. |
| G14 | Any outcome is valid. |

G2‴ (the removal clause) and G6, G7 are the sentences that differ from the
fourth seed (`diff`; `research/fifth/reading_the_seed.md`); G6 and G7 are the
first seed's word for word. G1, G3′, G4, G5, G8–G14 are the fourth seed's.

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry`, multiplicity | given (G1, G2‴) | |
| adding raises a multiplicity by one; removing lowers it by one | given (G2‴) | |
| asserted = multiplicity at least one; the counted state | chosen (4:C1′, no change) | the fourth's model, unchanged |
| an assertion has a first and a second term | derived (1:§2, no change) | |
| legal state (no `xrx`) | given (G4) | |
| `a`, `b` are two terms | derived (D1) | |
| what is given: the terms `a`, `b`; `arb` once; `bra` once or not at all | given (G3′), chosen (C2′) | unchosen: `bra` `k ≥ 2` times, or more terms; harmless (D9) |
| supply of letters not capped | chosen (C3) | harmless for results and fewest changes |
| `r` does not write a term | chosen (C9) | writing only |
| change, four kinds; what identifying does | given (G6, G7) | |
| the multiplicities of the pairs an identification merges add up | chosen (C5″) | unchosen: the larger of the two; same results and cost (D19) |
| removing what is not asserted, identifying a term with itself: not changes; adding what is asserted is a change | chosen (C5″) | |
| the order of the changes of a result | chosen (C6) | identifications and removals (no addition), a term, the assertions |
| obstructed change | given (G8) | characterised: derived (D3) |
| the obstruction of a change | chosen (C7) | the assertions that would become some `xrx`, with their multiplicities |
| refuse / remove the obstruction / build structure | given (G9, G10) | content: chosen (C7); removal a sequence of changes for an identification, refusal for adding `xrx`: derived (D5, R3); results independent of the answers: derived (D10) |
| destroyed given, cost | derived (D8) | the first derivation's, with size counting multiplicities |
| result | chosen (C6) | a legal counted state up to sameness |
| the results, as a set | derived (D9) | every legal state with at least one term; the fourth's are those with no destroyed given |
| sameness | given (G12) | two readings, both kept: chosen (C4) |
| terms and assertions added to what is given | given (G11) | assertions counted with multiplicity; may be negative |
| round; what counts as one change | chosen (C6) | the round of a result is its cost (D8) |
| bound, frontier | given (G13) | bound on terms and on rounds: chosen (C8′) |
| shortest sequences reaching a result; sequences of every length | computed (K7); derived (D13, D14) | exact within the bound where D14 says; infinitely many sequences in all |
| reachability between results | derived (D12) | the names decide; mutual within classes (D13) |
| parity of the cost | derived (D8) | every change moves it by an odd amount |
| counts of results by terms, total multiplicity, destroyed givens | computed (K1) | by series with the first's five kinds of named pair |
| what survives removal and identification | derived (§7; `Fifth/Compare.lean`) | see §8 for what does not |

## 3. Readings that had to be chosen

C3, C4, C6, C9 are the earlier derivations', unchanged; C2′, C8′ are the
fourth's; C5″ and C7 are restated for the four kinds on counted states.

**C2′. To begin with: the terms `a` and `b`; `arb` once; `bra` once or not
at all.** As 4:C2′. Harmless in a stronger sense now: every legal state is a
result of either beginning (D9), so any other beginning is a result of the
chosen one and has the same results.

**C3. No cap on the number of terms.** The sequences used in the proofs of
D8 and D9 never have more terms than `max(2, terms of the target)`, except
the sequence of D12 between two results, which uses two fresh terms to move
the names and so at most `max(terms) + 2`; a cap `L ≥ 4` leaves every
statement below about results with at most `L − 2` terms unchanged, and a cap
`L ≥ 2` leaves D8 and D9 unchanged.

**C4. Sameness, two readings, both kept.** FREE and ANCHORED as 1:C4 on
counted states (4:C4). Under ANCHORED a state remembers which terms carry the
names, and one term may carry both after an identification (1:C4); the least
writing puts the names first (4:§change log 2).

**C5″. What is a change.** Adding an assertion that is asserted already is a
change (it raises the multiplicity, 4:C5′). Removing an assertion that is
not asserted would lower zero, which is no number of times, so it is not a
change; identifying a term with itself replaces nothing, so it is not a
change (1:C5). A new term comes with no assertion; an added assertion is
between terms that are there. **Identification with multiplicities.** "Replaces
both by one term in every assertion": each of the `k` times an assertion is
asserted has its terms replaced, so when two different assertions become one
pair their times add up — the multiplicity of a pair of the outcome is the
sum of the multiplicities of the pairs that become it (`code/fifth/state.py`
`identify`, through the fourth's `image`; Lean `MSt.identify`, a sum over the
pairs that become `p`). Unchosen: another combination, for instance the
larger of the two. The two readings differ only when an identified pair is
related to a third term in the same direction. They give the same results
and the same fewest changes (D19): every proof below identifies terms only in
states with nothing asserted between the merged pairs, or uses only that a
merged multiplicity is at least each part and that an identification lowers
the size by at least one, which hold under both. So the unchosen reading is
kept as to records (the outcome of one identification) and eliminated as to
results and cost.

**C6. Results and rounds.** As 1:C6, 4:C6: a result is a legal counted state
up to sameness; round `k` attempts every change on every result first
reached in round `k − 1`; a performed change counts one; a refused change is
an attempt of its round that changes nothing; the further changes of an
answer count one each. Fewest additions first: identifications and removals
add nothing, then a term, then the assertions (the seed's order of kinds
among equals). Unchosen: an obstructed change and its answer counted as one;
other orders. The order cannot move a result to another round (D8: the round
of a result is its cost, which does not depend on the order of attempts);
counting an answered change as one would move rounds, not results (D10).

**C7. Obstruction and answers.** The obstruction of a change is the set of
assertions that would become some `xrx`, with their multiplicities: for
identifying `u`, `v`, those of `urv`, `vru` that are asserted; for adding
`xrx`, that assertion itself. *Refuse*: recorded, nothing changes. *Remove
the obstruction*: for an identification, lower each obstructing assertion to
zero — `M(u,v) + M(v,u)` removals — then identify (D5); for adding `xrx` the
obstruction is the assertion the change itself adds, and removing it is not
adding it, which is refusal: recorded on every obstructed addition as
`"remove the obstruction": "coincides with refusal: the obstruction is the
assertion the change itself adds; removing it is not adding it, and nothing
changes"` (1:C7's reading; the fourth's reason "no change lowers a
multiplicity" no longer holds, the conclusion does). *Build structure*: as
4:C7 — by additions, reach a legal state that stands for the would-be outcome
(the added terms read as `x`, multiplicities adding up); fewest additions
first: for adding `xrx`, a term `t` and `xrt` or `trx` (exactly two one-term
builds, 4:D10); for an identification, the state itself (1:C7). Under any
reading in which the further changes are changes of the four kinds, the
results are the same set (D10). "Declare which" is read as in 1:C7: every
answer is recorded with its kind and all are kept (N6).

**C8′. Bound on terms and on rounds.** As 4:C8′: within any bound on terms
the results are infinite (`arb` `k` times, every `k`), so every exploration
is bounded in terms and in rounds: 5 terms (FREE) or 4 terms (ANCHORED) with
8 rounds; 3 terms with 12 rounds; 2 terms with all 100 rounds. Under ANCHORED
a counts-only census at 5 terms with 8 rounds. Full attempt logs at 2 terms
and 4 rounds; reachability among the results of 3 terms and 6 rounds, along
the changes among the results of 3 terms and 9 rounds (enough for every
sequence the proof of D12 uses, §4). The frontier has two parts (4:C8′).
A result has about twice as many changes as under the fourth seed and the
same bounds completed in about eight minutes, so none was lowered.

**C9.** `r` writes assertions, not terms.

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. `a` and `b` are two terms.** Lean: `names_apart_of_legal` (4:D1,
1:D1; no change).

**D2. The beginnings.** On the given terms alone, exactly two legal states
asserting nothing twice contain what is given (`two_states_on_given_terms`,
1:D2, no change; they are two of infinitely many states on those terms,
4:D2). Each is one change from the other, in both directions: add `bra`
(`givenA4_to_givenB4` through the embedding) and remove `bra`
(`givenB4_remove_bra_eq`, `no_return_fails`). 1:D2's `givenB_to_givenA`
survives, re-proved; 4:D2's `givenB4_never_givenA4` does not (§8). The
one-term state is two changes away without `bra` and three with it
(`givenA4_to_oneTerm4`, `givenB4_to_oneTerm4`; 1:D9's
`givenA_to_oneTerm`, `givenB_to_oneTerm` re-proved).

**D3. Which attempts are obstructed; how many changes a result has.** An
attempt (`Try5`: the four kinds without the conditions that make them
unobstructed) makes some `xrx` asserted exactly when it adds some `xrx` or
identifies two related terms: `Try5.obstructed_iff`, `Try5.legal_iff`,
`Try5.step5_or_obstructed`; removal is never obstructed (`remove_legal`),
adding a term never (`addTerm_unobstructed4`, 4:D3 through the embedding),
adding an asserted `xry` with `x ≠ y` never
(`addAssertion_again_unobstructed`, 4:D3), and identifying `u`, `v` is
obstructed exactly when `urv` or `vru` is asserted (`identify_legal_iff`;
1:D3's `identify_legal_iff` re-proved with multiplicities: the outcome gives
`uru` the multiplicity `M(u,v) + M(v,u)`). So a result with `n` terms and
`d` asserted pairs has `C(n, 2) + d + 1 + n²` changes — every unordered pair
of terms, one removal per asserted pair, a term, every ordered pair — of
which the `n` additions of some `xrx` and the identifications of related
pairs are obstructed (computed: `attempts_equal_formula`,
`obstructed_equal_formula` true in every run).

**D4. Adding `xrx` is obstructed in every state.** `adding_xrx_always_obstructed4`
(4:D4, no change: the fourth's statement is about one attempt). It stays
obstructed after every sequence of changes since every reached state is
legal (`Reach5.legal`).

**D5. What clears an obstruction.** If `urv` is asserted then after any one
performed change either that change was the removal of `urv`, or `urv` is
still asserted, or the change was an identification and the assertion
between the replaced terms is asserted: `obstruction_persists5` (1:D5's
`obstruction_persists` re-proved with multiplicities: a removal lowers `urv`
by one, and only the removal of `urv` itself can bring it to zero — an
addition raises, an identification carries `M(u,v)` to at least itself,
`identify_M_ge`). So identifying `u` and `v` stays obstructed until `urv` and
`vru` are lowered to zero. The answer "remove the obstruction" is a sequence
of performed changes: lower `urv` to zero, lower `vru` to zero, identify —
`M(u,v) + M(v,u) + 1` changes (`reach5_lower`, `remove_answer5`; 1:D10's
`remove_answer_one_way`, `remove_answer_two_way` re-proved as one statement).
Removing first, or identifying first and then lowering the `uru` that results
to zero, gives the same state (`remove_obstruction_first_or_last5`; 1:D10's
`remove_obstruction_first_or_last` re-proved).

**D6. What every result has.** Every result is legal, well formed, has at
least one term, and is finite (`Reach5.legal`, `Reach5.wf`,
`Reach5.nonempty`; 1:D6 re-proved). Nothing else is kept: not the terms,
not the assertions, not the names apart (N13–N15).

**D7. The one irreversible change (ANCHORED).** Once `a` and `b` are one
term they are one term after every sequence of changes, and `arb` is never
asserted again: `Step5.names_stay_merged`, `Reach5.names_stay_merged`,
`Reach5.arb_gone_for_good` (1:D7 re-proved: the names follow the merge map
and no change tells two terms apart). From the one-term state what is given
is never reached (`merged_never_apart`). Under FREE there are no names and
every result reaches every result (D12).

**D8. Fewest changes (cost).** Let what is given have `m0` assertions (`1`
without `bra`, `2` with), so size `2 + m0` with size = terms + the sum of the
multiplicities. For a legal state `G` with names let `lost(G)` be the number
of given assertions with multiplicity zero between the terms named `a` and
`b` if these are two terms, and `m0 + 1` if they are one term (Lean
`lostA5`, `lostB5`). Then the fewest changes from what is given to `G` is

    size(G) − (2 + m0) + 2 · lost(G)

— the first derivation's formula (1:D8) with size counting multiplicities.
*(i) Lower bound.* `size + 2·lost` (Lean `costA5`, `costB5`) rises by at
most one per performed change (`Step5.costA_le`, `Step5.costB_le`): adding a
term or an assertion raises the size by one and destroys nothing (an
addition leaves the state contained in its outcome, `Step4.contains`, 4:D5
through the embedding; `lostA5_le_of_contains`); a removal lowers the size by
one (`size_remove`) and destroys at most one given, since it lowers one
multiplicity by one and `arb`, `bra` are different pairs
(`lostA5_remove`, `lostB5_remove`); an unobstructed identification lowers the
size by exactly one — the total multiplicity is kept, every unit of
multiplicity being carried to exactly one pair of the outcome
(`total_identify`, `size_identify`) — and destroys at most one given, since
it merges `a` and `b` only when nothing is asserted between them, which was
already lost, and otherwise carries each multiplicity to one at least as
large (`identify_M_ge`, `lostA5_identify`, `lostB5_identify`). A refused
change changes nothing. So a result reached in `n` changes has
`cost ≤ n + cost(given)`: `Reach5.costA_le`, `fewest_changes5_lower_A`,
`fewest_changes5_lower_B` (1:D8's `Step.costA_le`, `fewest_changes_lower_A`
re-proved). *(ii) Upper bound.* Remove the given assertions that `G` lacks
(`lost` removals, when `a`, `b` are apart); then `G` contains the state
reached and the fourth derivation's additions reach it in
`|terms(G)| − 2 + total(G) − (m0 − lost)` changes (`reach4_of_contains`, 4:D9,
through the embedding `Reach4.toReach5`); if `a` and `b` are one term in `G`,
remove the givens, identify `a` with `b` (the one-term state, `m0 + 1`
changes) and add: `removed_arb_contains`, `fewest_changes5_upper_A_apart`,
`givenA4_to_oneTerm4`, `oneTerm4_contains`, `fewest_changes5_upper_A_merged`,
and the `B` versions with the four cases of which givens are lacking;
together `fewest_changes5_A`, `fewest_changes5_B` (1:D8's `reach_by_edits`
replaced by removals then the fourth's additions). *(iii) Every writing.*
Changes commute with one-to-one rewriting (D11) and the cost is the same in
every writing (`costA5_rename`, `costB5_rename`), so the fewest changes to a
result is the cost of any of its writings:
`fewest_changes5_every_writing_A`, `_B` (target 6 of the plan closed; 1:O3
closed for the four kinds on counted states). *Under FREE* the names may be
placed anywhere and `lost` takes the first's closed form (1:D8): `m0 + 1` for
one term, `m0` for nothing asserted, `1` with `bra` given and no pair
asserted both ways, `0` otherwise; computed: the closed form equals the best
placement on every legal state with at most 3 terms and no multiplicity
above 2 (290 states, `free_cost_closed_form_mismatches` empty), and the round
of every explored result equals the formula in all twelve runs and both
census runs (`round_equals_cost_formula_for_every_result`). *(iv) Which
changes raise the cost by exactly one.* Along a shortest sequence every change
raises the cost by exactly one; by (i) these are: adding a term; adding an
assertion that restores no given; removing a given asserted once; identifying
`a` with `b`. Every other change lowers the cost by one, three or five (a
removal of another assertion; an identification that merges two other terms,
or makes a given asserted again by merging — lowering `lost` by one or two).
Proof from (i): the size moves by exactly one, up for an addition and down
otherwise (`Step5.size_step`); `lost` changes as computed in (i) and, for an
addition, falls exactly when a given is restored. Computed
(`code/fifth/cost.py` `raises_by_one`): the rule agrees with the outcome on
every unobstructed change within the bound of every run with names
(`cost_rule_disagreements` empty; 85 485 changes in the ANCHORED 4-term run).
*(v) Parity.* Every change moves the size by one and the destroyed givens
enter the cost twice, so every change moves the cost by an odd amount; the
size and the length of a sequence have a fixed parity (`Reach5.size_parity`):
no change keeps the round (computed: `changes_keeping_the_round: 0` in every
run), and a sequence between two states has the parity of their size
difference. **The cost survives only on results containing what is given**
(§7): there `lost = 0` (`lostA5_eq_zero_of_contains`) and the fewest changes
is the size difference (`fewest_changes5_of_contains_A`, `_B`), the fourth's
4:D8; but the size can fall along a change (`size_can_fall`: removing `arb`
from what is given), so "size rises by exactly one" and "every sequence has
the same length" (4:D8) do not survive — a result is reached by sequences of
different lengths (`length_not_unique`).

**D9. Everything legal is a result.** Every legal well-formed state with at
least one term is a result of either beginning, with its names on any terms:
`result5_iff_A`, `result5_iff_B` (from D12: `reach5_of_names`). 1:D9
re-proved with multiplicities and, new, with the names anywhere (the first
derivation placed them by a rewriting, 1:O3). **The results extend**: every
result of the fourth seed is a result of the fifth at the same round
(`results_extend_A`, `_B`, through the embedding), and the fifth has results
the fourth has not — the given terms with nothing asserted, one change away
(`results_grow`). The fourth's results are exactly the results with no
destroyed given: a result contains what is given exactly when `lost = 0`,
and then its round is its size difference (D8), the fourth's round.
Computed: in every run and census the results with no destroyed given, their
rounds and their numbers of shortest sequences are exactly the fourth
derivation's exploration's at the same bound and rounds
(`same_results_and_rounds_as_fourth_derivation`,
`same_shortest_sequence_counts_as_fourth_derivation`; 4:K1, 4:K2, 4:K7
computed again), and the fourth's independent counts are the `lost = 0` part
of this derivation's (`fourth_counts_are_the_lost_zero_part`, `counts.csv`;
4:K1 computed again).

**D10. Answers reach nothing new.** Refusal changes nothing; removing the
obstruction of an identification is a sequence of performed changes (D5,
`remove_answer5`); a build for `xrx` is two performed additions
(`build_answer5`, `build_answer5_reverse`, 4:D10 through the embedding), and
exactly two builds add one term (4:D10, R15: about additions and a reading
map, no change; computed on every beginning, `listed_builds_that_are_not_builds:
0`); the build for an identification is the state itself. Hence every answer
is a sequence of unobstructed changes and the results are the set reached by
unobstructed changes alone, under any reading of G9 in which the further
changes are changes of the four kinds (1:D10 re-proved). Computed: every
answer within the bound reaches an explored result no later than the round
of the state plus the changes it performs (`answers_reaching_something_new`
empty in every run; 48 691 removal answers recorded in the ANCHORED 4-term
run). The fourth's reading of a build — identifying the added term back
gives the would-be outcome — is now itself a change of the seed; it is
checked by computation (`is_build_of`) and, on supports, by the first
derivation's `build_gives_back` (on supports); a Lean statement on counted
states was attempted and not closed (change log 11).

**D11. Changes commute with one-to-one rewriting; sequences keep their
length.** `rename4_remove`, `rename4_identify` (with `merge_perm`:
replacing after rewriting is rewriting after replacing), `Step5.rename`,
`Reach5.rename`, `lostA5_rename`, `costA5_rename` (4:D11 through the
embedding for the two additions; the two new kinds re-proved).

**D12. Reachability: the names decide.** A legal well-formed state `t` is
reachable from a well-formed state `s` exactly when the names, if one term in
`s`, are one term in `t`: `reach5_iff`. Necessity is D7. Sufficiency
(`reach5_of_names`): remove every assertion (`reach5_clear`, one removal per
unit of multiplicity); identify every term other than the named ones into
`a` (`reach5_collapse`, unobstructed since nothing is asserted); move the
names onto the target's named terms — adding a fresh term and identifying it
with the term carrying a name leaves the fresh term carrying the name, since
the surviving term of an identification is the first (`move_a_pair`,
`move_b_pair`; eight changes through two fresh terms, `two_names_to`; or
identify `a` with `b` and move the one term, `merge_names`, `move_one`);
then the target contains the state reached and the fourth's additions reach
it (`reach4_of_contains`, 4:D9, through the embedding). Under FREE there are
no names and every result reaches every result. **The criterion does not
survive** (§7): containment is still sufficient (`contains4_reach5`, 4:D12
through the embedding) but not necessary — the beginning with `bra` reaches
the one without, which it does not contain (`criterion_fails`). Computed: the
criterion agrees with a search along the changes among the results within 3
terms and 9 rounds on every ordered pair of results within 3 terms and 6
rounds, in all four combinations (`criterion_agrees_with_search`; 421 201
pairs, names kept, no `bra`), and the fourth's containment implies the
fifth's reachability on every pair of the fourth's results
(`fourth_reachability_implies_fifth`; 240 100 pairs, of which the fourth
reached 7 685 and the fifth all).

**D13. Reachability is mutual within two classes; every result reaches
itself; any two results are comparable.** Reached and reaching back: if `t`
is reachable from `s` and the names of `t`, if one term, are one term in `s`,
then `s` is reachable from `t` (`reach5_symm`). So reachability is mutual on
the results with the names apart, mutual on the results with the names one
term, and one-way from the first class to the second (D7); every result with
`a ≠ b` reaches what is given (`reach5_back_A`, `reach5_back_B`); under FREE
all results reach each other. Any two results are comparable — one reaches
the other (`reach5_total`). Every well-formed state with a term reaches
itself in two changes: add a term and identify an old term with it, which
gives the state back (`add_identify_back`, `cycle2`); so the lengths of the
sequences reaching a result are unbounded (`Reach5.cycles`,
`Reach5.unbounded`), and infinitely many sequences reach every result.
**One-way reachability does not survive** (§7): the two beginnings reach
each other (`no_return_fails`), two different results are reachable from
each other (`antisymm_fails`), and a result is reached by sequences of
lengths 0 and 2 (`length_not_unique`). Computed: 193 482 unordered pairs of
different results reachable both ways among the 649 results within 3 terms
and 6 rounds (names kept, no `bra`), 16 794 ordered pairs unreachable — all
from the 27 results with the names one term to the 622 with them apart —
and every result has a two-change cycle in every run
(`results_with_a_two_change_cycle = results`).

**D14. Within the bound the exploration is complete; the frontier is exact;
the shortest-sequence counts are exact where said.** *Completeness.* Let the
bound be `N` terms and `R` rounds. Every legal state with at most `N` terms
and cost at most `R` lies at the end of the sequence of D8(ii), whose states
have at most `max(2, terms)` terms and whose cost rises by exactly one at each
change (it has length exactly the cost difference and each change raises the
cost by at most one); so every state on it is within the bound and, by
induction along it, found by the exploration in round = cost. Every explored
state is a legal state within the bound by construction. The results with
`n` terms, total multiplicity `t` and destroyed givens `lost` are counted
independently by the orbit method (K1): as the first derivation counted legal
states up to sameness by how the named terms stand — one term; neither
given asserted; `arb` only; `bra` only; both (1:K1, `count_named`) — with
the fourth's series `1 / (1 − x^L)` per cycle of the rewriting's action on
ordered pairs (4:D14) in place of the binomial, the named pairs `ab`, `ba`
getting `x / (1 − x)` when asserted; without names, all legal states, and
those with no pair asserted both ways, by the same series
(`code/fifth/orbits.py`); the destroyed givens of each kind are the first's
(`lost_of_kind`). The explored counts by (terms, total, lost) equal the
independent counts restricted to cost at most `R` in every run and census
(`explored_equals_independent_count`). *Frontier.* An attempt leaves the
bound on terms exactly when it is "add a term" on a result with `N` terms or
a build of an obstructed `xrx` on such a result (a removal answer never adds
a term): `1 + 2N` entries per such result whose changes were attempted
(`frontier_entries_are_1_plus_2N_per_state_with_N_terms` true in every
run); the results of round `R` are the second part. *Shortest sequences.* A
shortest sequence to a result consists of cost-raising changes (D8(iv)),
none of which removes a term except the identification of `a` with `b`; so
it never has more terms than the result, or one more when the result has `a`
and `b` one term; hence the count by dynamic programming over the explored
cost-raising changes is exact for every result with fewer than `N` terms or
with the names apart, and under FREE for every result (a FREE-shortest
sequence is ANCHORED-shortest for an optimal placement, which puts the names
apart on two or more terms). The flag `shortest_sequences_exact_within_bound`
records this per result (13 971 of 14 061 exact in the ANCHORED 4-term run;
all under FREE). *Rounds.* The number of results of round `r` without any
bound is given by the series and the cost formula (`layer_counts`); rounds
`0 … N − 2` of a run within `N` terms agree with it
(`rounds_agreeing_with_unbounded_formula`), since a result of round `r` has
at most `r + 2` terms (its cost is at least its number of terms minus two).
4:D14 survives with the split by destroyed givens added.

**D15. What is given, `bra` and passing on.** `bra` together with passing on
is impossible in any legal state (`passing_on_refutes_bra`, 1:R7, no change).
But 4:D15 — with `bra` given, passing on and "never both ways" hold in no
result — does not survive: `bra` can be removed, and both statements hold in
`a b; arb` (computed: `follows_*_with_bra.csv`, `passes_on` and
`both_ways_never` independent in every run with `bra`).

**D16. A result reached by two different shortest sequences.** The fourth's
witness `a b c; arb bra` (two additions in either order, `two_sequences4`,
through the embedding) and, new, `a b c; nothing asserted` — remove `arb`
then add the term, or the reverse — with two shortest sequences each
(computed, column `shortest_sequences_of_changes`); and every result is
reached by sequences of different lengths (D13).

**D17. Two terms: the results of every round in closed form.** With the
given terms only (names kept, `bra` not given) the results of round `r` are:
`arb` `1 + i` times, `bra` `j` times with `i + j = r` (`r + 1`; the fourth's
4:D17, surviving on `lost = 0`, with `C(i + j, i)` shortest sequences —
`two_term_sequences_equal_binomial` true); `arb` missing and `bra` `r − 1`
times (one, `r ≥ 1`); the one-term state (round 2); the names one term with a
second term and `r − 3` units of multiplicity between them (`r − 2`,
`r ≥ 3`): `1, 3, 5, 6` and then `2r`, 10 103 results in 100 rounds. With
`bra` given: `1, 4, 6, 7` and then `2r`, 10 106 results (proof: the cost of
each kind of two-term state, `code/fifth/evidence.py` `two_term_round_count`;
computed: `two_term_rounds_equal_closed_form` true on all 100 rounds of both
ANCHORED two-term runs). Without names: `1, 3, 3, 3, 3, 4, 4, …` (no `bra`).

**D18. Every state has a two-change cycle; no state keeps the round.** See
D13 and D8(v). 4:D18 (names kept, the exploration with `bra` is the
exploration without it with `bra` added once) does not survive: every legal
state is a result of both beginnings, but with different costs (`a b; arb`
is round 0 without `bra` and round 1 with it), so the rounds do not
correspond and the counts differ (14 061 against 17 240 at 4 terms).

**D19. The unchosen reading of identification gives the same results and
cost.** Under any reading in which the multiplicity of a merged pair is at
least each part and an identification lowers the size by at least one, the
lower bound of D8(i) holds (its identification case uses only these two
facts), the upper bound of D8(ii) and the sufficiency of D12 identify terms
only in states with nothing asserted at all or between the merged pairs
(where every reading agrees), and D7 depends on the names only. So the
results (D9), the cost (D8) and the reachability criterion (D12) are the same
under both readings; only the recorded outcome of an identification of two
terms both related to a third differs. Not in Lean (the Lean model fixes the
sum reading); the proof is this paragraph, and it is a proof about the Lean
proofs cited.

## 5. What does not follow

Each item has two legal witnesses among the results, or a proof.

**N1. `bra`. N2. Not `bra`.** Both beginnings are legal and contain what is
given. Lean: `bra_not_refuted`, `bra_not_derived` (1:N1, 1:N2, no change).

**N3. Anything on which two results differ**, and by D9 that is anything
about the asserting not true of every legal state: of the twenty-one
statements tested (the fourth's nineteen, plus "the names are one term" and
"nothing is asserted"), exactly "no `xrx`" and "at least one term" hold in
every result within the bound of every run (`statements_holding_in_every_result`),
and both are proved for all results (D6). Every other statement holds in
some result and fails in another in every run (`statements_that_do_not_follow`):
1:N5 returns in full, and the fourth's "`arb` is asserted", "`a`, `b` are
two terms", "something is asserted", "at least two terms", "`bra` is asserted
when given" no longer hold everywhere (§8).

**N4. That there are exactly two terms.** Holds in what is given, fails
after adding a term, and fails after two changes the other way (the
one-term state).

**N5. That what is given survives** (1:N4 returns). `arb` stays asserted:
fails after one change (`a b; nothing asserted`). `a` and `b` stay two
terms: fails after two changes without `bra`, three with it. Something is
asserted: fails after one change without `bra`, two with it
(`follows_*.csv`: first rounds 1, 2, 1 without `bra`).

**N6. Which answer an obstructed change gets.** Refusal is always possible;
removing the obstruction is possible exactly for an obstructed identification
(D5) and coincides with refusal for adding `xrx` (C7); a build is always
possible (adding a term is never obstructed, D3; the state itself for an
identification). No result needs a build, and no result needs an obstructed
change to be attempted at all (D10). "Must be answered" does not determine
the answer.

**N7. Growth.** Nothing forces terms or assertions to be added: what is given
adds none, one change gives a result that adds one of either, one change
gives a result with one assertion fewer. Every result is finite (D6);
whether terms or multiplicities can grow without end is not given (C3),
though every round has a new result (D9, D17).

**N8. That a result is reached by one sequence only, or by finitely many;
that results of one round are reached by equally many shortest
sequences.** Every result is reached by infinitely many sequences (D13). What
is given is reached by one shortest sequence (the empty one), `a b; nothing
asserted` by one, `a b; bra` by two (remove `arb` then add `bra`, or the
reverse), `a b c; nothing asserted` by two, `a c (a and b one term); nothing
asserted` by three, all of rounds 1–3 (column `shortest_sequences_of_changes`
of `results_*.csv`; 49 of the 14 061 results of the ANCHORED 4-term run have
one shortest sequence).

**N9. That the number of attempts on a result is the same for results of one
round with equally many terms.** It is `C(n, 2) + d + 1 + n²` (D3) and
depends on `d`: 6 for `a b; nothing asserted` and 8 for `a b; arb bra`, both
of round 1 (4:N10's "with equally many terms it follows" does not survive).

**N10. That nothing is asserted twice; that `arb` is asserted exactly once;
that all asserted assertions are asserted equally often; that `xry` and
`yrx`, when both asserted, are asserted equally often.** As 4:N11, 4:N12,
with the same witnesses (`follows_*.csv`).

**N11. That the two beginnings differ in what they reach, or in which
statements hold in some result.** Both reach every legal state (D9); every
statement independent under one beginning is independent under the other
(`statements_that_do_not_follow` the same list in every ANCHORED run). They
differ in the cost of each result (D8) and so in the rounds (D18).

**N12. That reachability is one-way, or that any two results are
incomparable.** Refuted and derived respectively: two different results
reach each other, and any two results are comparable (D13). 4:N8 ("that any
two results are comparable" does not follow) does not survive: it now
follows.

**N13. That a multiplicity never falls; that the number of terms, the total
multiplicity, the size, or the fewest classes of a split never falls.** All
refuted by witnesses: removing `arb` from what is given lowers the
multiplicity of `arb`, the total and the size (`arb_removed`,
`size_can_fall`); identifying `a` with `b` in `a b; nothing asserted` lowers
the number of terms; removing `brc` from `a b c; arb brc cra` lowers the
fewest classes from 3 to 2 (`tests/test_fifth_follows_invariants.py`).
Computed: in the ANCHORED 4-term run 10 853 changes lower the number of
terms, 19 441 a multiplicity, 30 294 the size, 3 730 the fewest classes
(`changes_lowering`). 4:D6, 4:D13, 2:D13 do not survive (§8).

**N14. That a state is contained in its outcome; that a sequence of changes
carries every assertion somewhere** (the fourth's containment, the second's
carrying map). Refuted: `contains_fails` (removing `arb`); a removal carries
the removed unit nowhere.

**N15. That `a` and `b` stay two terms; that `arb` stays asserted.** Refuted
under this seed (they held under the second, third and fourth): D2, N5.

**Refuted** (each a proved impossibility): `a` and `b` one term to begin with
(R1, D1); an answer that makes adding `xrx` performable (R2, D4); clearing an
obstructed identification by any change but the removal of the obstruction
(R3, D5); a state without terms (R4, D6); telling `a` and `b` apart again, or
asserting `arb` again, after identifying them; what is given reached from
the one-term state (R5, D7); an answer that reaches a result unobstructed
changes do not reach (R6, D10); `bra` together with passing on in one legal
state (R7, D15); a sequence of changes to a result shorter than its cost
(R8, D8); a legal state with at least one term that is not a result (R9,
D9); a change that keeps the cost, or the round, where it was (R10, D8(v));
a third one-term build for an obstructed `xrx` (R11, 4:R15); a pair of
results with the names apart that do not reach each other, or a pair of
results neither of which reaches the other (R12, D13); under the unchosen
reading of identification, a result or a fewest-changes count that differs
from the chosen reading's (R13, D19).

## 6. The exploration

**Protocol.** From each beginning, under each reading of sameness (four
combinations): round by round, every change on every result first reached in
the round before (C6), each result's changes fewest additions first —
identifications (each unordered pair once), removals (each asserted pair
once), a term, then every ordered pair as an addition, `xrx` included,
asserted already or not (`C(n, 2) + d + 1 + n²` changes). Refusal, the removal
of the obstruction (for an identification) and every build are recorded for
every obstructed attempt, with the declaration that removing the
obstruction coincides with refusal for adding `xrx` (C7); the exploration
spreads along unobstructed changes and checks the answers afterwards (D10).
Three explorations per combination (C8′): the main run (5 terms under FREE,
4 under ANCHORED, 8 rounds), a deeper run (3 terms, 12 rounds), and the
two-term run (the given terms only, all 100 rounds). Beside every run the
fourth derivation's exploration is made at the same bound and rounds and
compared on the results containing what is given (D9). Files per run
(`evidence/fifth/`, tag `bound{N}_rounds{R}_{reading}_{beginning}`):
`results_*.csv` (one row per result: terms, assertions counted and asserted,
largest multiplicity, additions to what is given, round, cost by formula,
destroyed givens, fewest classes, changes, obstructed identifications and
additions, whether its changes were attempted, shortest sequences and whether
the count is exact, whether it reaches what is given, whether the names are
one term, whether it contains what is given, whether it asserts nothing
twice), `added_*.csv`, `frontier_*.csv`, `rounds_*.csv`, `follows_*.csv`; per
combination `reach_bound3_rounds6_*.csv` (one row per result: how many
results it reaches and are reached from it, by the criterion and by search,
and the fourth derivation's count on the fourth's results) and the full
attempt log `attempts_bound2_rounds4_*.jsonl`; `counts.csv`, `given.json`,
`summary.json` (every check, per run), `lean_axioms.txt`, `MANIFEST.sha256`.

**Results within the bound** (K1, K2). Every check of every run passes
(`summary.json`; `python code/generate_fifth.py` prints one line per run).

| run | results | by terms | containing what is given (the fourth's) | names one term | shortest sequences (total) |
|---|---|---|---|---|---|
| FREE, no `bra`, 5 terms, 8 rounds | 5 015 | 1 / 30 / 520 / 2 215 / 2 249 | 5 010 | — | 20 633 677 |
| FREE, `bra`, 5 terms, 8 rounds | 9 492 | 1 / 34 / 756 / 4 128 / 4 573 | 8 594 | — | 28 291 532 |
| ANCHORED, no `bra`, 4 terms, 8 rounds | 14 061 | 1 / 74 / 2 288 / 11 698 | 11 157 | 222 | 11 558 117 |
| ANCHORED, `bra`, 4 terms, 8 rounds | 17 240 | 1 / 77 / 2 810 / 14 352 | 11 157 | 81 | 15 429 383 |
| FREE, no `bra`, 3 terms, 12 rounds | 3 198 | 1 / 56 / 3 141 | 3 195 | — | 653 040 848 |
| FREE, `bra`, 3 terms, 12 rounds | 4 421 | 1 / 62 / 4 358 | 4 058 | — | 664 905 154 |
| ANCHORED, no `bra`, 3 terms, 12 rounds | 17 057 | 1 / 158 / 16 898 | 12 467 | 1 575 | 874 315 151 |
| ANCHORED, `bra`, 3 terms, 12 rounds | 20 127 | 1 / 161 / 19 965 | 12 467 | 914 | 1 099 041 538 |
| FREE, no `bra`, 2 terms, 100 rounds | 2 653 | 1 / 2 652 | 2 651 | — | about 2.5 · 10^30 |
| FREE, `bra`, 2 terms, 100 rounds | 2 703 | 1 / 2 702 | 2 601 | — | about 2.5 · 10^30 |
| ANCHORED, no `bra`, 2 terms, 100 rounds | 10 103 | 1 / 10 102 | 5 151 | 4 852 | about 2.9 · 10^30 |
| ANCHORED, `bra`, 2 terms, 100 rounds | 10 106 | 1 / 10 105 | 5 151 | 4 754 | about 2.9 · 10^30 |

In every run the results containing what is given, with their rounds and
their shortest-sequence counts, are exactly the fourth derivation's
exploration's at the same bound and rounds (4:K1, 4:K2, 4:K7 computed again;
the fourth's 11 157, 5 010, 8 594, 12 467, 3 195, 4 058, 5 151, 2 651, 2 601
reappear as the `lost = 0` column). By destroyed givens (ANCHORED, no `bra`,
4 terms): 11 157 with none, 2 682 with `arb` missing, 222 with the names one
term. Every count by terms, total multiplicity and destroyed givens equals
the independent count (`explored_equals_independent_count`, D14), and every
result's round is its cost (D8).

**Rounds** (K2). ANCHORED, no `bra`, 4 terms
(`rounds_bound4_rounds8_anchored_without_bra.csv`): new results per round 1,
4, 13, 40, 129, 400, 1 195, 3 370, 8 909; of which containing what is given
1, 3, 10, 32, 104, 321, 959, 2 682, 7 045 (the fourth's); with the names one
term 0, 0, 1, 1, 3, 7, 19, 50, 141; without any bound on terms 1, 4, 13, 41,
138, 465, 1 614, 5 726, 20 833 (`layer_counts`; rounds 0–2 agree with the
run, as every round up to `N − 2` must). FREE, no `bra`, 5 terms: 1, 4, 10,
21, 54, 138, 393, 1 118, 3 276 against 1, 4, 10, 21, 55, 146, 425, 1 276,
4 040 without bound. With two terms, names kept: 1, 3, 5, 6, 8, 10, …, 200
(D17). Every round of every run has a new result.

**Attempts** (K3). 124 730 changes attempted and 35 372 obstructed in the
ANCHORED 4-term run; 7 and 3 in round 1 of the runs without `bra` (identify
`a` and `b`, obstructed by `arb`; remove `arb`; a term; `ara` and `brb`,
obstructed; `arb` again; `bra`), 8 and 3 with `bra`. The totals equal
`C(n, 2) + d + 1 + n²` and `n` plus the related pairs, summed over the
results whose changes were attempted (D3), in every run. Of the 85 485
unobstructed changes within the bound of the ANCHORED 4-term run, 57 552
raise the round by one and 27 933 lower it (by one, three or five); none
keeps it (D8(v)).

**Answers** (K4). 48 691 answers removing the obstruction are recorded in the
ANCHORED 4-term run (one per obstructed identification on a result whose
changes were attempted), 58 512 answers within the bound and 47 604 beyond
it; every answer within the bound reaches an explored result no later than
the round of its state plus the changes it performs (D10). The full logs
(`attempts_bound2_rounds4_*.jsonl`: 104, 130, 68, 77 attempts) record every
change, its obstruction with multiplicities, and every answer with its
further changes — for instance, on `a b; arb bra(2)`, identifying `a` and
`b` is obstructed by `arb` and `bra(2)`, and removing the obstruction is
three removals then the identification.

**Frontier** (K5). Every result with `N` terms whose changes were attempted
has `1 + 2N` entries: 3 873 such results and 34 857 entries in the ANCHORED
4-term run, 568 and 6 248 in the FREE 5-term run. The second part, the
results of round 8 whose changes await: 8 909 results with 234 087 changes
(ANCHORED, 4 terms), 3 276 with 110 132 (FREE, 5 terms); 200 results with
1 596 changes after round 100 with two terms.

**Results by what they add to what is given** (K6;
`added_bound4_rounds8_anchored_without_bra.csv`). Additions may be negative
again: one result adds (−1, −1) (the one-term state, round 2), two add
(0, −1) (`a b; nothing asserted`, round 1, and `a b; bra`, round 3), four add
(0, 0) (rounds 0–4), six add (0, 1) (rounds 1–5), 33 add (1, 1) (rounds
2–6). Results with the same additions appear in different rounds because of
the destroyed givens (1:§6's remark returns).

**Statements** (K7; `follows_*.csv`). Twenty-one statements tested (N3); the
two holding everywhere are proved (D6); the first failing rounds, names kept,
no `bra`: `arb` asserted 1; `a`, `b` two terms 2; something asserted 1;
nothing twice 1; at least two terms 2; both ways never 1.

**Reachability within 3 terms and 6 rounds** (K8;
`reach_bound3_rounds6_*.csv`, `summary.json` `reachability`), along the
changes among the results of 3 terms and 9 rounds:

| reading, beginning | results (names one term) | ordered pairs | reachable | unordered pairs reachable both ways | the fourth's results / pairs / reachable then / reachable now |
|---|---|---|---|---|---|
| ANCHORED, no `bra` | 649 (27) | 421 201 | 404 407 | 193 482 | 490 / 240 100 / 7 685 / 240 100 |
| ANCHORED, `bra` | 801 (11) | 641 601 | 632 911 | 311 710 | 490 / 240 100 / 7 685 / 240 100 |
| FREE, no `bra` | 187 (—) | 34 969 | 34 969 | 17 391 | 184 / 33 856 / 3 162 / 33 856 |
| FREE, `bra` | 263 (—) | 69 169 | 69 169 | 34 453 | 213 / 45 369 / 3 174 / 45 369 |

The criterion agrees with the search on every pair; the unreachable pairs
are exactly those from a result with the names one term to one with them
apart (27 × 622 = 16 794; 11 × 790 = 8 690); the fourth's 7 685 reachable
pairs (4:K8) are among the 240 100 reachable now, and no pair reachable
then is unreachable now.

**Census** (ANCHORED, 5 terms, 8 rounds, counts only): 25 212 results (1 /
74 / 2 288 / 11 698 / 11 151 by terms) without `bra`, 30 264 with it;
216 957 and 262 449 changes attempted, 55 119 and 66 376 obstructed; the
fourth's 20 654 results are the results containing what is given in both;
every check passes.

**Independent counts** (K1; `counts.csv`): all legal states with `n ≤ 5`
terms by total multiplicity `0 … 12`, under any rewriting (1, 49, 3 141,
113 840, 1 907 442 for `n = 1 … 5`) and with the names kept, by how the named
terms stand (1, 182, 27 888, 1 806 886, 47 263 030), beside the fourth's
counts of states containing what is given (4:K1, cited and computed again:
the `lost = 0` part).

**What is given** (`given.json`): the two beginnings, their 7 or 8 attempts
with the records, the two one-term builds for each obstructed `xrx`; each
beginning reaches the other, the one-term state, `arb` twice, and `a b;
nothing asserted` (cost 1 without `bra`, 2 with it), and all but the one-term
state reach it back.

**Reproducibility** (K9, K10). `python code/generate_fifth.py` rewrites every
computed file of `evidence/fifth/` (about eight minutes here); `--check`
regenerates into a temporary folder and compares byte for byte (matched);
`MANIFEST.sha256` lists every file's hash. `python code/lean_report_fifth.py`
builds all five Lean libraries and rewrites `evidence/fifth/lean_axioms.txt`
(165 theorems, every one within `propext`, `Classical.choice`, `Quot.sound`;
no `sorry`, `admit` or declared axiom in `lean4/`). After this work the
first, second, third and fourth derivations' `--check` and Lean reports were
re-run (`paper/fifth/change_log.md`, item 12). Tests: 434 passed, five
derivations; line coverage 99.88 %, branch coverage 99.20 % of all of `code/`
(`python code/xry/gate.py coverage.json`); `mypy --strict` clean; the prose
watchlist clean, with every pinned hit of this paper in §10.

## 7. What survives removal and identification

The task asks whether the results, the reachability criterion, the cost and
one-way reachability of the fourth derivation survive. In one line each,
with the Lean statements of `Fifth/Compare.lean`:

- **The results extend.** Every result of the fourth seed is a result of the
  fifth at the same round (`results_extend_A`, `_B`); the fifth has results
  the fourth has not (`results_grow`); the results are now every legal
  state with at least one term (D9), and the fourth's are exactly those with
  no destroyed given, with the same rounds and shortest sequences (computed
  on every run). So the fourth's set survives as a part, not as the whole.
- **The reachability criterion does not survive.** Containment still gives
  reachability (`contains4_reach5`) but reachability no longer gives
  containment (`criterion_fails`); the criterion is the names (D12): every
  result with the names apart reaches everything, every result with them one
  term reaches everything with them one term, and under FREE every result
  reaches every result.
- **The cost survives only on the fourth's results.** There the fewest
  changes is still the size difference (`fewest_changes5_of_contains_A`, `_B`);
  elsewhere it is the size difference plus twice the destroyed givens (D8),
  the first derivation's formula counted with multiplicities; the size can
  fall along a change (`size_can_fall`), and "every sequence has the same
  length" fails on the fourth's own results (`cost_survives_length_does_not`).
- **One-way reachability does not survive.** The two beginnings reach each
  other (`no_return_fails`), two different results are reachable from each
  other (`antisymm_fails`), every result reaches itself in two changes
  (`cycle2`), and any two results are comparable (`reach5_total`). What is
  left is the first derivation's irreversibility: the names, once one term,
  stay one term (D7).

## 8. Alternatives: kept, or eliminated by proof

| Alternative | Kept / eliminated |
|---|---|
| `bra` asserted to begin with / not | both kept: computed under both; N1, N2 |
| `bra` asserted `k ≥ 2` times, or more terms, to begin with | eliminated as starting points by D9 (results of the chosen beginning, with the same results); not computed separately |
| FREE / ANCHORED sameness | both kept: every file exists under both |
| identification: multiplicities add up / the larger of the two | the first chosen and computed; the second kept as to the record of one identification, eliminated as to results and cost (D19, R13) |
| removing the obstruction of adding `xrx` | kept as a record: coincides with refusal (C7); eliminated as a way to perform the change (R2) |
| removing the obstruction of an identification | kept: a sequence of performed changes (D5); reaches nothing new (D10) |
| readings of "build structure" | kept as to records; eliminated as to results (D10) |
| the other orders of attempts; counting an answered change as one | not computed; same results and rounds (D8), same results (D10) |
| a bound on terms alone | eliminated: the results within it are infinite (4:D9, D9) |
| every legal state within the bound, up to sameness | kept; none dropped (D14) |

Earlier results that fail under the fifth seed, each with the reason:
4:D5 (containment) — refuted, `contains_fails`; 4:D6 and 2:N8's refutation
(no count ever decreases) — refuted, N13; 4:D7 and 3:D7 (no change lowers a
multiplicity; an obstruction is never cleared) — refuted, D5, N13; 4:D8's
"size rises by exactly one", "every sequence has the same length", "cost =
size difference" — refuted, D8, `size_can_fall`, `length_not_unique`; the
cost survives on the fourth's results only; 4:D9, 3:D9, 2:D9 (results =
states containing what is given) — the set extends, D9; 4:D12, 3:D12
(reachability = containment) and 2:D12 (the carrying map) — refuted, D12,
N14; 4:D13, 3:D13 (one-way; the fewest classes never decrease) — refuted,
D13, N13; 2:D13 (`Carries.split`) — the monotonicity fails, N13; 4:D15
(with `bra` given, passing on in no result) — fails, D15; 4:D17 — survives on
`lost = 0` only, more results per round now (D17); 4:D18 (the two ANCHORED
explorations correspond round by round) — fails, D18; 4:R3, 4:R5, 4:R8,
4:R9, 4:R10, 4:R11, 4:R12, 4:R13, 4:R14 — each refuted statement now has a
witness (D2, D5, D8, D9, D13, N13); 4:N8 (comparability does not follow) —
it follows now, N12; 4:N10's clause "with equally many terms it follows" —
fails, N9; 3:C5's and 4:C5′'s "removing is not a change" — replaced by the
seed; 1:D11's `3 · 2^d` one-term builds — stays replaced by two (4:D10);
the first derivation's `Reach.costA_le`, `reach_by_edits`, `fewest_changes_A`
— survive on supports (D8), re-proved with multiplicities; 1:D2's
`givenB_to_givenA` and 1:D9's `givenA_to_oneTerm` — survive, re-proved
(D2); every K-claim of the fourth derivation — computed again as the
`lost = 0` part (§6). Everything else cited stands with the re-check given at
its citation.

## 9. Open

- O1 of the earlier papers (multiplicity) stays closed by the fourth seed.
- O2. Number of new results in rounds beyond the bound: given by the series
  and the cost formula for any round (D14, `layer_counts`); not listed.
- O3. Results beyond the declared bounds, listed: the frontier is exported
  (both parts); the census counts at 5 terms.
- O4. Other readings of "build structure": open as to records; closed as to
  results (D10).
- O5. A closed form for the number of shortest sequences reaching a result
  with three or more terms, or with the names one term: computed per result
  within the bound (K7); with two terms and no destroyed given it is
  `C(i + j, i)` (D17).
- O6. A Lean statement, on counted states, that identifying the added term
  of a build back with `x` gives the would-be outcome (4:C7's reading):
  attempted once and not closed (change log 11); checked by computation and
  on supports by the first derivation's `build_gives_back`.
- O7. A Lean statement of D8(iv) (exactly which changes raise the cost by
  one) and of the exactness of the shortest-sequence counts: proved in the
  paper and checked by computation.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Loopless directed multigraphs under vertex identification, edge
  deletion and insertion.** A counted state is a loopless multidigraph with
  two marked vertices; the four kinds are the elementary edits of graph
  edit distance with vertex contraction (identification of non-adjacent
  vertices, the elementary homomorphism) in place of vertex deletion. D9 is
  that the edit graph on marked loopless multidigraphs is connected except
  for the one-way merge of the two marks; D12 says its strong components are
  exactly two (marks apart, marks merged) under ANCHORED and one under FREE,
  and D13 that it is far from a partial order: the fourth derivation's
  sub-multigraph order (4:§9) is recovered only as the restriction to
  insertions.
- **Graph edit distance from a fixed small graph** (Sanfeliu and Fu, 1983).
  D8 is a closed form for the edit distance from the two-vertex marked
  multigraph `arb` to any marked loopless multidigraph, with insertions and
  deletions of parallel arcs at unit cost and contraction of non-adjacent
  vertices at unit cost: the size difference plus twice the destroyed marks,
  the first derivation's potential-function argument (1:§9) carried to
  multigraphs. The parity fact (D8(v)) is that every edit changes the number
  of vertices plus arcs by one.
- **Pólya enumeration with weights, by marked-pair type.** The independent
  count (D14) is the fourth's cycle-index computation with the figure series
  `1 / (1 − x)`, split as the first derivation split it by the type of the
  marked pair (the five kinds); the completeness certificate compares the
  exploration with it per cost, and the cost is a linear function of size and
  type.
- **Compositions and lattice paths.** With two vertices the results of
  round `r` are the compositions of `r + 1` into two positive-or-zero parts
  with a positive first part (the fourth's `r + 1`), plus the states with a
  destroyed mark: `2r` in all (D17); the shortest sequences to a state with
  no destroyed mark are the monotone lattice paths, `C(i + j, i)` (4:§9).
- **Irreflexive plus transitive gives asymmetric**: `passing_on_refutes_bra`,
  as before (D15).
- **Independence by two models**: N1, N2, as before.

What appears to be specific to this seed: that restoring the two kinds of
change to the counted seed brings back the first derivation's answers —
everything legal is a result, the cost is the size difference plus twice the
destroyed givens, the names' merge is the one irreversible change — with
multiplicities counted, and does so on top of the fourth's model, so that the
fourth's results, cost and rounds are recovered exactly on the states with no
destroyed given (`Fifth/Compare.lean`); that the reachability relation has
exactly two classes under one reading of sameness and one under the other
(D12, D13); that every change moves the cost by an odd amount, so no change
keeps the round (D8(v)); that a result now has `C(n, 2) + d + 1 + n²` changes
and "remove the obstruction" is a genuine answer with `M(u,v) + M(v,u) + 1`
changes (D3, D5); and that with the given terms only the seed's 100 rounds
complete with `2r` results in round `r` (D17).
