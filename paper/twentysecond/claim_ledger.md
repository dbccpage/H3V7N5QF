# Claim ledger, twenty-second derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/twentysecond/paper.md`). Lean names are in the namespace
`Twentysecond` of `lean4_core/` (library `Twentysecond`, no outside library).
Axiom report: `evidence/twentysecond/lean_axioms.txt`, `#print axioms` for every
theorem of the library; "p, Q" means the theorem depends on `propext` and
`Quot.sound` only (some on one or none); "—" means no Lean theorem is cited. No
`sorry`, `admit`, or declared axiom occurs in `lean4_core/` (scanned by
`code/twentysecond/leanreport.py`, recorded in the same file), and the report
refuses any other axiom, `Classical.choice` included.

An ID written `9:…`, `8:…`, `7:…`, `1:…` is a claim of the ninth, eighth,
seventh or first derivation (the ninth is the parent; the others are cited
through it). The column **Re-check** says how a cited earlier result was
checked from this seed: *no change* (it is about states or changes, which the
changed sentence does not touch), *re-proved* (proved afresh in `lean4_core/` or
in the paper for this seed's results), *computed again* (the earlier
exploration re-run beside this one and compared). "—" in that column: the claim
uses no earlier result. The column **Falsifier** says what would refute the
claim.

## Given

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| G1 | Terms are written with letters. | given | seed | — | — | a `diff` of the seed showing another wording |
| G2⁗ | An assertion is `xry` or `xsy`, asserted a number of times; adding raises, removing lowers its multiplicity by one. | given | seed | — | — | a `diff` of the seed showing another wording |
| G3″ | Nothing is given: no terms, nothing asserted. | given | seed | — | — | a `diff` of the seed showing another wording |
| G6, G7 | The four kinds of change; identifying replaces both terms by one in every assertion. | given | seed | — | — | a `diff` of the seed showing another wording |
| G11 | Attempt every change, fewest additions first; record for every result the terms and assertions it adds to what is given. | given | seed | — | — | a `diff` of the seed showing another wording |
| G12′ | Two results differing only in how their terms are written, or only by an `xry` and an `xsy` asserted together, are the same result. | given | seed (the one changed sentence) | — | — | a `diff` against the ninth seed showing a second changed sentence, or none |
| G13, G14 | 100 changes per alternative; bound, frontier, completeness; any outcome is valid. | given | seed | — | — | a `diff` of the seed showing another wording |

## Chosen

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| C-inh | The ninth's readings of state, letters, changes, order of attempts, bound on terms and rounds (9:C1′, C3, C5⁗, C6, C8′, C9). | chosen | paper §3 | — | no change (about states and changes) | a sentence of the seed about states or changes that differs from the ninth's |
| C-J1 | "Differ only by an `xry` and an `xsy` asserted together": one more `xry` and `xsy` on one pair (`x = y` allowed); sameness is the equivalence generated with rewriting. | chosen | paper §3 | — | — | a sentence of the seed naming two pairs, or excluding `x = y` |
| C-J2 | Unchosen, kept: the letters as placeholders (any `xry` with any `usv`). | chosen (alternative) | paper D15; `readings.json` | — | — | a proof that C-J2 gives the results of C-J1 (refuted by the 29 against 673 results of `readings.json`) |
| C-J3 | Unchosen, kept: only `x ≠ y`. | chosen (alternative) | paper D15; `readings.json` | — | — | a proof that C-J3 gives the results of C-J1 (refuted by the 1 081 against 673 results of `readings.json`) |
| C-X | A change of a result is a change of any state of it (unchosen C-X′: of its plain state only). | chosen | paper §3, D2 | — | — | a change of one state of a result whose outcome no change of another state reaches (refuted by `step_of_same`) |
| C-R | What is recorded for a result is read on its plain state: terms, assertions in `r`, in `s`. | chosen | paper §3 | — | — | a record of a result differing between two of its writings (refuted by `recorded_same`) |

## Derived

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| D1 | Two states are one result exactly when they have equally many terms and, after one rewriting, the same excess `M_r − M_s` at every ordered pair; the generated sameness is exactly this; each result has one plain state up to writing. | derived | Lean `gen_iff_same`, `same_iff_excess`, `genW_iff_sameW`, `count_plain`, `plain_reduced`, `plain_rename`, `SameW.symm`, `SameW.trans`; computed `generated_sameness` (1 242 states, 247 classes) | p, Q | — | two states with the same excess function (up to rewriting) not joined by the sentence's steps, or joined states with different excesses |
| D2 | A change of any state of a result has the outcome of a change of any other state of it; removing `xry` is the result of adding `xsy`; so a result's changes are its plain state's (`C(n, 2) + d + 1 + 2n²`). | derived | Lean `step_of_same`, `reach_of_same`, `same_remove_add_partner`, `Same.identify`, `Same.remove`; computed `removal_outside` empty, `attempts_equal_formula` | p, Q | 9:D3 computed again on the plain state | a removal from a state that is not plain whose result is no outcome of the plain state's changes |
| D3 | The first change adds a term; the empty result is never returned to. | derived | Lean `first_change_adds_term`, `Step.n_pos`, `Reach.n_pos`, `empty_never_returned` | p, Q | 9:D1, 9:D2 re-proved | a sequence from a result with a term to the empty result |
| D4 | The fewest changes to a result is `n + Σ |excess|` (the plain state's size); the ninth's size of a state exceeds it by the atoms of its pairs asserted together; a shortest sequence is additions only through plain states. | derived | Lean `fewest_changes`, `fewest_changes_every_writing`, `Step.phi_le`, `Reach.phi_le`, `reach_plainSt`, `size_eq_phi_add_together`, `shortest_additions`, `shortest_prefix`, `shortest_all_plain`, `phi_ofR`; computed `round_not_cost` empty | p, Q | 9:D4 re-proved (holds on plain states only); 7:D4 re-proved (`phi_ofR`) | a result reached in fewer changes, or an explored result whose round differs from the formula |
| D5 | In the ninth no addition undoes an earlier addition, in any writing; here `xry` then `xsy` returns to the start's result; at a fixed writing two additions in a row return exactly when they are one pair in the two relations; with a rewriting other pairs can. | derived | Lean `ninth_additions_never_return`, `ninth_additions_never_return_every_writing`, `addition_undoes_addition`, `addition_undoes_not_in_ninth`, `same_add_add_iff`, `two_additions_return_iff`; computed `undo_failed` empty, `given.json` | p, Q | 9:D4 (size moves by one per addition) re-proved (`AddReach.size`) | a ninth addition run returning to its start; a pair `xry`, `xsy` not returning here |
| D6 | What is recorded moves: term `(+1, 0)`; addition `−1` iff the result asserts the pair in the other relation, else `+1`; removal `−1` iff the result asserts it, else `+1`; identification `(−1, −2c)`, any `c`; so the cost changes by an odd number and no change keeps a result or its round. | derived | Lean `record_addTerm`, `record_add`, `record_remove`, `record_identify`, `identify_takes`, `recorded_same`, `recorded_sum`, `Step.phi_parity`, `Step.not_same`, `ninth_record_add`; computed `record_move_mismatch` empty, `how_each_kind_moves_what_is_recorded` | p, Q | 9:D4(v) (no change keeps the round) re-proved by parity; 9:D4(i) (moves by one) refuted for identifications | a change whose recorded move differs from the rule |
| D7 | The ninth's results asserting no pair in both relations stay pairwise different here, in every writing; every ninth result is one result here with exactly one of them; a merge loses exactly the pairs asserted together (`min(M_r, M_s)` at each pair). | derived | Lean `same_plainSt`, `together_plain`, `plain_states_stay_apart`, `plain_states_stay_apart_every_writing`, `state_of_result_and_together`, `count_together`, `merge_loses`; computed `ninth_derivation` blocks | p, Q | 9:K1 computed again | two plain ninth states that are one result here |
| D8 | The ninth's states do not map one to one, nor under any map carrying additions; the seventh's do (`ofR`, changes carried, one to one in every writing); the map back returns the original, answers exactly the images, and answers "none" first on the one-term result asserting `asa` once (cost 2, the smallest); the eighth's and the first's states do not map one to one. | derived | Lean `ninth_not_one_to_one`, `carried_additions_merge`, `Step7.embed`, `Reach7.embed`, `plain_ofR`, `ofR_same_iff`, `ofR_sameW_iff`, `readBack_ofR`, `same_ofR_of_readBack`, `readBack_same`, `readBack_none_rename`, `readBack_asa`, `readBack_none_phi`, `readBack_none_smallest`, `phi_asa`; computed `seventh_derivation`, `given.json` (eighth witness); paper (first) | p, Q | 7:D5 (the seventh's results) computed again; 8:C4, 1:C4 no change (names kept by their sameness) | two seventh results that are one result here; a result answered "none" costing under two, or costing two other than `a; asa` |
| D9 | A result reaches another exactly when the other has a term or the first is empty; results with a term reach each other both ways. | derived | Lean `reach_criterion`, `reach_mutual`, `reach_clear`, `reach_collapse`, `reach_grow`; computed `reach_bound3_rounds4.csv` | p, Q | 9:D8, 9:D9 re-proved | a pair of results where the criterion and a search disagree |
| D10 | The exchange of the relations negates every excess and is a symmetry of results, cost and reachability. | derived | Lean `excess_swap`, `plain_swap`, `same_swap_iff`, `phi_swap`, `Step.swap`, `swap_wf`; computed `exchange_mismatch` empty | p, Q | 9:D16 re-proved | a result whose exchange is not a result at the same round |
| D11 | Each cycle of pairs of a rewriting contributes `(1 + x^L)/(1 − x^L)`; with at most two terms the results of round `r` are `[r = 0] + [r ≥ 1]·one(r − 1) + [r ≥ 2]·two(r − 2)`, `two(t) = 4t(t² + 2)/3 + [t even]·t`; 31 391 855 within 100 rounds. | derived | paper D11; computed `count_mismatch`, `two_term_mismatch` empty, `counts.csv`; tests against a listing | — | 9:D10, 9:D11 refuted as counts of this seed (new forms) | an explored round count or a listed count differing from the formula |
| D12 | A one-term result has one shortest sequence. | derived | paper D12 (from D4); computed `one_term_not_one_sequence` empty | — | 9:D11 (`C(p + q, p)`) refuted here; 7:D11 re-proved | a one-term result with two shortest sequences |
| D13 | Within the bound the exploration is complete, the frontier exact, the shortest-sequence counts exact. | derived | paper D13; computed `count_mismatch` empty, `frontier_entries_are_1_per_state_with_N_terms` | — | 9:D10 re-proved | a result within the bound missing from the exploration |
| D14 | Under the unchosen "larger of the two" identification: same results, cost and reachability; an identification's outcome as a result depends on the state taken. | derived | paper D14 | — | 9:D15 re-proved (survives in results, cost, reachability) | a result whose cost differs under the larger reading |
| D15 | C-J2: a result is `(n, Σ M_r − Σ M_s)`, cost `n + |D|`; C-J3: cost the reduced size, a count by cycles; under C-J3 with C-X, round 3 is infinite. | derived | paper D15; computed `readings.json`, `readings_mismatch` empty | — | — | a C-J2 or C-J3 round differing from its formula; a C-J3 padded identification not giving a new result |
| D16 | No tested statement about the asserting holds in every result; "some pair asserted in both relations" holds in none, by construction of the plain state. | derived | computed `follows_*.csv`, `statements_holding_in_every_result` empty | — | 9:D14 computed again | a tested statement holding in every explored result |

## Computed

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| K1 | Results within the bounds: 7 168 (5 terms, 8 rounds), 39 526 (3, 10), 86 201 (2, 24); every check of `JointCheck` empty. | computed | `summary.json` `runs`, `disagreements` | — | — | a regeneration giving other figures (`--check`) |
| K2 | The seventh's results at the same bounds are the results whose plain state asserts nothing with `s` (799, 2 232, 7 539), same rounds and sequence counts. | computed | `summary.json` `seventh_derivation`, `seventh_mismatch` empty | — | 7:K1, 7:K2, 7:K7 computed again | a mismatch |
| K3 | The map back answers "none" on 6 369, 37 294, 78 662 results; first `a; asa`, round 2. | computed | `summary.json` | — | — | another first result |
| K4 | The ninth's 10 416 / 25 965 / 22 021 results merge into 7 168 / 13 912 / 4 235 results here, one plain ninth result each; up to 55 / 55 / 70 ninth results in one. | computed | `summary.json` `ninth_derivation`, `ninth_mismatch` empty | — | 9:K1, 9:K2 computed again | a mismatch |
| K5 | Shortest-sequence counts per result; one per one-term result. | computed | `results_*.csv` | — | — | a regeneration giving other counts (`--check`) |
| K6 | 42 statements read on the plain state: none in every result, one in none. | computed | `follows_*.csv` | — | 9:K7 computed again | a regeneration in which a tested statement holds in every explored result |
| K7 | Reachability within 3 terms and 4 rounds: 36 results, 1 261 of 1 296 pairs reachable, the rest into the empty state. | computed | `reach_bound3_rounds4.csv`, `summary.json` | — | 9:K8 computed again | a disagreement with search |
| K8 | The unchosen readings at 2 terms and 8 rounds. | computed | `readings.json` | — | — | a regeneration giving other figures (`--check`) |
| K9 | Reproducibility: `--check` matches; the Lean report within `propext`, `Quot.sound`. | computed | `MANIFEST.sha256`, `lean_axioms.txt` | p, Q | — | a mismatch |

## What does not follow, and refuted

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| N1 | The ninth's size, totals, parts are not kept by the sameness (witness `a`, `a; ara asa`). | derived | Lean `merge_loses` | p, Q | — | a proof that the ninth's size is a function of the result (refuted by `merge_loses`) |
| N2 | An addition need not raise what is recorded (`a; ara` + `asa`), nor lower it (`a` + `ara`). | derived | Lean `record_add`; `given.json` | p, Q | — | a proof that additions always raise, or always lower, what is recorded |
| N3 | A removal need not lower what is recorded. | derived | Lean `record_remove` | p, Q | — | a proof that removals always lower what is recorded |
| N4 | An identification's loss has no fixed bound. | derived | Lean `identify_takes` | p, Q | — | a bound on the assertions one identification takes out (refuted by `identify_takes`) |
| N5 | Two additions that undo need not be one pair, up to rewriting. | derived | `given.json` | — | — | a proof that two additions returning to their start are always one pair (refuted by `given.json`) |
| N6 | The cost need not move by exactly one per change. | derived | Lean `record_identify`, `identify_takes` | p, Q | 9:D4(i) refuted here | a proof that every change moves the cost by exactly one |
| N7 | A result's plain `r` and `s` parts are not free of each other. | derived | Lean `plain_reduced` | p, Q | 9:D5 (jointly free parts) refuted for results | two plain states asserting one pair in both relations |
| N8 | Results with equally many terms need not have equally many changes. | derived | paper N8; `results_*.csv` | — | — | a formula for the changes of a result from its terms alone |
| N9 | A result need not have one shortest sequence. | computed | `results_*.csv` | — | — | a proof that every result has one shortest sequence |
| N10 | Nothing about the asserting follows (D16). | computed | `follows_*.csv` | — | — | a statement about the asserting true of every excess function |
| N11 | The seventh's states do not cover the results. | derived | Lean `readBack_asa` | p, Q | — | a result with an `s` assertion in its plain state answered by the map back |
| R1 | A change other than adding a term on the empty state. | refuted | Lean `first_change_adds_term` | p, Q | 9:R1 re-proved | a change of the empty state other than adding a term |
| R2 | A sequence from a result with a term to the empty result. | refuted | Lean `empty_never_returned` | p, Q | 9:R2 re-proved | a sequence from a result with a term to the empty result |
| R3 | Fewer changes to a result than `n + Σ |excess|`. | refuted | Lean `fewest_changes` | p, Q | — | a sequence to a result shorter than its cost |
| R4 | A shortest sequence with a removal, an identification, or a state asserting a pair in both relations. | refuted | Lean `shortest_additions`, `shortest_all_plain` | p, Q | 9:R6 re-proved | a shortest sequence with a removal, an identification or a state asserting a pair in both relations |
| R5 | A change keeping a result's round, or returning a result to itself. | refuted | Lean `Step.phi_parity`, `Step.not_same` | p, Q | 9:R5 re-proved | a change whose outcome is the result it started from, or of the same round |
| R6 | A non-empty run of ninth additions returning to its start's ninth result. | refuted | Lean `ninth_additions_never_return_every_writing` | p, Q | — | a non-empty run of additions ending at a ninth state of the start's size |
| R7 | Two plain ninth results that are one result here. | refuted | Lean `plain_states_stay_apart_every_writing` | p, Q | — | two plain ninth states, not the same ninth state, with one result here |
| R8 | Two seventh results that are one result here. | refuted | Lean `ofR_sameW_iff` | p, Q | — | two different seventh results with one result here |
| R9 | A result answered "none" costing under two, or costing two and other than `a; asa`. | refuted | Lean `readBack_none_phi`, `readBack_none_smallest` | p, Q | — | a result answered "none" of cost 0 or 1, or of cost 2 other than `a; asa` |

## Earlier results used

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| 9:C1′…C9 | The ninth's readings of states and changes. | chosen (cited) | `paper/ninth/paper.md` §3 | — | no change | a sentence of the seed about states or changes differing from the ninth's |
| 9:D1, 9:D2 | The first change adds a term; the empty state is never returned to. | derived (cited) | this D3 | p, Q | re-proved | as R1, R2 |
| 9:D3 | `C(n, 2) + d + 1 + 2n²` changes. | derived (cited) | this D2 | — | computed again (on the plain state) | an explored result whose attempts differ from the count on its plain state |
| 9:D4 | Fewest changes = size. | derived (cited) | this D4 | p, Q | re-proved: holds on plain states only | a plain state whose size is not its fewest changes |
| 9:D5 | Everything well formed is a result; jointly free parts. | derived (cited) | this D1, N7 | p, Q | re-proved: every state is reached; parts not free as results | a well-formed state not reached from the empty state |
| 9:D8, 9:D9 | Reachability: a term decides; mutual among results with a term. | derived (cited) | this D9 | p, Q | re-proved | as D9 |
| 9:D10, 9:D11 | Completeness; the count; the two-term closed form; one-term binomial. | derived (cited) | this D11–D13 | — | re-proved (completeness); refuted as counts of this seed | as D11, D13 |
| 9:D12 | One sameness, no names. | derived (cited) | this §3 | — | no change | a name in the seed |
| 9:D14 | Nothing about the asserting holds in every result. | derived (cited) | this D16 | — | computed again | as D16 |
| 9:D15 | The unchosen identification reading changes nothing computed. | derived (cited) | this D14 | — | re-proved | as D14 |
| 9:D16 | The exchange is a symmetry. | derived (cited) | this D10 | p, Q | re-proved | as D10 |
| 9:D17 | The relations interact through the terms alone. | derived (cited) | this D6, N7 | p, Q | refuted for results (re-proved false) | a proof that an assertion of one relation never changes a result's plain part in the other |
| 7:D4 | The seventh's cost is its size. | derived (cited) | Lean `phi_ofR` | p, Q | re-proved | a seventh state whose embedded result costs other than its size |
| 7:D11 | A one-term result has one shortest sequence. | derived (cited) | this D12 | — | re-proved | as D12 |
| 8:C4, 1:C4 | The eighth's and first's sameness keep the names. | chosen (cited) | this D8 | — | no change | a rewriting of an eighth or first state that moves its names onto one term |

## Open

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| O1 | A closed form for the shortest-sequence counts with two or more terms. | open | computed per result (K5) | — | — | a closed form checked against the computed counts would close it |
| O2 | Results beyond the bounds, listed. | open | counted by formula (D11) | — | — | a listing beyond the bounds would close it |
| O3 | Lean statements of D11–D15 and of the first seed's witness. | open | proved in the paper, checked by computation | — | — | Lean proofs of these statements would close it |
