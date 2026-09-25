# Claim ledger, twenty-fifth derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/twentyfifth/paper.md`). Lean names are in the namespace
`Twentyfifth` of the library `Twentyfifth` in `lean4_core/` (no outside
library; it imports the twenty-third's `Twentythird` and through it the
twenty-second's `Twentysecond`). Axiom report:
`evidence/twentyfifth/lean_axioms.txt`, `#print axioms` for every theorem of the
library and for every theorem of `Twentythird` or `Twentysecond` cited here as
imported; "p, Q" means the theorem depends on `propext` and `Quot.sound` only
(some on one or none); "—" means no Lean theorem is cited. No `sorry`, `admit`,
or declared axiom occurs in `lean4_core/` (scanned by
`code/twentyfifth/leanreport.py`, recorded in the same file), and the report
refuses any other axiom, `Classical.choice` included.

An ID written `23:…`, `22:…`, `9:…`, `7:…`, `1:…` is a claim of the twenty-third,
twenty-second, ninth, seventh or first derivation (the twenty-third is the
parent; the others are cited through it). The column **Re-check** says how a
cited earlier result was checked from this seed: *no change* (it is about the
assertions of a state or the four kinds of change, which this seed does not
touch), *imported* (a theorem of the twenty-third's or twenty-second's Lean
library used as it stands; its statement mentions nothing this seed changes,
and Lean re-checks it when this library is built), *re-proved* (proved afresh
here), *computed again* (an earlier exploration re-run beside this one and
compared). "—" in that column: the claim uses no earlier result. The column
**Falsifier** says what would refute the claim.

## Given

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| G1, G2⁗, G3″ | Terms written with letters; assertions `xry`, `xsy` with multiplicities; nothing given. | given | seed | — | — | a `diff` of the seed showing another wording |
| G6′ | Five kinds of change: identifying two terms, removing an assertion, adding a term, adding an assertion, filling three different terms; nothing else. | given | seed (the extended list) | — | — | a `diff` against the twenty-third seed showing another change |
| G7 | Identifying two terms replaces both by one term in every assertion. | given | seed | — | — | a `diff` of the seed showing another wording |
| G7a | Three filled terms balance when, going round them, as many assertions are written with `r` as with `s`; for every result, record which filled terms balance. | given | seed (the added sentence) | — | — | a `diff` against the twenty-third seed showing another change |
| G11, G13, G14 | Fewest additions first; record terms and assertions added; 100 changes per alternative, bound, frontier; any outcome valid. | given | seed | — | — | a `diff` of the seed showing another wording |
| G12″, G12a | The twenty-third's sameness sentence (writing, pairs asserted together, raising) and raising. | given | seed | — | — | a `diff` against the twenty-third seed |

## Chosen

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| C-inh | The twenty-third's readings of the assertions, letters, the four kinds, the bound, 22:C-J1, 23:C-H1, 23:C-X, 23:C-E, 23:C-R. | chosen | paper §3 | — | no change (about the assertions, the four kinds, and sentences repeated word for word); 23:C-X and 23:C-E re-checked with filled triples (D9, §6) | a sentence of the seed about these that differs from the twenty-third's |
| C-F1 | A state carries its filled triples; filling adds one; filling a filled triple is not a change. | chosen | paper §3; Lean `FSt`, `FSt.fill`, `Step25` | — | — | a sentence of the seed saying what filling does to assertions |
| C-F2 | Unchosen, kept: filling changes no state; its results are the twenty-third's at the twenty-third's rounds. | chosen (alternative) | paper §3, D16; `readings.json` | — | 23:K1 computed again (the twenty-third's results at that bound) | a C-F2 result at a round other than the twenty-third's |
| C-O1 | A filled triple keeps its way round; going round from another term is the same triple. | chosen | paper §3; Lean `Tri.norm`, `norm_rot` | p, Q | — | a sentence of the seed making filling unordered |
| C-O2, C-O3, C-O4 | Unchosen, kept and computed: a set balancing both ways / either way; every start another triple. | chosen (alternatives) | paper §3, D16; `readings.json` | — | — | a regeneration giving other figures |
| C-B1 | Going from `x` to `y` goes along `xry` and `xsy`: balance is the sum around being zero. | chosen | paper §3; Lean `around`, `Balanced` | — | — | a sentence of the seed counting assertions between two terms either way |
| C-B2 | Unchosen, kept and computed: the assertions between two terms either way; balance is the two-way sums adding up to zero. | chosen (alternative) | paper §3, D16; `readings.json` | — | — | a regeneration giving other figures |
| C-M1, C-M2 | A triple filled or not (chosen); fillings counted (unchosen, computed). | chosen | paper §3, D16 | — | — | a sentence of the seed giving fillings a multiplicity |
| C-I1 | Identifying carries the filled triples, drops those left without three different terms, merges those that become one. | chosen | paper §3; Lean `carry`, `length_carry_le`, `carry_wf` | p, Q | — | a sentence of the seed saying what identifying does to filled terms |
| C-I2, C-I3 | Unchosen: drop every triple naming either term (same results and rounds); keep the degenerate triples (cost and reachability fail). | chosen (alternatives) | paper §3, D16; `readings.json` | — | — | a C-I2 result at another round, or a C-I3 result with a filled triple reaching one with none |
| C-A | Fillings attempted with the changes adding nothing; unchosen, last: the same results and rounds. | chosen | paper §3; `readings.json` | — | — | a result at another round with fillings last |
| C-R | What is recorded: the twenty-third's record and which filled triples balance. | chosen | paper §3 | — | 23:C-R no change | — |
| C-K | The terms keeping a result from nothing: the least sets whose reading is not the result asserting nothing. | chosen | paper §3; `code/twentyfifth/told.py` | — | 23:D2 imported (one, two or three terms) | a least keeping set of four terms or more |
| C-T | Told from a result asserting nothing: the balance records compared, with the same filled triples. | chosen | paper §3; Lean `nothingWith`, `SameRecord` | — | — | — |

## Derived

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| D1 | A filled triple balances in one state of a result exactly when in every other, in every writing, going round from any of its terms; the exchange keeps which triples balance. | derived | Lean `around_rot`, `around_norm`, `Same3.around25`, `Same25.balanced_iff`, `around_rename`, `around_swap`, `balanced_swap`; computed `record_mismatch` empty | p, Q | 23:D2 imported (`Same3.around`) | two states of one result, one balancing a filled triple and the other not |
| D2 | The sameness: the twenty-third's on the assertions and the same filled triples; exactly what the clauses generate; with rewriting an equivalence, exactly what clauses and rewriting generate. | derived | Lean `Same25.refl`, `Same25.symm`, `Same25.trans`, `Gen25.same25`, `gen25_iff_same25`, `rename25_wf`, `rename25_rename`, `rename25_comp`, `Same25.rename`, `SameW25.symm`, `SameW25.trans`, `genW25_iff_sameW25` | p, Q | 23:D1 imported (`gen3_iff_same3`, `Same3.rename`, `excess_rename`) | two states joined by the clauses and rewriting that `SameW25` separates, or the converse |
| D3 | The twenty-third's record shows whether a result is the one asserting nothing, not which terms keep it from being so: `a b; ara` and `a b; arb`; the three-term trio. | derived | Lean `record_shows_whether`, `record_pair_two_terms`, `record_does_not_show_which_terms`, `fewest_wLoop`, `fewest_wPair`, `fewest_arcThree`, `cost3_of_sums3`, `cost3_of_around3`; computed `records_*.csv`, `whether_mismatch` and `keeping_mismatch` empty | p, Q | 23:D5, 23:D7 imported (`cost3_iff`, `cost3_two`, `fewest_iff`, `phi_ge_around`) | two results with the same twenty-third record and the same least keeping sets in every case, or a record of no assertion on a result not asserting nothing |
| D4 | Told exactly when a filled triple does not balance; a told result is the same as no result asserting nothing; not told: the same record as the result asserting nothing with its filled triples; in every writing and under the exchange. | derived | Lean `nothing_balanced`, `told_iff`, `told_not_nothing`, `not_told`, `sameRecord_nothing`, `SameW25.told_iff`, `told_swap`; computed `told_mismatch` empty | p, Q | 23:D2 imported (`same3_nothing_iff`) | a result with an unbalanced filled triple that is the result asserting nothing |
| D5 | Not told though not nothing: nothing filled; only loops differing (never gone along); two-way sums seen one way round; sums around off the filled triples. | derived | Lean `nothing_filled_of_lt_three`, `excess_add_loop`, `around_add_loop`, `loop_unseen`, `arb_one_way`, `two_triples_do_not_decide`; computed `summary.json` `told_or_not` | p, Q | — | a loop changing a sum around three different terms |
| D6 | Blind results: three terms, two-way sums adding up to zero; four terms, equal across each split and adding up to zero; five terms or more, loops only. | derived | Lean `Blind.balanced`, `blind_three_iff`, `blind_three_not_nothing`, `blindThree_blind`, `blind_four`, `blind_four_not_nothing`, `three_others`, `blind_twoWay_five`, `blind_five`; paper D6 (the four-term converse); computed `blind_mismatch` empty, `unseen.csv` | p, Q | 23:D2 imported (`same3_nothing_iff`) | a blind result with five terms, loops zero, not the result asserting nothing |
| D7 | Which sets of filled triples decide: rank `C(n − 1, 2)`; the triples through one term; with four terms exactly three of four; with five terms the census. | derived | Lean `cone_decides`, `two_triples_do_not_decide`; paper D7 (the rank criterion); computed `decide.csv`, `decide_mismatch` empty | p, Q | 23:D2 imported | a set of the rank that does not decide, or a non-deciding set without a witness |
| D8 | The fewest changes to a result: the twenty-third's cost of its assertions plus its filled triples; in every writing; with nothing filled the twenty-third's. | derived | Lean `Step25.psi_le`, `Reach25.psi_le`, `reach_fill_all`, `reach_build`, `Cost25.unique`, `Cost25.congr`, `cost25_eq`, `Reach25.proj`, `cost25_embed_iff`, `cost25_every_writing`, `Cost25.le_psi`; computed `round_not_cost`, `plain_mismatch` empty | p, Q | 22:D4 imported (`Step.phi_le`, `reach_plainSt`); 23:D5 imported (`cost3_iff`, `cost3_iff_min`) | an explored result whose round differs from that cost |
| D9 | A filling raises the cost by one; a change from a state asserting the fewest raises it by at most one; none returns a state to its own result; the twenty-third's parity fails; filling respects the sameness, adding a term does not. | derived | Lean `Step25.cost_le`, `Step25.not_same`, `parity_fails`, `cost_oneFilled`, `Same25.fill`, `addTerm_not_respected25`; computed `change_mismatch` empty, `how_each_kind_moves_the_cost` | p, Q | 23:D6 re-proved (parity fails; `Step.not_same3` imported for additions and removals); 23:D4 imported (`addTerm_not_respected`) | a change from a state asserting the fewest raising the cost by two, or a filling moving it by another amount |
| D10 | The twenty-third maps one to one, in every writing, each change carried to the same change; the twenty-second, ninth, seventh and first do not. | derived | Lean `embed_same_iff`, `embed_sameW_iff`, `embed_step`, `embed_reach`, `embed_wf`, `seventh_pair_merge25`, `first_pair_merge25`; computed `embed_mismatch` empty | p, Q | 23:D9 imported (`seventh_pair_merge`, `first_pair_merge`, `seventh_pair_apart`, `twentysecond_pair_apart`, `ninth_pair_apart`, `first_pair_apart`); 23:K1 computed again | two twenty-third results one here, or one twenty-third result two here |
| D11 | The map back returns the original on every mapped result, depends on the result only; every "none" costs at least four; the smallest is `a b c` with one triple filled, one result in every writing. | derived | Lean `readBack25_embed`, `readBack25_congr`, `readBack25_none_iff`, `readBack25_some`, `readBack25_none_cost`, `tri_three`, `readBack25_none_smallest`, `oneFilled_sameW_other`, `readBack25_none_smallest_writing`, `cost_oneFilled`; computed `read_back_mismatch` empty | p, Q | — | a result answered "none" costing three, or a second result answered "none" at cost four |
| D12 | No twenty-third results are merged; forgetting the filled triples is not one to one, losing them and their record. | derived | Lean `embed_same_iff`, `forget_same`, `forget_loses`; computed `twentythird_derivation` blocks | p, Q | — | two twenty-third results one here |
| D13 | Reachability: a result reaches another exactly when the other has a term or the first is empty. | derived | Lean `Step25.n_pos`, `Reach25.n_pos`, `reach25_clear`, `reach25_collapse`, `reach25_grow`, `reach25_fill_in`, `reach25_criterion`, `reach25_mutual`, `empty_never_returned25`; computed `reach_bound3_rounds5.csv`, `reach_mismatch` empty | p, Q | 23:D12 re-proved with filled triples; 22:D9 imported (`reach_grow`, `addReach_atoms`, `eq_empty_of_wf`) | a pair where the criterion and a search disagree |
| D14 | The exchange keeps the sameness, the cost, reachability and the balance record. | derived | Lean `FSt.swap_swap`, `Same25.swap`, `same25_swap_iff`, `swap25_wf`, `Step25.swap`, `Reach25.swap`, `cost25_swap`, `reach25_swap`, `told_swap`; computed `exchange_mismatch` empty | p, Q | 22:D10 imported (`excess_swap`, `swap_swap`, `swap_wf`) | a result whose exchange has another cost or another balance record |
| D15 | Counts: orbits of sets of filled triples under the stabilizer of each twenty-third result; with at most two terms the twenty-third's closed form. | derived | paper D15; computed `count_mismatch`, `two_term_mismatch` empty, `counts.csv` | — | 23:D14 computed again (its closed form, its listing of results) | an explored count differing from the independent count |
| D16 | The readings: C-F2 the twenty-third's results; C-I2 and fillings last the chosen results; C-O2, C-O3, C-O4, C-M2, C-B2 rounds at their cost; C-I3 cost and reachability fail. | derived | paper §3, D16; computed `readings.json`, `readings_mismatch` empty | — | 23:K1 computed again (C-F2) | a reading's round differing from its cost (not C-I3), or a C-I3 filled result reaching one with none |
| D17 | No tested statement holds in every result with three terms or more; some depend on the state asserting the fewest. | derived | computed `follows_*.csv` | — | 23:D17 computed again | a tested statement holding in every explored result of the five-term run |

## Computed

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| K1 | Results within the bounds: 9 573 (5 terms, 8 rounds), 29 883 (3, 10), 7 914 (2, 24); every list of `FillingCheck` empty. | computed | `summary.json` `runs`, `disagreements` | — | — | a regeneration giving other figures (`--check`) |
| K2 | Completeness within the bound; the frontier (59, 21 203, 71 875 entries). | computed | paper K2; `frontier_*.csv`; the independent count | — | — | a result within the bound missing from the grouping |
| K3 | The map back answers "none" first on `a b c` filled at `a b c`, round 4. | computed | `summary.json` `map_back` | — | — | another first result |
| K4 | The twenty-third's results are the results with nothing filled at the same rounds (4 973, 15 671, 7 914). | computed | `summary.json` `twentythird_derivation`, `embed_mismatch` empty | — | 23:K1 computed again | a mismatch |
| K5 | Records shared by results kept by sets of terms of different sizes: 55 of 90, 51 of 101, 44 of 324. | computed | `summary.json` `the_twentythird_record`, `records_*.csv` | — | 23:D8 computed again (its record) | a regeneration giving other figures |
| K6 | Told and not told, by reason (five-term run: 2 309 told, 4 967 nothing filled, 236 loops only, 61 blind, 1 961 off the filled triples, 39 nothing). | computed | `summary.json` `told_or_not` | — | — | a regeneration giving other figures |
| K7 | Reachability within 3 terms and 5 rounds: 90 results, 8 011 of 8 100 pairs. | computed | `reach_bound3_rounds5.csv` | — | 23:K7 computed again | a disagreement with search |
| K8 | The readings at 3 terms and 6 rounds: 319, 257, 291, 291, 478, 319, 328, 319, 328, 319 results. | computed | `readings.json` | — | — | a regeneration giving other figures |
| K9 | How each kind moves the cost (identifications by even amounts too). | computed | `summary.json` `changes` | — | — | a regeneration giving other figures |
| K10 | The sets of triples that decide up to five terms (34 sets with five terms, 3 of 6 of size six). | computed | `decide.csv`, `unseen.csv`, `summary.json` | — | — | a regeneration giving other figures |
| K11 | Reproducibility: `--check` matches; the Lean report within `propext`, `Quot.sound` (170 theorems of the library, 26 imported theorems cited). | computed | `MANIFEST.sha256`, `lean_axioms.txt` | p, Q | — | a mismatch |

## What does not follow, and refuted

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| N1 | The twenty-third's record does not show which terms keep a result from nothing. | derived | Lean `record_pair_two_terms`, `record_does_not_show_which_terms` | p, Q | — | a proof that equal records have equal least keeping sets |
| N2 | A result not asserting nothing need not be told. | derived | Lean `loop_unseen`, `arcThree_told` | p, Q | — | a proof that every such result has an unbalanced filled triple |
| N3 | Filling both ways round does not see every two-way sum. | derived | Lean `blind_three_not_nothing`, `blind_four_not_nothing` | p, Q | — | a three-term blind result with a two-way sum proved nothing |
| N4 | One way round does not tell what the other does. | derived | Lean `arb_one_way` | p, Q | — | a proof that the two sums around are equal |
| N5 | Two triples through one term do not decide. | derived | Lean `two_triples_do_not_decide` | p, Q | — | a proof that they do |
| N6 | Not every change changes the cost by an odd number. | derived | Lean `parity_fails` | p, Q | 23:D6 re-proved (fails here) | a proof of the parity with filled triples |
| N7 | The map back need not answer. | derived | Lean `readBack25_oneFilled` | p, Q | — | an answer for a result with a filled triple |
| N8 | Forgetting the filled triples is not one to one. | derived | Lean `forget_loses` | p, Q | — | a proof that it is |
| N9 | Reachability need not hold under every reading (C-I3). | derived | paper D16; computed `readings.json` | — | — | a C-I3 filled result reaching one with none |
| N10 | Nothing about the asserting or the filling holds in every result. | computed | `follows_*.csv` | — | — | a statement true of every explored result |
| R1 | A told result that is the result asserting nothing. | refuted | Lean `told_not_nothing` | p, Q | — | such a result |
| R2 | A filled triple balancing in one state of a result and not another. | refuted | Lean `Same25.balanced_iff` | p, Q | — | such a pair |
| R3 | Fewer changes to a result than the twenty-third's cost plus its filled triples. | refuted | Lean `cost25_eq` | p, Q | 23:R3 re-proved with filled triples | a shorter sequence |
| R4 | A change from a state asserting the fewest raising the cost by more than one, or returning a state to its own result. | refuted | Lean `Step25.cost_le`, `Step25.not_same` | p, Q | 23:R4 re-proved | such a change |
| R5 | A blind result with five terms or more, loops zero, not the result asserting nothing. | refuted | Lean `blind_five` | p, Q | — | such a result |
| R6 | A result answered "none" costing fewer than four. | refuted | Lean `readBack25_none_cost` | p, Q | — | such a result |
| R7 | Two twenty-third results made one here. | refuted | Lean `embed_same_iff` | p, Q | — | such a pair |

## Earlier results used

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| 23:C-inh, 23:C-H1, 23:C-X, 23:C-E, 23:C-R | The twenty-third's readings of the assertions, raising, changes of results, exploration and record. | chosen (cited) | `paper/twentythird/paper.md` §3 | — | no change; 23:C-X and 23:C-E re-checked with filled triples (D9, §6) | a sentence of the seed about these differing from the twenty-third's |
| 23:D1 | The twenty-third's sameness: excesses differing by `g(x) − g(y)`, in every writing. | derived (cited) | this D2 | p, Q | imported | as D2 |
| 23:D2 | Loops, two-way sums and sums around three terms kept by the sameness and deciding the result asserting nothing. | derived (cited) | this D1, D3–D7 | p, Q | imported | as D1 |
| 23:D4 | Adding a term does not respect the sameness. | derived (cited) | this D9 | p, Q | imported (`addTerm_not_respected`) | a proof that adding a term respects it |
| 23:D5 | The cost of a result's assertions. | derived (cited) | this D8 | p, Q | imported (`cost3_iff`, `cost3_iff_min`, `cost3_two`, `phi_ge_around`) | as D8 |
| 23:D6 | Parity of the cost; changes from states asserting the fewest; no change returns a state. | derived (cited) | this D9 | p, Q | re-proved: parity fails; the other two re-proved with filled triples | as D9 |
| 23:D7 | States asserting the fewest (`Fewest`, `fewest_iff`). | derived (cited) | this D3 | p, Q | imported | a state satisfying `fewest_iff` not asserting the fewest |
| 23:D8 | What the twenty-third records. | derived (cited) | this D3 | — | computed again (`records_*.csv`) | as D3 |
| 23:D9 | The seventh's and the first's pairs apart there and merged in the twenty-third. | derived (cited) | this D10 | p, Q | imported | as D10 |
| 23:D12 | Reachability. | derived (cited) | this D13 | p, Q | re-proved with filled triples | as D13 |
| 23:D13 | The exchange. | derived (cited) | this D14 | p, Q | re-proved with filled triples; 22:D10 imported | as D14 |
| 23:D14 | Counts, the two-term closed form. | derived (cited) | this D15 | — | computed again | as D15 |
| 23:D17, 23:K1, 23:K7 | Statements; the twenty-third's exploration; reachability. | derived / computed (cited) | this D17, K4, K7 | — | computed again | a mismatch |
| 22:D4, 22:D9, 22:D10 | `phi` rises by at most one; the addition path; reachability paths; the exchange on states. | derived (cited) | this D8, D13, D14 | p, Q | imported | as D8, D13, D14 |

## Open

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| O1 | A closed form of the cost of the assertions with four or more terms. | open | 23:O1; computed by descent | — | 23:O1 no change | a closed form checked against the computed costs would close it |
| O2 | Lean statements of the rank criterion in general, the four-term blind converse, the counts, and the readings. | open | proved in the paper, checked by computation | — | — | Lean proofs would close it |
| O3 | Which sets of filled triples decide with six terms or more, in words other than the rank. | open | computed up to five terms | — | — | a description checked against the rank would close it |
| O4 | Whether some map from the twenty-second's, ninth's, seventh's or first's states, carrying each change to some change, is one to one. | open | 23:O4 | — | 23:O4 no change | such a map, or a proof that none exists |
| O5 | A closed form for the number of shortest sequences to a result with filled triples. | open | computed per result (`results_*.csv`) | — | — | a closed form checked against the files would close it |
