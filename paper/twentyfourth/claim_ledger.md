# Claim ledger, twenty-fourth derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/twentyfourth/paper.md`). Lean names are in the namespace
`Twentyfourth` of the library `Twentyfourth` in `lean4_core/` (no outside
library; it imports the twenty-third's `Twentythird` and through it the
twenty-second's `Twentysecond`). Axiom report:
`evidence/twentyfourth/lean_axioms.txt`, `#print axioms` for every theorem of
the library and for every earlier theorem named here; "p, Q" means the theorem
depends on `propext` and `Quot.sound` only (some on one or none); "—" means no
Lean theorem is cited. No `sorry`, `admit`, or declared axiom occurs in
`lean4_core/` (scanned by `code/twentyfourth/leanreport.py`, recorded in the
same file), and the report refuses any other axiom, `Classical.choice` included.

An ID written `23:…`, `22:…`, `9:…`, `7:…`, `1:…` is a claim of the
twenty-third, twenty-second, ninth, seventh or first derivation (the
twenty-third is the parent; the others are cited through it). The column
**Re-check** says how a cited earlier result was checked from this seed: *no
change* (it is about the assertions or the four earlier kinds of change, which
this seed does not touch), *imported* (a theorem of the twenty-third's or
twenty-second's Lean library used as it stands; its statement mentions nothing
this seed changes, and Lean re-checks it when this library is built),
*re-proved* (proved afresh here), *computed again* (an earlier exploration
re-run beside this one and compared). "—" in that column: the claim uses no
earlier result. The column **Falsifier** says what would refute the claim.

## Given

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| G1, G2⁗, G3″ | Terms written with letters; assertions `xry`, `xsy` with multiplicities; nothing given. | given | seed | — | — | a `diff` of the seed showing another wording |
| G6′ | A change is exactly one of five kinds, the fifth filling one term; nothing else is a change. | given | seed (the changed sentence) | — | — | a `diff` against the twenty-third seed showing another change |
| G7 | Identifying two terms replaces both by one term in every assertion. | given | seed | — | — | a `diff` of the seed showing another wording |
| G7a | A filled term `x` balances when `xrx` and `xsx` are asserted equally often; for every result, record which filled terms balance. | given | seed (the added sentence) | — | — | a `diff` against the twenty-third seed showing another change |
| G11, G13, G14 | Fewest additions first; record terms and assertions added; 100 changes per alternative, bound, frontier; any outcome valid. | given | seed | — | — | a `diff` of the seed showing another wording |
| G12″, G12a | The sameness sentence (writing, pairs asserted together, raising) and what raising is. | given | seed | — | — | a `diff` against the twenty-third seed showing another wording |

## Chosen

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| C-inh | The twenty-third's readings of the assertions, letters, the four earlier kinds and merged multiplicities, raising (C-H1), pairs asserted together (C-J1), a change of a result (C-X), the exploration (C-E) and its record (C-R). | chosen | paper §3 | — | no change (about the assertions, the four earlier kinds, and clauses repeated word for word) | a sentence of the seed about those that differs from the twenty-third's |
| C-F1 | Filling `x` makes `x` filled and changes nothing asserted; filling a filled term is not a change. | chosen | paper §3; `FSt.fill`, `Step24` | — | — | a sentence of the seed saying what filling adds or removes |
| C-F1′ | Filling a filled term as a change with its start as outcome. | chosen (unchosen reading, eliminated) | paper §3: it reaches no state C-F1 does not | — | — | a result reached under C-F1′ and not under C-F1 |
| C-F2 | A term filled a number of times (kept, computed). | chosen (unchosen reading, kept) | `readings.json`: 233 results against 175, every round the counted cost | — | — | a C-F2 result whose round is not the twenty-third's cost plus its fillings |
| C-F3 | Filling also asserts `xrx` and `xsx` once each (eliminated). | chosen (unchosen reading, eliminated by proof) | `fillLoops_same`; `readings.json` | p, Q | — | a C-F3 outcome that is not C-F1's result |
| C-F4 | Filling adds the missing loops until the term balances (kept, computed). | chosen (unchosen reading, kept) | paper §3; `readings.json`: C-F1's results and rounds | — | — | a C-F4 result or round differing from C-F1's |
| C-S | A rewriting carries the filled terms; pairs asserted together and raising touch none; results differing in their filled terms are two results. Set aside: filled terms off the result. | chosen | paper §3 (G7a's "for every result") | — | — | a clause of the seed joining results that differ in their filled terms |
| C-I1 | The one term of an identification is filled when either was. | chosen | paper §3; `idF` | — | — | a sentence of the seed on filled terms under identification |
| C-I2, C-I3 | Filled only when both were; never filled (kept, computed). | chosen (unchosen readings, kept) | `readings.json`: the same results and rounds; 41 and 46 of 113 identifications reach another result; D11 | — | — | a C-I2 or C-I3 result or round differing from C-I1's |
| C-B | The record: for every filled term, at the result's least writing, whether it balances, and the two counts. | chosen | paper §3; `results_*.csv` | — | — | two states of one result recording differently (refuted by D2) |
| C-N | A result with nothing asserted on as many terms keeps the filled terms. | chosen | paper §3; `nothingOf` | — | — | a reading of the task's words fixing the filled terms otherwise |
| C-N0 | Nothing asserted and nothing filled (kept, answered). | chosen (unchosen reading, kept) | paper §3, D4; `readings.json`: 115 of 175 | — | — | — |
| C-K | The terms keeping a result from being the one asserting nothing: the smallest sets on which it is not (a loop, two terms, three terms). | chosen | paper §3; `keeping_size`, `keeping_terms` in `code/twentyfourth/state.py` | — | 23:D2 (no change) | a smaller set keeping a result, not of these kinds (refuted by 23:D2) |
| C-O | Fillings with the changes that add nothing: identifications, removals, fillings, a term, additions. | chosen | paper §3 | — | — | a result whose round depends on the order within a round |
| C-E′ | The ninth's states with filled terms, grouped (computed). | chosen (unchosen reading, kept) | `readings.json`: the same 175 results, 482 states against 340 | — | — | a result or round differing from C-E's |

## Derived

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| D1 | `Same24` (the twenty-third's `Same3` and the same filled terms) is an equivalence keeping the terms, the filled count and whether a term is filled; the clauses generate exactly the classes of the mark. | derived; computed | `Same24.refl`, `Same24.symm`, `Same24.trans`, `Same24.fc`, `Same24.hasFilled`, `Same24.sameW24`; `summary.json` (`generated_sameness`: 6 and 29 classes) | p, Q | 23:D1 imported (`gen3_iff_same3`) | two states joined by the clauses with different marks, or the converse |
| D2 | A filled term balances exactly when its loop's excess is zero; this is the same in every state of a result and in every writing. | derived; computed | `balances_iff`, `Same24.balances`, `SameW24.pointwise`, `SameW24.balances`; `balance_mismatch` empty | p, Q | 23:D2 imported (`Same3.loop`); rewriting of the excess imported (`excess_rename`) | two states of one result, one balancing at a filled term and the other not |
| D3a | The twenty-third's record counts no assertion exactly for the result asserting nothing on its terms. | derived; computed | `record_whether`, `cost3_nothing`; `record_question_mismatch` empty | p, Q | 23:D5 imported (`cost3_iff`) | a result costing its number of terms that is not the one asserting nothing |
| D3b | The twenty-third's record does not show which terms keep a result from being the one asserting nothing: `a b; ara` / `a b; arb` and `a b c; ara asb` / `a b c; arb bsa` record the same and are kept by one term / two, one / three. | derived; computed | `record23_does_not_show_which`, `record23_does_not_show_which_three`, `fewest_loopA`, `fewest_arbA`, `fewest_loopAsb`, `fewest_arcThree`; `given.json`: 17 of 37 records | p, Q | 23:D2, 23:D5 imported (`arcThree_not_nothing`, `phi_ge_around`); 23:D8 no change | the two states of a pair recording differently, or not asserting the fewest |
| D4 | The record of `X` differs from that of the result asserting nothing on its terms, the same filled, exactly when some filled term's loop has non-zero excess; such a result is not the one asserting nothing; told is a mark of the result in every writing. | derived; computed | `told_iff`, `nothing_balances`, `balRec_nothing`, `told_not_nothing`, `Same24.told`, `SameW24.told`, `same24_nothing_iff`; `tell_mismatch` empty | p, Q | 23:D2 imported (`same3_nothing_iff`) | a result told apart with every filled loop zero, or not told with one non-zero |
| D5 | Every result neither the one asserting nothing nor told is one filling away, or of the two-term kind, or of the three-term kind; in the last two no filling tells. | derived; computed | `not_told_cases`, `told_after_fill`, `never_told_of_loops_zero`, `awayOne_not_told`, `awayOne_fill_told`, `twoWayFilled_not_nothing`, `twoWayFilled_never_told`, `aroundFilled_never_told`, `toldOne_told`; `summary.json` classes | p, Q | 23:D2 imported (`same3_nothing_iff`, `arcThree_not_nothing`) | a result of the two- or three-term kind told after some filling |
| D6 | Identifying two terms puts the two loops and the two-way sum on the one loop; it can make a result told, and it can merge a three-term witness away. | derived | `identify_tells`; paper D6 | p, Q | — | an identification whose merged loop differs from that sum |
| D7 | Filling respects the sameness; adding a term does not. | derived; computed | `Same24.fill`; `respect_mismatch` empty | p, Q | 23:D4 imported (`addTerm_not_respected`) through `same24_ofSt_iff` | a filling of two states of one result reaching two results |
| D8 | The cost of a result is the twenty-third's cost of its assertions plus its filled terms, `n + |F| + min_g Σ|e + g(x) − g(y)|`, in every writing; a shortest sequence adds terms, adds assertions and fills. | derived; computed | `cost24_eq`, `Step24.pot_le`, `Reach24.pot_le`, `reach24_upper`, `reach24_fillUpTo`, `fc_fill`, `fc_identify_le`, `rsum_image_le`, `Cost24.unique`, `Cost24.congr`, `cost24_ofSt`, `fill_cost`, `cost24_every_writing`, `fc_rename`, `pot_rename`, `shortest24`, `Step24.size24_step`, `Reach24.raising`; `round_not_cost` empty | p, Q | 22:D4 imported (`reach_plainSt`, `Step.phi_le`, `Step.phi_identify`); 23:D5 imported (`cost3_iff`) | a result reached in fewer changes, or a round differing from the formula |
| D9a | A change from a state asserting the fewest raises the cost by at most one; no change returns a state to its own result. | derived; computed | `Step24.cost_le`, `cost24_le_pot`, `Step24.not_same24`; `change_mismatch` empty | p, Q | 23:D6 imported (`Same3.size_parity`) | a change from such a state raising the cost by two, or a change returning to its own result |
| D9b | Identifying two filled terms moves the cost by an even number (`a b` both filled: 4 to 2); under C-I1 every other change moves it by an odd number. | derived; computed | `identify_two_filled_even`, `pairFilled_wf`, `cost24_oneFilled`; `change_mismatch` empty; `summary.json` moves | p, Q | 23:D6 re-proved (fails here) | an even move of another change, or an odd move of such an identification |
| D10 | A one-term result has one shortest sequence unfilled and `t + 1` filled. | derived (paper); computed | paper D10; `sequences_mismatch` empty | — | 22:D12 computed again (fails for filled terms) | a one-term count differing |
| D11a | Under C-I1 a filled term never goes away. | derived | `Step24.hasFilled`, `Reach24.hasFilled`, `idF_of`, `idF_iff` | p, Q | — | a sequence from a state with a filled term to one without |
| D11b | A result reaches another exactly when the other has a term or the first is empty, and the other has a filled term or the first has none. | derived; computed | `reach24_criterion`, `Reach24.forget`, `reach24_clear`, `reach24_collapse`, `reach24_grow`, `reach24_atoms`, `reach24_fillFrom`, `reach24_from_one`, `idF_move`, `glue_move`, `reach24_mutual`; `reach_mismatch` empty (1 034 of 1 369) | p, Q | 22:D9 imported (`Reach.n_pos`) | a pair where the criterion and a search along the changes disagree |
| D11c | The twenty-third's criterion fails exactly on the pairs from a result with a filled term to one without. | derived; computed | `twentythird_criterion_fails`; `reach_bound2_rounds4.csv` (299 = 13 × 23) | p, Q | 23:D12 re-proved (fails under C-I1) | a result with a filled term reaching one without |
| D11d | Under C-I2 and C-I3 a filled term can go away and the twenty-third's criterion holds. | derived (paper; witness in Lean); computed | `i2_unfills`; paper D11; `reach_mismatch` empty (1 333 of 1 369) | p, Q | 23:D12 computed again | a pair where the twenty-third's criterion fails under C-I2 or C-I3 |
| D12 | The exchange keeps the sameness, balance, told, the cost and reachability, and carries each change to one of the same kind. | derived; computed | `same24_swap_iff`, `Same24.swap`, `balances_swap`, `told_swap`, `cost24_swap`, `reach24_swap`, `Step24.swap`, `Reach24.swap`, `FSt.swap_swap`; `exchange_mismatch` empty | p, Q | 22:D10 imported (`excess_swap`, `swap_swap`) | an exchanged result at another round, or with another balance record |
| D13 | The twenty-third maps in one to one, each change carried to a change of the same kind; no two of its results are made one here, so the merge loses nothing. | derived; computed | `same24_ofSt_iff`, `sameW24_ofSt_iff`, `Step.toStep24`, `Reach.toReach24`, `idF_false`, `no_merge`, `ofSt_wf`, `ofSt_fc`; `twentythird_mismatch` empty | p, Q | 23:D1 imported; the twenty-third's exploration computed again (1 164, 6 450, 2 182 results) | two twenty-third results one here, or a change without its image |
| D13a | The twenty-second's, ninth's, seventh's and first's witnesses of 23:D9 merge here as there. | derived | `seventh_pair_merge24` | p, Q | 23:D9 imported (`seventh_pair_merge`) | the seventh pair two results here |
| D14a | The map back returns the original on mapped results, answers "none" exactly with a filled term, and depends on the result only. | derived; computed | `readBack_ofSt`, `readBack_none_iff`, `readBack_some`, `readBack_congr`, `anyFilled_iff`; `read_back_mismatch` empty | p, Q | — | a mapped result answered otherwise |
| D14b | Every result answered "none" costs at least two; the smallest is `a` filled, nothing asserted, at cost two, the only one there. | derived; computed | `readBack_none_cost`, `fc_pos`, `smallest_none`, `smallest_none_unique`; first "none" at round 2 in every run | p, Q | — | a result answered "none" at cost one, or another at cost two |
| D14c | The forgetting map answers every result, carries each change to a change or to none, and merges results differing only in their filled terms. | derived; computed | `Step24.forget`, `forget_merges`; `forget_mismatch` empty | p, Q | — | a change whose forgotten outcome is no twenty-third change |
| D15 | The counts: two-term closed forms `2t² + t + 1`, `4t² + 2`, `2t² + t + 1`; per round `8r² − 46r + 78` from `r = 4`; 2 482 245 within 100 rounds. | derived (paper); computed | `counts.csv`, `summary.json`; `count_mismatch`, `two_term_mismatch` empty | — | 23:D14 re-proved (with filled terms) | an explored count differing from the independent one |
| D16 | The unchosen readings: C-F2 other results; C-F3, C-F4, C-I2, C-I3, C-E′ C-F1's results and rounds. | derived; computed | `fillLoops_same`; `readings.json`; `readings_mismatch` empty | p, Q | — | a reading's results or rounds differing as stated |
| D17 | No statement about the asserting or the filling holds in every explored result; 21, 21, 16 depend on the state. | computed | `follows_*.csv` | — | 23:D17 computed again | a statement holding in every result |

## Computed

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| K1 | Results within 5 terms and 7 rounds, 3 and 9, 2 and 16: 2 052, 15 467, 6 905, every round its cost. | computed | `results_*.csv`, `rounds_*.csv`, `summary.json` | — | — | a regeneration differing (`--check`) |
| K2 | Completeness within the bound: every result with at most `N` terms and cost at most `R` is formed at its cost; the frontier is the attempts adding a term at `N` terms. | derived; computed | paper K2; `shortest24`; `frontier_*.csv` | p, Q | — | a result within the bound missing from the run |
| K3 | The map back's first "none" is `a` filled at round 2 in every run. | computed | `summary.json` | — | — | another first "none" |
| K4 | The twenty-third's exploration at the same bounds equals the results here with no filled term. | computed | `summary.json` (`twentythird`) | — | 23:K1 computed again | a missing or extra result |
| K5 | 17 of the 37 records of the twenty-third's results within three terms and six rounds hold results kept by different numbers of terms. | computed | `given.json` | — | 23 exploration computed again | another count |
| K6 | Statement verdicts. | computed | `follows_*.csv` | — | 23:K6 computed again | — |
| K7 | Reachability within two terms and four rounds under each reading of identifying. | computed | `reach_bound2_rounds4.csv`, `summary.json` | — | — | a pair differing from the search |
| K8 | The readings within two terms and six rounds. | computed | `readings.json` | — | — | — |
| K9 | How each kind of change moves the cost. | computed | `summary.json` | — | — | an even move other than identifying two filled terms |

## Refuted

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| R1 | A told result that is the one asserting nothing. | refuted | `told_not_nothing` | p, Q | 23:D2 imported | such a result |
| R2 | A told result with every loop zero, whatever is filled. | refuted | `never_told_of_loops_zero` | p, Q | — | such a result |
| R3 | Fewer changes to a result than the twenty-third's cost plus its filled terms. | refuted | `cost24_eq` | p, Q | 23:D5 imported | a shorter sequence |
| R4 | A change from a state asserting the fewest raising the cost by more than one; a change returning a state to its own result. | refuted | `Step24.cost_le`, `Step24.not_same24` | p, Q | 23:D6 imported | such a change |
| R5 | Under C-I1, a sequence from a state with a filled term to one without. | refuted | `Reach24.hasFilled` | p, Q | — | such a sequence |
| R6 | A result answered "none" costing less than two. | refuted | `readBack_none_cost` | p, Q | — | such a result |
| R7 | Two twenty-third results made one here. | refuted | `no_merge` | p, Q | 23:D1 imported | such a pair |

## Open

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| O1 | A closed form of the cost with four or more terms. | open | 23:O1 | — | no change (the filled terms add their number) | — |
| O2 | Lean statements of the counts, of the C-I2 and C-I3 criteria beyond `i2_unfills`, of C-F4's results. | open (proved in the paper, computed) | paper D11, D15, §3 | — | — | — |
| O3 | A closed form of the number of shortest sequences with two or more terms. | open | `results_*.csv` | — | — | — |
| O4 | Whether some map from an earlier seed other than the twenty-third, carrying each change to some change, is one to one. | open | 23:O4 | — | no change | — |
