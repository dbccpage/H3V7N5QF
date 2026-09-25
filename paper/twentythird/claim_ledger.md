# Claim ledger, twenty-third derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/twentythird/paper.md`). Lean names are in the namespace
`Twentythird` of the library `Twentythird` in `lean4_core/` (no outside
library; it imports the twenty-second's `Twentysecond`). Axiom report:
`evidence/twentythird/lean_axioms.txt`, `#print axioms` for every theorem of the
library; "p, Q" means the theorem depends on `propext` and `Quot.sound` only
(some on one or none); "—" means no Lean theorem is cited. No `sorry`, `admit`,
or declared axiom occurs in `lean4_core/` (scanned by
`code/twentythird/leanreport.py`, recorded in the same file), and the report
refuses any other axiom, `Classical.choice` included.

An ID written `22:…`, `9:…`, `8:…`, `7:…`, `1:…` is a claim of the
twenty-second, ninth, eighth, seventh or first derivation (the twenty-second is
the parent; the others are cited through it). The column **Re-check** says how
a cited earlier result was checked from this seed: *no change* (it is about
states or changes, which this seed does not touch), *imported* (a theorem of
the twenty-second's Lean library used as it stands; its statement mentions
nothing this seed changes, and Lean re-checks it when this library is built),
*re-proved* (proved afresh here), *computed again* (an earlier exploration
re-run beside this one and compared). "—" in that column: the claim uses no
earlier result. The column **Falsifier** says what would refute the claim.

## Given

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| G1, G2⁗, G3″ | Terms written with letters; assertions `xry`, `xsy` with multiplicities; nothing given. | given | seed | — | — | a `diff` of the seed showing another wording |
| G6, G7 | The four kinds of change; identifying replaces both terms in every assertion. | given | seed | — | — | a `diff` of the seed showing another wording |
| G11, G13, G14 | Fewest additions first; record terms and assertions added; 100 changes per alternative, bound, frontier; any outcome valid. | given | seed | — | — | a `diff` of the seed showing another wording |
| G12″ | Two results differing only in how their terms are written, only by an `xry` and an `xsy` asserted together, or only by raising terms, are the same result. | given | seed (the extended sentence) | — | — | a `diff` against the twenty-second seed showing another change |
| G12a | Raising a term `x` adds `xry` and `ysx` once for every other term `y`. | given | seed (the added sentence) | — | — | a `diff` against the twenty-second seed showing another change |

## Chosen

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| C-inh | The twenty-second's readings of state, letters, changes, order of attempts, bound on terms and rounds, and C-J1 (22:C-inh, 22:C-J1). | chosen | paper §3 | — | no change (about states, changes, and a clause repeated word for word) | a sentence of the seed about states or changes that differs from the twenty-second's |
| C-H1 | Raising as the seed says; "differ only by raising terms": terms raised any number of times each; the sameness is the equivalence the three clauses generate. | chosen | paper §3 | — | — | a sentence of the seed restricting how often a term is raised |
| C-H2 | Unchosen, kept: raising every term at once; its results are the twenty-second's. | chosen (alternative) | paper §3, D16; Lean `raise_all_gen`; `readings.json` | p, Q | — | a proof that raising every term at once is not pairs asserted together (refuted by `raise_all_gen`) |
| C-H3 | Unchosen, eliminated: each term raised at most once generates C-H1's sameness. | refuted (as a different reading) | paper §3 (transitivity) | — | — | a pair of states one result under C-H1 and two under C-H3 |
| C-J2, C-J3 | The twenty-second's unchosen readings, with raising: C-J2's results unchanged; C-J3 computed. | chosen (alternatives) | paper D16; `readings.json` | — | 22:D15 computed again with raising | a C-J3 round differing from its cost, or raising changing the C-J2 mark |
| C-X | A change of a result is a change performed on one of its states. | chosen | paper §3, D4 | — | re-proved: 22:C-X's independence of the state fails here (D4) | — |
| C-E | The twenty-second's exploration of states run as it stands, results formed afterwards; the round of a result is the first round one of its states is reached (unchosen C-E′: the ninth's states). | chosen | paper §3, §6; `summary.json` | — | 22:D13 imported (its exploration); C-E′ computed again | a result formed at a round other than its cost |
| C-R | What is recorded for a result: terms, and assertions in `r` and in `s` of a state asserting the fewest. | chosen | paper §3, D8 | — | — | two states asserting the fewest of one result with different splits (refuted by D8) |

## Derived

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| D1 | Raising moves the excess by `[u = x] − [v = x]`; the sameness the three clauses generate is: equally many terms and excesses differing by `g(x) − g(y)` (writing included: after one rewriting). | derived | Lean `excess_raise`, `excess_raiseTo_all`, `gen3_iff_same3`, `Same3.symm`, `Same3.trans`, `excess_rename`, `Same3.rename`, `SameW3.symm`, `SameW3.trans`, `genW3_iff_sameW3`; computed `generated_sameness` (234 states), `sameness_mismatch` empty | p, Q | 22:D1 imported (same excess ⇒ joined by pairs) | two states joined by the clauses whose excesses do not differ by some `g(x) − g(y)`, or the converse |
| D2 | A state is the result asserting nothing on its terms exactly when its loops, two-way sums and sums around three terms are zero; every other result carries a non-zero such sum, kept by the sameness; three terms can be needed. | derived | Lean `Same3.loop`, `Same3.twoWay`, `Same3.around`, `same3_nothing_iff`, `sameW3_nothing_iff`, `raisedPair_nothing`, `arcThree_not_nothing`; computed `nothing_mismatch` empty | p, Q | — | a state with all those sums zero that is not the result asserting nothing, or two states of one result with different sums |
| D3 | In the twenty-second a state is the result asserting nothing exactly when its excess is zero everywhere: some states asserting something are, no result whose plain state asserts something is. | derived | Lean `same22_nothing_iff`, `state_asserting_something_is_nothing22`, `raisedPair_not_nothing22` | p, Q | 22:D1 imported | a twenty-second result with a non-zero excess joined to the one asserting nothing |
| D4 | Adding or removing an assertion respects the sameness; adding a term does only with one term; identifying does only with at most three terms; the twenty-second's 22:D2 fails here. | derived | Lean `addTerm_not_respected`, `step_of_same3_fails`; paper D4; computed `respect_mismatch` empty, `given.json` | p, Q | 22:D2 re-proved (it fails for adding a term and for identifying); imported for removals (removing `xqy` is adding the other relation) | two states of one result with at most three terms whose identification of the same terms gives two results |
| D5 | The cost is `n + min_g Σ |e(x, y) + g(x) − g(y)|`, in every writing; two-term closed form; three-term closed form; the loops and two-way sums do not fix it; raising sets of terms while the count falls reaches it. | derived | Lean `cost3_iff`, `phi_eq_sum`, `cost3_iff_min`, `cost3_every_writing`, `cost3_two`, `phi_ge_around`, `cost3_three_ge`, `loops_and_two_way_do_not_fix_the_cost`; paper D5(b), D5(c); computed `round_not_cost`, `closed_form_mismatch` empty | p, Q | 22:D4 imported (fewest changes to a state is its plain `phi`) | an explored result whose round differs from the cost by descent, or a search over `g` finding fewer |
| D6 | Every change changes the cost by an odd number; none returns a state to its own result; from a state asserting the fewest the cost rises by at most one; adding a term to another state can raise it by `2k + 1`. | derived | Lean `Gen3.size_parity`, `Same3.size_parity`, `Cost3.parity`, `Step.cost3_odd`, `Step.not_same3`, `Step.cost3_le`, `adding_a_term_raises_the_cost`; computed `change_mismatch` empty, `how_each_kind_moves_the_cost` | p, Q | 22:D4, 22:D6 imported (the size moves by one per change); 22:D6 "a change from the plain state raises the cost by at most one" re-proved only from states asserting the fewest | a change moving the cost by an even number, or raising it by more than one from a state asserting the fewest |
| D7 | A state asserts the fewest exactly when it asserts no pair in both relations and raising no set of terms lowers its count; with two terms, no `xry` with `ysx`; single terms suffice up to three terms and not with four. | derived | Lean `Fewest.plain`, `fewest_iff`, `fewest_two_iff`, `four_single_terms_do_not_find_the_fewest`; paper D5(c), D7; computed `fewest_mismatch`, `characterization_mismatch` empty | p, Q | — | a state satisfying the criterion that does not assert the fewest, or the converse |
| D8 | What is recorded is the same on every state asserting the fewest. | derived | paper D8; computed `record_mismatch` empty | — | — | two such states of one result with different splits between `r` and `s` |
| D9 | None of the seventh, ninth, twenty-second or first maps its states one to one; any map carrying additions to the same additions merges the seventh pair. | derived | Lean `seventh_pair_apart`, `seventh_pair_merge`, `twentysecond_pair_apart`, `ninth_pair_apart`, `first_pair_states`, `first_pair_apart`, `first_pair_merge`, `carried_additions_merge3`; computed `seventh_derivation` blocks, `seventh_mismatch` empty | p, Q | 22:D8 imported (the seventh's one-to-one map into the twenty-second, `ofR`); 7:D5 computed again; 1:C4, 8:C4 no change | a rewriting making the pair one seventh or first state, or the pair two results here |
| D10 | The map back to the twenty-second's results answers at most one result up to writing; returns the original exactly on the sole states asserting the fewest; answers "none" on `a b; arb arb`; answers on every result costing at most three; the smallest "none" results cost four. | derived | Lean `ReadBack3.functional`, `ReadBack3.congr`, `readBack3_self_iff`, `readBack3_answer_cost`, `readBack3_arb`, `readBack3_raisedPair`, `readBack3_none`, `readBack3_some_of_cost_le_three`, `two_single`; computed `read_back_mismatch` empty, `map_back` blocks | p, Q | 22:D1 imported (the twenty-second's sameness in every writing) | a result of cost at most three with two states asserting the fewest that are two twenty-second results |
| D11 | A merge loses the excess beyond the kept sums, the twenty-second's plain state and cost; it keeps the sums, `Σ e`, the parity, the cost, the record. | derived | Lean `merge_loses3`; computed `twentysecond_derivation` blocks | p, Q | 22:K1 computed again | a merge keeping the twenty-second's cost |
| D12 | A result reaches another exactly when the other has a term or the first is empty, from any state of it. | derived | Lean `reach3_criterion`, `reach3_of_same3`, `reach3_mutual`; computed `reach_bound3_rounds4.csv`, `reach_mismatch` empty | p, Q | 22:D9 imported (the criterion for its sameness) | a pair where the criterion and a search disagree |
| D13 | The exchange of the relations keeps the sameness, the cost and reachability. | derived | Lean `Same3.swap`, `same3_swap_iff`, `cost3_swap`, `reach3_swap`; computed `exchange_mismatch` empty | p, Q | 22:D10 imported (the exchange negates the excess and carries changes) | a result whose exchange has another cost |
| D14 | Two-term results recording `t` assertions: `2t² + t + 1`; round counts `[r = 0] + [r ≥ 1]·one(r − 1) + [r ≥ 2]·two(r − 2)`; three-term counts from the invariants; 642 248 results with at most two terms within 100 rounds. | derived | paper D14; computed `count_mismatch`, `two_term_mismatch` empty, `counts.csv` | — | 22:D11 re-proved (new counts; the twenty-second's do not hold here) | an explored or listed count differing from the formula |
| D15 | On two terms, `xry` then `ysx` gives back the result before both. | derived | Lean `two_additions_undo3` | p, Q | 22:D5 re-proved (extended: two different pairs undo here) | two terms where those two additions change the result |
| D16 | C-H2's results are the twenty-second's; C-J2 with raising keeps its mark; C-J3 with raising computed. | derived | Lean `raise_all_gen`; paper D16; computed `readings.json`, `readings_mismatch` empty | p, Q | 22:D15 computed again | a C-J3 round differing from its cost |
| D17 | No tested statement holds in every result; some depend on the state asserting the fewest taken. | derived | computed `follows_*.csv`, `statements_holding_in_every_result` empty | — | 22:D16 computed again (read on every state asserting the fewest) | a tested statement holding in every explored result |

## Computed

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| K1 | Results within the bounds: 4 973 (5 terms, 8 rounds), 15 671 (3, 10), 7 914 (2, 24); every list of `RaisingCheck` empty. | computed | `summary.json` `runs`, `disagreements` | — | — | a regeneration giving other figures (`--check`) |
| K2 | Completeness within the bound; the frontier is the twenty-second's (40, 12 761, 71 875 entries). | computed | paper K2; `frontier_*.csv` | — | 22:D13 imported | a result within the bound missing from the grouping |
| K3 | The map back answers "none" on 1 071, 8 133, 7 306 results; first `a b; bsa bsb`, round 4. | computed | `summary.json` `map_back` | — | — | another first result |
| K4 | C-E′: the ninth's states grouped give the same results at the same rounds (4 973, 6 450, 860 within its rounds). | computed | `summary.json` `ninth_derivation`, `ninth_mismatch` empty | — | 9:K1 computed again | a mismatch |
| K5 | The twenty-second's results merge: up to 7, 12, 22 in one result. | computed | `summary.json` `twentysecond_derivation` | — | 22:K1 computed again | a regeneration giving other figures |
| K6 | 45 statements read on every state asserting the fewest: none in every result; 21 depend on the state (5-term run). | computed | `follows_*.csv` | — | 22:K6 computed again | a regeneration in which a statement holds in every result |
| K7 | Reachability within 3 terms and 4 rounds: 29 results, 813 of 841 pairs. | computed | `reach_bound3_rounds4.csv` | — | 22:K7 computed again | a disagreement with search |
| K8 | The readings at 2 terms and 8 rounds: C-H1 226, C-H2 673, C-J3 with raising 419. | computed | `readings.json` | — | — | a regeneration giving other figures |
| K9 | Reproducibility: `--check` matches; the Lean report within `propext`, `Quot.sound`. | computed | `MANIFEST.sha256`, `lean_axioms.txt` | p, Q | — | a mismatch |

## What does not follow, and refuted

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| N1 | The twenty-second's excess, plain state and cost are not kept by the sameness. | derived | Lean `merge_loses3` | p, Q | — | a proof that the twenty-second's cost is a function of the result here |
| N2 | Loops and two-way sums do not show every result other than the one asserting nothing. | derived | Lean `arcThree_not_nothing` | p, Q | — | a proof that loops and two-way sums suffice with three terms |
| N3 | A change of a result need not have one outcome as a result. | derived | Lean `addTerm_not_respected`, `step_of_same3_fails` | p, Q | — | a proof that adding a term respects the sameness |
| N4 | One change can raise the cost by more than one. | derived | Lean `adding_a_term_raises_the_cost` | p, Q | — | a bound on the rise independent of the state |
| N5 | Loops and two-way sums do not fix the cost. | derived | Lean `loops_and_two_way_do_not_fix_the_cost` | p, Q | — | a formula for the cost from loops and two-way sums alone |
| N6 | Raising single terms does not always find the fewest. | derived | Lean `four_single_terms_do_not_find_the_fewest` | p, Q | — | a proof that single terms suffice with four terms |
| N7 | A result need not have one state asserting the fewest. | derived | Lean `readBack3_none` | p, Q | — | a proof that every result has one |
| N8 | No earlier seed maps in one to one (as D9). | derived | as D9 | p, Q | — | as D9 |
| N9 | The map back need not return the original on a mapped state. | derived | Lean `readBack3_raisedPair` | p, Q | — | a proof that it always returns the original |
| N10 | Nothing about the asserting follows; some statements depend on the state. | computed | `follows_*.csv` | — | — | a statement true of every explored result |
| R1 | A result other than the one asserting nothing with all loops, two-way sums and sums around zero. | refuted | Lean `same3_nothing_iff` | p, Q | — | such a result |
| R2 | A change keeping the parity of the cost, or returning a state to its own result. | refuted | Lean `Step.cost3_odd`, `Step.not_same3` | p, Q | 22:R5 re-proved | such a change |
| R3 | Fewer changes to a result than its cost. | refuted | Lean `cost3_iff_min` | p, Q | 22:R3 re-proved for this seed | a shorter sequence |
| R4 | A change from a state asserting the fewest raising the cost by more than one. | refuted | Lean `Step.cost3_le` | p, Q | — | such a change |
| R5 | A state asserting the fewest that asserts a pair in both relations. | refuted | Lean `Fewest.plain` | p, Q | — | such a state |
| R6 | A result costing at most three answered "none". | refuted | Lean `readBack3_some_of_cost_le_three` | p, Q | — | such a result |
| R7 | The pairs of D9 kept apart here. | refuted | Lean `seventh_pair_merge`, `first_pair_merge` | p, Q | — | a sum kept by the sameness that differs between them |

## Earlier results used

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| 22:C-inh, 22:C-J1 | The twenty-second's readings of states, changes and "asserted together". | chosen (cited) | `paper/twentysecond/paper.md` §3 | — | no change | a sentence of the seed about these differing from the twenty-second's |
| 22:D1 | Same excess at a fixed writing ⇔ joined by pairs asserted together; the full sameness in every writing. | derived (cited) | this D1, D3, D10 | p, Q | imported | as D1 |
| 22:D2 | A change of any state of a result has the outcome of a change of any other. | derived (cited) | this D4 | p, Q | re-proved (fails here for adding a term and identifying); imported for removals | a proof that adding a term respects this seed's sameness |
| 22:D4 | The fewest changes to a state is its plain `phi`; the size moves by one per change. | derived (cited) | this D5, D6 | p, Q | imported | a state reached in fewer changes than its plain `phi` |
| 22:D5 | Undoing at a fixed writing only by one pair in the two relations. | derived (cited) | this D15 | — | re-proved (extended: other pairs undo here) | two additions of different pairs on two terms that do not undo each other |
| 22:D8 | The seventh's states map one to one into the twenty-second's results (`ofR`). | derived (cited) | this D9 | p, Q | imported | a rewriting making two seventh results one twenty-second result |
| 22:D9 | Reachability: a term decides. | derived (cited) | this D12 | p, Q | imported | as D12 |
| 22:D10 | The exchange negates the excess, carries changes. | derived (cited) | this D13 | p, Q | imported | as D13 |
| 22:D11, 22:D12 | The twenty-second's counts; one shortest sequence per one-term result. | derived (cited) | this D14 | — | 22:D11 re-proved (its counts do not hold here); 22:D12 no change (one term: raising adds nothing) | as D14 |
| 22:D13 | The twenty-second's exploration: complete within its bound, its frontier. | derived (cited) | this K2 | — | imported (run as it stands) | a twenty-second result within the bound missing from its exploration |
| 22:D15, 22:D16 | The unchosen readings; statements. | derived (cited) | this D16, D17 | — | computed again | as D16, D17 |
| 9:K1 | The ninth's exploration of every state. | computed (cited) | this K4 | — | computed again | a mismatch in K4 |
| 7:D5 | The seventh's results. | derived (cited) | this D9 | — | computed again | a mismatch in `seventh_derivation` |
| 1:C4, 8:C4 | The first's and eighth's sameness keep the names. | chosen (cited) | this D9 | — | no change | a rewriting of a first or eighth state moving its names onto one term |

## Open

| ID | Statement | Status | Evidence | Axiom report | Re-check | Falsifier |
|---|---|---|---|---|---|---|
| O1 | A closed form of the cost with four or more terms; whether the best closed-walk bound equals it. | open | computed by descent (D5(c)) | — | — | a closed form checked against the computed costs, or a proof of the equality, would close it |
| O2 | Lean statements of the set criterion, the three-term closed form, which changes respect the sameness, and the counts. | open | proved in the paper, checked by computation | — | — | Lean proofs would close it |
| O3 | A closed form of the shortest-sequence counts with two or more terms. | open | computed per result | — | — | a closed form checked against `results_*.csv` would close it |
| O4 | Whether some map carrying each change of an earlier seed to some change here is one to one. | open | D9 refutes maps carrying additions to the same additions | — | — | such a map, or a proof that none exists |
