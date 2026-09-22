# Claim ledger, tenth derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/tenth/paper.md`). Lean names in namespace `Seed.Tenth` are in
`lean4/Tenth/`; names in `Seed.Ninth` are the ninth's. Axiom report:
`evidence/tenth/lean_axioms.txt`; "std" means the theorem depends on
`propext`, `Classical.choice`, `Quot.sound` only (some on a subset). No
`sorry`, `admit`, or declared axiom occurs anywhere in `lean4/` (scanned by
`code/tenth/leanreport.py`).

The column **Re-check** says how a cited earlier result was re-checked from
the tenth seed and whether it *survives leftover outcomes*: *no change*
(the statement mentions no leftover), *identity* (`NDSt` / `Step9` as
`Step10`), *computed again* (tenth exploration against the ninth's), or "—"
for a claim new to this derivation.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The ninth seed, word for word | given | `diff` of `prompt/tenth/seed_prompt.md` against `prompt/ninth/seed_prompt.md` | — | 9:G* no change | a sentence of the tenth seed that differs elsewhere |
| G15 | After every change, record what that change leaves; a leftover is not an assertion; three outcomes; declare which for every change | given | `prompt/tenth/seed_prompt.md` | — | — | a sentence making leftover an assertion or naming a fifth kind |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C-L1 | Leftover is recorded on the change; a result is a two-relation state; additions leave nothing; a removal is cleared by adding that assertion; an identification is clearable iff some one later change restores the start up to writing | chosen | `code/tenth/leftover.py` (`restores_in_one`, with `same`); Lean `leftoverOf` (some `Step9 t (rename9 π s)`) — the two agree since the review repair (change log 5) | — | — | a seed sentence putting leftover in the result |
| C-L2 | Unchosen, kept: leftover tags the result | chosen (unchosen) | `code/tenth/state.py` `Tagged`; Lean `Tagged` | — | — | — |
| C8′ | Bounds: 3 terms / 6 rounds; 3 / 5; 2 / 8; log 2 / 3; tagged 2 / 4 | chosen | `code/tenth/evidence.py` `Plan` | — | 9:C8′ lowered | — |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D3 | An addition leaves nothing | derived + computed | Lean `leftover_addTerm`, `leftover_addAssertion`, `first_change_leftover`; `given.json` | std | identity on `Step9.addTerm` / `addAssertion` | an addition whose leftover is not nothing left |
| D4 | A removal leaves a leftover cleared by adding that assertion | derived + computed | Lean `leftover_remove`, `clears_remove`, `remove_add_of_pos`; `given.json` `remove_ara_leftover` | std | identity on `Step9.remove` | a removal not restored by adding that assertion |
| D5 | A leftover of a removal in one relation is not cleared by a change of the other | derived + computed | Lean `other_rel_not_clear`; `given.json` `other_relation_clears_a_removal` false; `leftovers_*.csv` `other_relation_cleared` empty | std | — | a removal restored by adding an assertion of the other relation |
| D6 | Leftover is not a third multiplicity beside `r` and `s` | chosen (C-L1, by construction) | the state is `NDSt`, which has no field for leftover. Lean `no_third_rel` and `leftover_not_assertion` are definitional (`rfl` on `proj`; a case split on the three outcomes) and do not mention leftover as a multiplicity: they are not a proof of D6 | std | identity on `NDSt` | a seed sentence making leftover a multiplicity |
| D7 | Identifying two terms asserting nothing is restored by adding a term | derived + computed | Lean `identify_twoEmpty_restored`, `leftover_identify_twoEmpty`; `given.json` `two_term_empty_identify_leftover` | std | — | that pair of states with no one restoring change |
| D8 | An identification is restored by one later change iff one of the two terms is bare (in no assertion of either relation); so identifying two terms with an assertion between them is not | derived (paper §4) + computed | paper §4 D8 proof; `code/tenth/invariants.py` `bare_criterion`, compared with the search `restores_in_one` on every identification of every run (`identify_disagreements` empty); `given.json` `two_term_between_identify_leftover`. Not in Lean (O1) | — | — | an identification of two non-bare terms restored by one change, or of a bare term not restored |
| D9 | Under C-L1 fewest changes is the size | derived | Lean `fewest_changes10` (the ninth's `fewest_changes9`) | std | 9:D4 identity | a C-L1 result whose round is not its size |
| D10 | C-L1 results, rounds, sequences and count are the ninth's; count not a product for `n ≥ 2` | derived (identity) + computed | the C-L1 exploration *is* the ninth's (`tenth.explore.explore` wraps `ninth.explore.explore`), so `same_results`, the round and the sequence comparisons in `compare_with_ninth` agree by construction and show only determinism; the one independent check is `explored_equals_independent_count` (the ninth's orbit count, `ninth.orbits.count_results`), true in every run; 9:D10 for the non-product | — | 9:D5, 9:D10 identity / no change | an explored count different from the independent count |
| D11 | Reachability is having a term; jointly free results; exchange carries leftover of additions and removals | derived | Lean `reach10_iff`, `results_pair10`, `leftover_swap_addTerm`, `leftover_swap_remove` | std | 9:D8, 9:D5, 9:D16 identity | a pair the criterion admits with no sequence |
| D12 | Under C-L2 the one-term state is two results; the clearable tag costs 3 against size 1 | derived (two results; a route of 3) + computed (3 is the fewest) | Lean `tagged_one_nothing`, `tagged_extra` (two results), `tagged_cost_fails` (a route of 3 changes: an upper bound only, not the fewest); `tagged.json` `one_term_clearable_cost` = 3 (breadth-first, the fewest within the bound) | std | 9:D4 does not survive on tagged results | a unique tag per ninth state; a route to the clearable one-term state shorter than 3 |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | All three leftover outcomes are inhabited | computed | `given.json` `three_outcomes_inhabited`; leftovers of the 2-term 8-round run | — | — | an empty leftover class at those witnesses |
| K2 | Leftover statements about a change do not follow | computed | the 2-term 8-round run (`summary_bound2_rounds8.json`): all three outcomes inhabited (`leftovers.three_outcomes_inhabited`), so each of the three statements holds of some change and fails of some, and `leftover_statements_holding_of_every_change` is empty; `tests/test_tenth_follows.py` at 2 terms and 4 rounds | — | 9:D14 for state statements, identity | a leftover statement true of every performed change within 2 terms and 8 rounds |
| K3 | C-L2 at 2 terms and 4 rounds has more results than the ninth | computed | `tagged.json` | — | 9:K results computed again and exceeded | equal tagged and ninth counts at that bound |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| O1 | Lean of D8 | open in Lean | paper §4 D8; Python `bare_criterion` against `restores_in_one` | — | — | a Lean proof of the bare-term criterion |
| O2 | `leftoverOf s.swap t.swap = leftoverOf s t` for identifications | open in Lean | `leftover_swap_addTerm`, `_remove`; 9:D16 `Step9.swap` | — | — | a counterexample under swap |
| O3 | Results beyond the declared bounds | open as a listing | ninth frontier; 9:D11 | — | 9:O2 | — |
