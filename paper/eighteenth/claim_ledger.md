# Claim ledger, eighteenth derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**.
"std" means the cited theorem depends only on `propext`, `Classical.choice`
and `Quot.sound` (`evidence/eighteenth/lean_axioms.txt`).

The column **Re-check** says whether a base result used the sentence that
two writings are one result.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1 | The base seed, with the sameness sentence reworded to "different results" | given | `prompt/eighteenth/seed_prompt.md` | — | 1:G12 reworded | another sentence differing |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C1 | A result is a legal state as written. Both base beginnings are kept. Bound: 3 terms, 12 rounds | chosen | `explore_written`; `summary.json` | — | 1:C4 not applied | a seed sentence that still identifies two writings |
| C2 | Every rewriting is a result, reached or not, is computed and not used as the exploration. On that reading the count grows with every letter, so no finite supply bounds it | chosen; the growth derived + computed | `letter_supply`; `sample_letter_supply_grows`; section 4 | — | — | a sentence that every unreached writing has been obtained |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D1 | `n!` splits into writings times permutations that fix the state, on every reached state. (That two results are the same exactly when the written states are equal is C1, by construction: `same_written` is equality, checked against the written key of every reached pair, `writings_called_the_same`.) | computed | `orbit_splits_factorial` on every reached state (`orbit_formula_fails` empty on all four runs) | — | 1:G12 reworded | a reached state whose writings do not split `n!` |
| D2 | The writing with `bra` and the names exchanged is not what is given, and not the beginning that asserts `bra` with the names unmoved | derived | Lean `given_ne_bra`, `swapped_ne_given`, `swapped_ne_bra`; Python `rewrite` by `(1, 0)` is that writing | std | the base's unformalised rewriting (`Paths.lean`) | one of those three states equal to another |
| D3 | With the names kept, the round equals the base count of changes for that writing, and so is the fewest changes with no bound on terms | computed + derived | `summary.json` `rounds_above_the_base_cost` = 0 and `rounds_below_the_base_cost` empty on both named runs; base Lean `fewest_changes_lower_A`, `fewest_changes_lower_B` | std | 1:D8 does not use the sameness sentence: the count reads the size and the destroyed givens, the same for every writing | a named result whose round differs from `xry.cost.cost` |
| D4 | Without the names, the base count is a lower bound on the round, strict on 32 and 29 results, by at most 2 and 4 | computed | `summary.json` `rounds_below_the_base_cost` empty, `rounds_above_the_base_cost`, `greatest_excess_over_the_base_cost` | — | 1: the free count is the least over writings | a writing reached in fewer changes than that least count |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | Named closures coincide for the two beginnings: 137 results, 109 base classes, 28 classes in two writings, 128 frontier attempts | computed | `summary.json` | — | computed again against `xry.explore` | a regeneration with other totals |
| K2 | Nameless closures coincide: 69 results, 20 base classes, 15 split, 64 frontier attempts. Answer writings are all reached | computed | `summary.json` `answers_on_an_unreached_writing` = 0 | — | — | an answer whose writing is outside the closure after round 12 |
| K3 | Evidence regenerates byte for byte | computed | `python code/run_eighteenth.py --check` | — | — | `--check` reporting a difference |

## Refuted

| ID | Statement refuted | Status | Evidence | Axioms | Re-check | What would falsify the refutation |
|---|---|---|---|---|---|---|
| R1 | Two writings of one base result are one result | refuted | D2, K1, K2 | std | 1:G12 | the 28 named classes, or the 15 nameless classes, each reached once |
| R2 | The changes reach a last result with no bound on terms | refuted | the frontier is non-empty; adding a term is never obstructed (base `addTerm_legal`) | — | 1: no change to the changes | a state on which adding a term is obstructed |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would close it |
|---|---|---|---|---|---|---|
| O1 | A closed form for 137 and 69 | open | K1, K2 | — | — | a formula checked against the runs |
| O2 | Without the names: a return from four terms cannot be shorter than the recorded round. (With the names: closed by D3.) | open | section 6 | — | — | a proof, or a shorter witness |
