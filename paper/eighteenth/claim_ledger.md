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
| C2 | Every rewriting is a result, reached or not, is computed and not used as the exploration | chosen | `letter_supply`; section 4 | — | — | a sentence that every unreached writing has been obtained |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D1 | Two results are the same exactly when the written states are equal. `n!` splits into writings times permutations that fix the state | derived + computed | `same_written`; `orbit_splits_factorial` on every reached state; Lean `swapped_ne_given` | std | 1:G12 reworded | a reached state whose writings do not split `n!` |
| D2 | The writing with `bra` and the names exchanged is not what is given, and not the beginning that asserts `bra` with the names unmoved | derived | Lean `given_ne_bra`, `swapped_ne_given`, `swapped_ne_bra`; Python `rewrite` by `(1, 0)` is that writing | std | the base's unformalised rewriting (`Paths.lean`) | one of those three states equal to another |
| D3 | With the names kept, the round equals the base count of changes for that writing | computed | `summary.json` `rounds_off_the_base_cost` = 0 on both named runs | — | 1:D8 does not use the sameness sentence | a named result whose round differs from `xry.cost.cost` |
| D4 | Without the names, the base count is a lower bound on the round, strict on 32 and 29 results | computed | `summary.json`; the excesses are at most 2 and 4 | — | 1: the free count is the least over writings | a writing reached in fewer changes than that least count |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | Named closures coincide for the two beginnings: 137 results, 109 base classes, 28 classes in two writings, 128 frontier attempts | computed | `summary.json` | — | computed again against `xry.explore` | a regeneration with other totals |
| K2 | Nameless closures coincide: 69 results, 20 base classes, 15 split, 64 frontier attempts. Answer writings are all reached | computed | `summary.json` `answers_on_an_unreached_writing` = 0 | — | — | an answer whose writing is outside the closure after round 12 |
| K3 | Evidence regenerates byte for byte | computed | `python code/run_eighteenth.py --check` | — | — | `--check` reporting a difference |

## Refuted

| ID | Statement refuted | Status | Evidence | Axioms | Re-check | What would falsify the refutation |
|---|---|---|---|---|---|---|
| R1 | Two writings of one base result are one result | refuted | D1, K1, K2 | std | 1:G12 | the 28 named classes, or the 15 nameless classes, each reached once |
| R2 | The changes reach a last result with no bound on terms | refuted | the frontier is non-empty; adding a term is never obstructed (base `addTerm_legal`) | — | 1: no change to the changes | a state on which adding a term is obstructed |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would close it |
|---|---|---|---|---|---|---|
| O1 | A closed form for 137 and 69 | open | K1, K2 | — | — | a formula checked against the runs |
| O2 | A return from four terms cannot be shorter than the recorded round | open | section 6 | — | — | a proof, or a shorter witness |
