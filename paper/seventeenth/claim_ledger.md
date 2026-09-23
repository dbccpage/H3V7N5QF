# Claim ledger, seventeenth derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/seventeenth/paper.md`). Lean names in namespace `Seed.Seventeenth`
are in `lean4/Seventeenth/`; names in `Seed` are the base's
(`lean4/H3V7N5QF/`). Axiom report: `evidence/seventeenth/lean_axioms.txt`,
written by `python code/lean_report_seventeenth.py` after `lake build`.
"std" means the cited theorem depends only on `propext`, `Classical.choice`
and `Quot.sound`. The report's scan of `lean4/` finds no `sorry`, `admit`,
or declared axiom outside comments.

The column **Re-check** says how a cited base result was re-checked from
this seed, and whether it rested on the struck sentence. *no change*: the
statement mentions no ban. *re-proved*: a `Step17` proof that does not
assume the ban. *through the embedding*: `Step.toStep17`, `Step17.toStep`,
`Reach.toReach17`, `Reach17.toReach`. *computed again*: `check_bounds`
against `xry.explore` and `xry.cost.cost`. "—" : a claim new to this
derivation.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1–G3, G5–G14 | The base seed, except the struck sentence | given | `prompt/seventeenth/seed_prompt.md`; `diff` against `prompt/seed_prompt.md` | — | 1:G1–G3, G5–G14 no change | a sentence of this seed that differs elsewhere |
| G4 | "For no term `x` may `xrx` be asserted" is not a sentence of this seed | given | the same `diff` | — | 1:G4 struck | the sentence appearing in this seed |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C2 | Beginnings: terms `a`, `b`, `arb`, and `bra` either way. Unchosen, kept: also `ara`; also `brb` | chosen | `xry.state.given`; `with_loop`, `with_other_loop` | — | 1:C2, the support "G4 forbids them" dropped | a seed sentence naming another term to begin with |
| C4 | Both readings of sameness kept | chosen | `xry.state.Sameness`; four runs in `summary.json` | — | 1:C4 no change | a proof from the seed that one reading is excluded |
| C5 | Adding what is asserted, removing what is not, identifying a term with itself, are not changes | chosen | 1:C5; `xry.changes.changes` | — | 1:C5 no change | a seed sentence allowing one of those as a change |
| C6 | One performed change counts one; a refusal changes nothing; fewest additions first | chosen | `seventeenth.explore.closure`; `xry.explore.order` | — | 1:C6 no change | — |
| C7 | M1 is the base obstruction; M2 is "the outcome asserts `xrx`"; A-replace does not enter an obstructed change; A-perform does | chosen | `seventeenth.loop`; `Step17.obstructedM1`, `Step17.obstructedM2`; `closure_unobstructed`, `closure_perform` | — | 1:C7 kept as M1 and as A-replace; the dropped reading is A-perform | a seed sentence that picks one reading |
| C8 | Bound: 3 terms and 6 rounds; log at 2 terms and 3 rounds | chosen | `Plan` in `seventeenth.evidence`; `summary.json` | — | 1:C8 lowered | — |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D1 | On a loop-free state, M1 and M2 name the same changes. Adding `xrx` is M1-obstructed with no loop-free hypothesis; that second sentence holds by the definition of M1 (C7): `adding_xrx_step_obstructed` is `rfl` | derived + computed | Lean `m1_iff_m2_of_loopFree`, `adding_xrx_obstructed`, `adding_xrx_step_obstructed`; `summary.json` `m_disagree_loopfree` | std | 1:D3 re-proved without taking `Legal` as a given | a loop-free state and a change where the two tests differ |
| D2 | On `loopyWitness`, identifying `1` with `2` is not M1-obstructed and is M2-obstructed | derived + computed | Lean `loopy_m1_allows`, `loopy_m2_obstructs`, `loopyWitness_hasXrx`; `summary.json` `m_agree_on_loop` | std | — | the two tests agreeing on that identification |
| D3 | An unobstructed `Step17` from a loop-free state stays loop-free, and so does `Reach17` | derived + computed | Lean `Step17.loopFree_out`, `Step17.no_xrx_of_unobstructed`, `Reach17.loopFree`; `summary.json` `replace_has_xrx` | std | 1:D6 re-proved; the hypothesis is the start, not the ban | an unobstructed step from a loop-free state whose outcome asserts `xrx` |
| D4 | A base `Step` is an unobstructed `Step17`; an unobstructed `Step17` is a base `Step`, with no hypothesis on the state; the sequences match | derived | Lean `Step.toStep17`, `Step.unobstructed17`, `Step17.toStep`, `Reach.toReach17`, `Reach17.toReach` | std | through the embedding | a base step that is M1-obstructed, or an unobstructed `Step17` that is not a base `Step` |
| D5 | Along `Reach17` from either beginning, the fewest changes of a loop-free well-formed state with `a = 0` and `b ∈ {0, 1}` is the base formula | derived + computed | Lean `fewest_changes17_A`, `fewest_changes17_B`, `fewest_changes17_lower_A`, `fewest_changes17_lower_B`; `summary.json` `replace_cost_mismatch`, `replace_not_formula`, `replace_not_base` | std | 1:D8 through the embedding; computed again | an A-replace result whose round differs from `xry.cost.cost` |
| D6 | Identifying `a` with `b` in what is given is one `Step17`. The outcome asserts `ara`, the names are one term, and the base cost is not that length (6 ≰ 1+3 without `bra`; 8 ≰ 1+4 with `bra`). Adding `ara` is one `Step17` that no `Reach17` reaches | derived + computed | Lean `identify_givenA_step`, `identify_givenA_reach`, `names_merged_with_loop`, `mergedA_hasXrx`, `cost_not_lower_bound_A`, `cost_not_lower_bound_B`, `add_ara_reach`, `add_ara_hasXrx`, `add_ara_not_unobstructed`; `summary.json` `perform_misses_witness`, `perform_cost_not_above`, `loop_beginning_not_in_perform` | std | 1:D8 fails as a lower bound on `ReachAll` | the outcome not asserting `ara`, or `costA` of it being ≤ 4 |
| D7 | Remove-then-identify equals identify-then-remove. The intermediate asserts `xrx`. Refusal of adding `ara` does not enter it, and `Reach17` does not reach it | derived + computed | Lean `remove_first_eq_perform_first`, `perform_first_intermediate_has_xrx`, `perform_first_givenA`, `refusal_does_not_enter`; `summary.json` `remove_first_differs`, `refusal_changes_something` | std | 1:D10 cited, not re-proved: `remove_first_eq_perform_first` is the base's `remove_obstruction_first_or_last`, unchanged, whose hypothesis is a loop-free start (not the ban as a given); the intermediate is no longer excluded | the two orders ending apart, or the refusal changing the state |
| D8 | Every `Step17` preserves well-formedness and at least one term, and keeps the names one term once they are one term. The same for `Reach17` and `ReachAll` | derived | Lean `Step17.wf`, `Step17.nonempty`, `Step17.names_stay_merged`, `Reach17.wf`, `Reach17.nonempty`, `Reach17.names_stay_merged`, `ReachAll.wf`, `ReachAll.nonempty`, `ReachAll.names_stay_merged` | std | 1:D6, 1:D7 re-proved; none of these proofs assumes loop-freeness | a `Step17` that drops the last term, or that separates the names |
| D9 | For an injective rewriting, a `Step17` becomes a `Step17` of the same kind, and so do `Reach17` and `ReachAll`; loop-freeness is carried | derived | Lean `Step17.rename`, `Reach17.rename`, `ReachAll.rename`, `loopFree_rename` | std | the base's open rewriting step, for these steps | an injective rewriting that does not carry one of the four kinds |
| D10 | Adding a term is never M1-obstructed, and the outcome has a new term, so there is no last round | derived | paper §4, from the `addTerm` clause of `Step17.obstructedM1` (it is `False`) and `St.addTerm` (the term is new) | — | 1: the same reason the base does not finish in 100 rounds | a state on which adding a term is M1-obstructed, or returns the same state |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | At 3 terms and 6 rounds, four runs: the disagreement lists are empty; 201 A-replace results and 1188 A-perform results, summed; `ara` and `brb` beginnings are in A-perform and not in A-replace; the one-term witness is at round 1 | computed | `evidence/seventeenth/summary.json`; `tests/test_seventeenth_core.py` | — | computed again against `xry.explore` | a regenerated `summary.json` with `passes` false or other totals |
| K2 | The exact frontier of the declared bound: 874 attempts that leave the term bound (`\|terms`) and 400 results first reached in round 6, whose changes the round bound left unattempted (`\|rounds`; per run in `unexpanded_by_run`); and the attempt log at 2 terms and 3 rounds | computed | `summary.json` `frontier`, `unexpanded_by_run`; `attempts_bound2_rounds3.jsonl` | — | — | `--check` reporting a difference |
| K3 | Evidence regenerates byte for byte | computed | `python code/run_seventeenth.py --check`; `evidence/seventeenth/MANIFEST.sha256` | — | — | `--check` reporting a difference |
| K4 | Every theorem cited above depends only on `propext`, `Classical.choice` and `Quot.sound`, and `lean4/` contains no `sorry`, `admit`, or declared axiom outside comments | computed | `evidence/seventeenth/lean_axioms.txt`; `tests/test_seventeenth_leanreport.py` fails if a cited theorem of `lean4/Seventeenth/` has no line there | std | — | a line of that file outside those three axioms, a hit of the scan, or a cited theorem with no line |
| K5 | For each of the 1389 results, by run and reading: how many terms and assertions it adds to what is given, the round it is first reached, and whether it asserts `xrx` | computed | `evidence/seventeenth/results_bound3_rounds6.csv` | — | the base records the same per result (`xry.evidence.result_rows`) | `--check` reporting a difference |

## Refuted

| ID | Statement refuted | Status | Evidence | Axioms | Re-check | What would falsify the refutation |
|---|---|---|---|---|---|---|
| R1 | The struck sentence is still a given | refuted | G4 | — | 1:G4 | the sentence in this seed |
| R2 | Every result asserts no `xrx` | refuted | D6 (`mergedA_hasXrx`); it holds of A-replace results (D3) | std | 1:D6 survives only along `Reach17` | `has_xrx` false on `oneLoop` |
| R3 | A-replace and A-perform have the same results | refuted | D6 (`add_ara_not_unobstructed`); K1 | std | — | `add_ara` reached by `Reach17` |
| R4 | M1 and M2 disagree on some loop-free state | refuted | D1 | std | — | a loop-free counterexample |
| R5 | The base cost lower-bounds A-perform | refuted | D6 | std | 1:D8 | `costA (givenA.identify 0 1) ≤ 4` |
| R6 | After the perform-first identification, `ara` is not asserted | refuted | Lean `arb_not_gone` | std | 1:`Reach.arb_gone_for_good` fails on this state | `(a, a)` absent there |

## Does not follow

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| N1 | `bra` is asserted, and `bra` is not asserted, as claims about loop-free assertings | does not follow | base Lean `bra_not_derived`, `bra_not_refuted`; both beginnings are kept | std | 1:N1, 1:N2; the models are loop-free, so they still apply | one of the two beginnings excluded by this seed |
| N2 | `a` and `b` are two terms in every result, and they are one term to begin with | does not follow | they are two in the chosen beginning; they are one after the identification (D6, D8) | std | `given_distinct` survives only with `Legal` | the identification leaving them two terms |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would close it |
|---|---|---|---|---|---|---|
| O2 | A closed form for the fewest A-perform changes | open | D6 refutes the base formula; no replacement | — | — | a proved formula, checked against the rounds |
| O3 | A path that leaves the term bound cannot be shorter than the recorded A-perform round | open | paper §6 | — | — | a proof, or a witness path |
| O4 | The A-perform closure equals the well-formed states inside the bound | open | no listing; K2 is the frontier instead | — | the base orbit count counts loop-free states only | a count that matches the closure |
| O5 | The base cost at a writing other than `a = 0`, `b ∈ {0, 1}` | open | D9 carries the steps; D5 does not claim the other writings | — | 1: the same open rewriting of the cost | a Lean theorem without that hypothesis |
