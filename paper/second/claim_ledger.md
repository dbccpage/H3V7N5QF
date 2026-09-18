# Claim ledger, second derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/second/paper.md`). Lean names in namespace `Seed.Second` are in
`lean4/Second/`; names in namespace `Seed` are the first derivation's,
`lean4/H3V7N5QF/`. Axiom report: `evidence/second/lean_axioms.txt`; "std"
means the theorem depends on `propext`, `Classical.choice`, `Quot.sound` only;
"none" means no axioms. No `sorry`, `admit`, or declared axiom occurs anywhere
in `lean4/` (scanned by `code/second/leanreport.py`, recorded in the same file).

An ID written `1:…` is a claim of the first derivation (`paper/claim_ledger.md`).
The column **Re-check** says how a cited first-derivation result was
re-checked from the second seed: *no change* (the statement mentions no change
of state), *embedding* (restricted through `Step3.toStep` / `Reach3.toReach`,
itself a Lean theorem), *re-proved* (the first proof used a removal), or "—"
for a claim new to this derivation.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1–G5, G7–G14 | The sentences of the seed other than the one on changes, as listed in `paper.md` §1 | given | `prompt/second/seed_prompt.md`; identical to the first seed's | — | no change (`diff`) | a sentence of the seed that says otherwise |
| G6′ | A change is exactly one of: identifying two terms; adding a term; adding an assertion. Nothing else is a change. | given | `prompt/second/seed_prompt.md` | — | — (the one sentence that differs from the first seed) | a sentence of the seed naming another kind of change |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C1 | An assertion is asserted or not; no multiplicity | chosen | wording of the seed | — | 1:C1, no change | a seed sentence that uses multiplicity |
| C2 | To begin with there are exactly the terms `a`, `b` | chosen | the seed flags exactly `bra` as not given; harmless by D9 | — | 1:C2; harmlessness re-proved (additions only) | a seed sentence naming another term to begin with |
| C3 | No cap on the number of terms | chosen | harmless for results and fewest changes: the paths of D8–D10 are additions and never exceed their target's terms; not claimed for builds | — | 1:C3, re-proved | a seed sentence giving an alphabet and one letter per term |
| C4 | Sameness under two readings, FREE and ANCHORED, both kept | chosen | `code/xry/state.py`; all evidence files exist for both | — | 1:C4, no change | a proof from the seed that one reading is excluded |
| C5 | Adding what is asserted and identifying a term with itself are not changes; a new term has no assertion; an added assertion is between terms there | chosen | G6′ ("exactly one of", "nothing else") | — | 1:C5 minus its removal clause | a seed sentence allowing a combined change |
| C6 | A result is a legal state up to sameness; one performed change counts one; refusals are attempts that change nothing; round `k` attempts the changes of the results first reached in round `k − 1`, fewest additions first | chosen | `code/second/explore.py` | — | 1:C6, no change | — (a convention; D10 makes results independent of it) |
| C7 | The obstruction is the set of assertions that would become `xrx`; remove = un-assert them, then perform (impossible under this seed, R3); build = additions reaching a legal state that gives the would-be outcome when the added terms are identified back, fewest additions first | chosen | `code/second/changes.py` (`answers`), `REMOVAL_IMPOSSIBLE` recorded on every obstructed attempt; unchosen readings of "remove": withdrawing (= refusal), moving by identification (refuted, D7) | — | 1:C7; the removal branch refuted | — (D10 makes results independent of it) |
| C8 | Bounds: 5 terms (FREE), 4 terms (ANCHORED) for the exported files; a counts-only census at 5 terms (ANCHORED) | chosen | `evidence/second/summary.json` (`plan`, `anchored_census`) | — | — | — |
| C9 | `r` does not write a term | chosen | writing only | — | 1:C9, no change | — |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D1 | `a` and `b` are two terms | derived | Lean `given_distinct` | none | 1:D1, no change | a legal asserting with `a = b` and `arb` |
| D2 | On the given terms exactly two legal states contain `arb`; they differ; the one without `bra` reaches the one with it in one change; the one with `bra` never reaches the one without | derived + computed | Lean `two_states_on_given_terms`, `two_states_differ`, `givenA_to_givenB3`, `givenB_never_givenA`; `evidence/second/given.json` (`count: 2`, `reaches_the_other_beginning`) | std; `two_states_differ`: `propext` | 1:D2: the two-states theorems no change; `givenA_to_givenB` re-proved as `givenA_to_givenB3`; `givenB_to_givenA` was a removal, refuted here | a third legal state on `a`, `b` with `arb`; a sequence of changes from the beginning with `bra` to the one without |
| D3 | Obstructed changes are exactly: adding `xrx`; identifying `u`, `v` with `urv` or `vru` asserted; adding a term and adding `xry` with `x ≠ y` never | derived + computed | Lean `identify_legal_iff`, `addAssertion_legal_iff`, `addTerm_legal`; `tests/test_second_changes.py::test_obstructed_exactly_when_some_xrx_would_be_asserted` | std | 1:D3, no change (one state operation each; `remove_legal` has no object) | a legal state and a change where the rule and the outcome disagree |
| D4 | Adding `xrx` is obstructed in every state | derived | Lean `adding_xrx_always_obstructed` | std | 1:D4, no change | a state in which adding `xrx` leaves no `xrx` |
| D5 | Every sequence of changes has a carrying map: terms to terms, asserted `xry` to asserted `q(x) r q(y)`, names to names | derived | Lean `Step3.carries`, `Reach3.carries` | std | — (false under the first seed) | a change after which some asserted `xry` has no asserted image |
| D6 | In every result `a`, `b` are two terms, `arb` is asserted (`bra` too if given), there are at least two terms, something is asserted; every result is legal, well formed, finite | derived + computed | Lean `Reach3.names_apart`, `Reach3.arb_persists`, `Reach3.bra_persists`, `Reach3.two_terms`, `reach3_givenA_two_terms`, `reach3_givenB_two_terms`, `Reach3.legal`, `Reach3.wf`, `Reach3.nonempty`; `evidence/second/follows_*.csv`, `summary.json` (`statements_holding_in_every_result`, `additions_never_negative`) | std | legal / wf / nonempty: 1:D6 `Step.legal`, `Step.wf`, `Step.nonempty` by embedding; the rest new | a sequence of changes ending with `a = b`, without `arb`, or with one term |
| D7 | An obstruction is never cleared: after any sequence of changes the images of `u`, `v` are still related, so identifying them is still obstructed; no change has the outcome of a removal | derived | Lean `Reach3.obstruction_persists`, `Reach3.identify_images_obstructed`, `Step3.ne_remove`, `Step.remove_or_step3`, `removal_answer_outcome_unreachable`; for adding `xrx`: D4 | std | 1:D5 one-change `obstruction_persists` by embedding (consistent); sequence version new, closes 1:O6 for this seed | a sequence of changes after which the images of `u`, `v` are unrelated |
| D8 | Fewest changes to a result = terms + assertions − size of what is given; destroyed givens are always zero on a result | derived + computed | Lean `Step3.size_le`, `Reach3.size_le`, `fewest_changes3_lower_A`, `fewest_changes3_lower_B`, `reach3_by_additions`, `additions_count`, `fewest_changes3_A`, `fewest_changes3_B`, `fewest_changes3_every_writing_A`, `fewest_changes3_every_writing_B`, `Reach3.costA_le_inherited`, `Reach3.costB_le_inherited`, `lostA_eq_zero_of_reach3`, `lostB_eq_zero_of_reach3`, `costA_eq_size_of_reach3`, `costB_eq_size_of_reach3`; `evidence/second/results_*.csv` (`round_first_reached` = `fewest_changes_by_formula`), `summary.json` (`round_equals_cost_formula_for_every_result` true in four runs and both census runs; `free_cost_closed_form_checked_on: 476`, mismatches empty) | std | lower bound of 1:D8 (`fewest_changes_lower_A/B`) by embedding; upper bound re-proved (1:`reach_by_edits` used removals) | one explored result whose round differs from the formula; a Lean build failure |
| D9 | The results are exactly the legal states containing what is given (names kept); without names, the legal states with an assertion (with `bra`: with a pair asserted both ways) | derived + computed | Lean `result_iff_A`, `result_iff_B`, `reach3_givenA_contains`, `reach3_givenB_contains`; FREE case: paper §4; `summary.json` (`explored_equals_independent_count` true in four runs and both census runs), `evidence/second/counts.csv` | std | 1:K1 counts, no change; replaces 1:D9, which is refuted (R9) | a legal state containing what is given that the exploration misses within the bound, or an explored result not containing it |
| D10 | Every answer is nothing or additions; every result is reached by additions alone in the same round; identifications reach nothing new | derived + computed | Lean `build_answer3`, `build_answer3_reverse`, `build_gives_back`, `build_reverse_gives_back`, `build_needs_term_and_assertion`, `reach3_by_additions`; `summary.json` (`additions_alone_reach_the_same_results_in_the_same_rounds` true, `answers_reaching_something_new` empty, `answers_removing_the_obstruction: 0`, all four runs) | std | builds: 1:D11 no change; removal answers of 1:D10 refuted (R3) | an answer or identification whose result additions do not reach, or reach later |
| D11 | Changes commute with one-to-one rewriting; size is invariant | derived | Lean `Step3.rename`, `Reach3.rename`, `size_rename` | std | — (closes 1:O3 for this seed) | a change whose rewriting is not a change of the same kind |
| D12 | A result is reachable from a result exactly when a carrying map exists | derived + computed | only if: Lean `Reach3.carries`; if: paper §4, with `Reach3.rename`, `reach3_by_additions` for the one-to-one case; `evidence/second/reach_bound3_*.csv`, `summary.json` (`carrying_map_agrees_with_search` true on 1 156 + 289 + 289 + 100 ordered pairs) | std | — | a pair with a carrying map and no sequence of changes, or the reverse |
| D13 | The fewest classes of a split with no two related terms in a class never decreases along a change | derived + computed | Lean `Reach3.split_mono`; `summary.json` (`fewest_classes_lowered_by` empty on 122 227 + 111 948 + 7 267 + 3 361 changes), column `fewest_classes` of `results_*.csv` | std | — | a change whose outcome needs fewer classes |
| D14 | Within the bound the exploration is complete, rounds equal fewest changes without bound, and the frontier is exact | derived + computed | paper §4; `summary.json` (`explored_equals_independent_count`, `rounds_agreeing_with_unbounded_formula`, `frontier_entries_are_1_plus_2N_per_state_with_N_terms`), `evidence/second/frontier_*.csv`, `counts.csv` | — | 1:D12 re-proved with the additions-only path | a mismatch with the independent count; a frontier state with other than `1 + N` leaving attempts or `1 + 2N` entries |
| D15 | With `bra` given, passing on and "never both ways" hold in no result | derived + computed | Lean `passing_on_refutes_bra`, `Reach3.bra_persists`; `evidence/second/follows_anchored_with_bra.csv`, `follows_free_with_bra.csv` (no `first_holds`) | none; std | 1:R7 `passing_on_refutes_bra`, no change | a result of the beginning with `bra` in which asserting passes on |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | Results with 1–6 terms by independent count: FREE without `bra` 0, 2, 15, 217, 9 607, 1 540 943; FREE with `bra` 0, 1, 9, 176, 9 026, 1 519 464; ANCHORED without `bra` 0, 2, 32, 1 056, 89 472, 22 638 656; with `bra` 0, 1, 16, 528, 44 736, 11 319 328 | computed | `evidence/second/counts.csv`, `summary.json` (`independent_counts`); cross-checked by listing for 1–3 terms (`tests/test_second_orbits.py`) and by the explorations | — | 1:K1 counts, no change | a regenerated file with another hash; a listing that disagrees |
| K2 | Results within the bound: 9 841 / 9 212 (FREE without / with `bra`), 1 090 / 545 (ANCHORED); last round with a new result 22 / 21 / 13 / 12; census at 5 terms (ANCHORED): 90 562 / 45 281, last new round 22 / 21 | computed | `evidence/second/rounds_*.csv`, `summary.json` | — | — | regeneration gives other numbers |
| K3 | New results per round without bound, rounds 0–20, all four combinations (e.g. round 20: 2 007 940 773 / 6 422 479 070 / 27 270 015 509 / 22 096 992 409); agreement with the exploration in rounds `0 … N − 2` | computed from D8, D9 | `evidence/second/rounds_*.csv` (last column), `summary.json` (`rounds_agreeing_with_unbounded_formula`) | — | — | D8 or D9 false; or disagreement in an early round |
| K4 | Attempts / obstructed within the bound: 253 611 / 121 777, 235 665 / 114 691, 17 737 / 9 414, 8 596 / 4 707; frontier 9 607 states / 57 642 attempts / 105 677 entries, 9 026 / 54 156 / 99 286, 1 056 / 5 280 / 9 504, 528 / 2 640 / 4 752; census 2 299 273 / 1 149 670 and 1 126 996 / 574 835 attempts, 89 472 and 44 736 frontier states | computed | `evidence/second/rounds_*.csv`, `frontier_*.csv`, `summary.json` | — | — | regeneration gives other numbers |
| K5 | Results by terms and assertions added to what is given; every group in one round, none negative | computed | `evidence/second/added_*.csv`, `results_*.csv` | — | — | regeneration gives other numbers |
| K6 | Of the fourteen statements tested, those holding in every result within the bound are exactly: no `xrx`, at least one term, at least two terms, something asserted, and with names `arb` asserted, `a`, `b` two terms, and `bra` asserted when given | computed | `evidence/second/follows_*.csv`, `summary.json` | — | — | a listed witness that is not a result |
| K7 | Reachability within 3 terms: 439 of 1 156, 161 of 289, 153 of 289, 62 of 100 ordered pairs reachable; 34, 28, 16, 10 unordered pairs reachable both ways; results reaching what is given within the bound: 14 of 1 090, 83 of 545, 32 of 9 841, 363 of 9 212 | computed | `evidence/second/reach_bound3_*.csv`, `summary.json` (`reachability`, `results_that_reach_what_is_given`) | — | — | regeneration gives other numbers |
| K8 | Fewest classes never fell on 122 227, 111 948, 7 267, 3 361 changes | computed | `summary.json` (`fewest_classes_checked_on`, `fewest_classes_lowered_by`) | — | — | a listed drop |
| K9 | Evidence is regenerable: a fresh run reproduces every computed file of `evidence/second/` byte for byte; the first derivation's `evidence/` still regenerates unchanged | computed | `python code/generate_second.py --check`; `python code/generate.py --check`; `python code/lean_report.py`; `tests/test_second_evidence.py::test_command_line` | — | — | a `--check` reporting a difference |
| K10 | Tests: 193 passed (both derivations, including the prose-watchlist gate and the cost property); line coverage 100.00 %, branch coverage 99.24 % of `code/`; `mypy --strict` clean | computed | `python -m pytest`; `python code/xry/gate.py coverage.json`; `python -m mypy` | — | — | a failing run |

## Refuted

| ID | Statement refuted | Status | Evidence | Axioms | Re-check | What would falsify the refutation |
|---|---|---|---|---|---|---|
| R1 | `a` and `b` are one term to begin with | refuted | D1 | none | 1:R1, no change | a legal state asserting `arb` with `a = b` |
| R2 | Some answer makes adding `xrx` performable | refuted | D4 | std | 1:R2, no change | a state in which adding `xrx` leaves no `xrx` |
| R3 | The obstruction of some obstructed change can be removed; some change has the outcome of a removal | refuted | D7 (`Reach3.identify_images_obstructed`, `Step3.ne_remove`, `removal_answer_outcome_unreachable`), D4 | std | replaces 1:R3 (which allowed removal) | a sequence of changes after which the images of `u`, `v` are unrelated; a change equal to a removal |
| R4 | Some sequence of changes reaches a state with fewer than two terms | refuted | D6 (`reach3_givenA_two_terms`, `reach3_givenB_two_terms`, `oneTerm_unreachable_A`, `oneTerm_unreachable_B`) | std | strengthens 1:R4 | a result with one term |
| R5 | Some sequence of changes identifies `a` and `b`, or un-asserts `arb` | refuted | D6 (`Reach3.names_apart`, `Reach3.arb_persists`) | std | strengthens 1:R5 | a result with `a = b` or without `arb` |
| R6 | Some answer, or some identification, reaches a result that additions do not reach | refuted | D10 | std | 1:R6, plus identifications | such an answer or identification |
| R7 | `bra` is asserted and asserting passes on; with `bra` given, some result passes on | refuted | D15 (`passing_on_refutes_bra`, `Reach3.bra_persists`) | none; std | 1:R7, no change | a legal result of the beginning with `bra` in which asserting passes on |
| R8 | The beginning with `bra` reaches the beginning without | refuted | D2 (`givenB_never_givenA`) | std | — | a sequence of changes from `arb`, `bra` to `arb` alone |
| R9 | Some result does not contain what is given (1:D9 under this seed) | refuted | D9 (`reach3_givenA_contains`, `result_iff_A`) | std | — | a result without `arb` between `a`, `b` |
| R10 | Some result is reached in fewer changes than its size difference, or has fewer terms or assertions than what is given | refuted | D8, D6; `additions_never_negative` | std | — | such a result |
| R11 | Some change lowers the fewest classes of a split | refuted | D13 | std | — | such a change |

## Does not follow

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| N1 | `bra` is asserted | does not follow (derived) | Lean `bra_not_derived` | `propext` | 1:N1, no change | a derivation of `bra` from G3, G4 |
| N2 | `bra` is not asserted | does not follow (derived) | Lean `bra_not_refuted` | none | 1:N2, no change | a derivation of not-`bra` from G3, G4 |
| N3 | Never both ways; passing on; every term first; always both ways (from the beginning without `bra`; the first two are refuted in every result of the beginning with `bra`, D15) | do not follow (computed witnesses) | `evidence/second/follows_*.csv` | — | 1:N3, narrowed | a listed witness not being a result |
| N4 | Exactly two terms (the other three items of 1:N4 now follow, D6) | does not follow (computed witnesses: what is given; add a term) | `evidence/second/follows_*.csv` | — | 1:N4, narrowed | — |
| N5 | Any statement about the asserting that holds in one legal state containing what is given and fails in another | does not follow (derived from D9) | D9 | std | 1:N5, narrowed | D9 false |
| N6 | Which answer an obstructed change gets (refuse or build; removal never) | does not follow (derived from D3, D7, D10) | as cited | std | 1:N6, changed | — |
| N7 | Growth: that terms must be added | does not follow (witnesses: what is given, a result one change away) | `evidence/second/added_*.csv` | — | 1:N7, no change | what is given not being a result |
| N8 | That the number of terms, of assertions, or the size never decreases | does not follow (computed witnesses) | `evidence/second/attempts_bound3_anchored_without_bra.jsonl` (state `3:01:0-1`, "identify a and c", outcome `2:01:0-1`); paper §5 | — | — | the witness not being a legal change |
| N9 | That a result once left is never returned to; that every result returns to what is given | do not follow (witness of N8; R8; `results_that_reach_what_is_given`) | `summary.json`, `results_*.csv` | std (R8) | — | — |
| N10 | That reachability among results is symmetric, or antisymmetric | do not follow (computed: K7) | `evidence/second/reach_bound3_*.csv` | — | — | a listed pair not being reachable as stated |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would settle it |
|---|---|---|---|---|---|---|
| O1 | The seed read with multiplicity of assertions | open | not explored | — | 1:O1 | a model with multiplicity and its exploration |
| O2 | Number of new results in rounds 21–100 | open | determined by D8, D9; not computed | — | 1:O2 | a count up to sameness for up to 102 terms |
| O3 | Lean proof of the "if" direction of D12 when the carrying map merges terms | open in Lean; proved on paper; computed within 3 terms | paper §4 (D12) | — | — | a Lean proof (the identifications along the map) |
| O4 | Results beyond the declared bounds, listed | open | frontier exported (bounds 5 / 4); census counts at 5 | — | 1:O4 | a larger run |
| O5 | Other readings of "build structure" | open as to records; closed as to results (D10) | paper §3 (C7) | — | 1:O5 | — |
