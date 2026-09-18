# Claim ledger

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/paper.md`). Lean names are in namespace `Seed`, files under
`lean4/H3V7N5QF/`. Axiom report: `evidence/lean_axioms.txt`; "std" means the
theorem depends on `propext`, `Classical.choice`, `Quot.sound` only; "none"
means no axioms. No `sorry`, `admit`, or declared axiom occurs in `lean4/`
(scanned by `code/xry/leanreport.py`, recorded in the same file); the report
is refused if the build warns of `sorry` or a cited theorem depends on anything
outside the three axioms above.

## Given

| ID | Statement | Status | Evidence | Axioms | What would falsify it |
|---|---|---|---|---|---|
| G1–G14 | The fourteen sentences of the seed, as listed in `paper.md` §1 | given | `prompt/seed_prompt.md` | — | a sentence of the seed that says otherwise |

## Chosen

| ID | Statement | Status | Evidence | Axioms | What would falsify it |
|---|---|---|---|---|---|
| C1 | An assertion is asserted or not; no multiplicity | chosen | wording of the seed ("is asserted", "whether") | — | a seed sentence that uses multiplicity |
| C2 | To begin with there are exactly the terms `a`, `b` | chosen | the seed flags exactly `bra` as not given; harmless by D9 | — | a seed sentence naming another term to begin with |
| C3 | No cap on the number of terms | chosen | harmless for results and fewest changes by the remark in D8; not claimed for answers | — | a seed sentence giving an alphabet and one letter per term |
| C4 | Sameness under two readings, FREE and ANCHORED, both kept | chosen | `code/xry/state.py`; all evidence files exist for both | — | a proof from the seed that one reading is excluded |
| C5 | Adding what is asserted, removing what is not, identifying a term with itself are not changes; a new term has no assertion; an added assertion is between terms there | chosen | G6 ("exactly one of", "nothing else") | — | a seed sentence allowing a combined change |
| C6 | A result is a legal state up to sameness; one performed change counts one; refusals are attempts that change nothing; round `k` attempts the changes of the results first reached in round `k − 1`, each result's fewest additions first | chosen | `code/xry/explore.py` | — | — (a convention; D10 makes results independent of it) |
| C7 | The obstruction is the set of assertions that would become `xrx`; remove = remove them, then perform; build = additions reaching a legal state that gives the would-be outcome when the added terms are identified back, fewest additions first | chosen | `code/xry/changes.py` (`answers`, `is_build_of`); the readings dropped: D4, D5 | — | — (D10 makes results independent of it) |
| C8 | Bound: at most 5 terms (FREE), 4 terms (ANCHORED) | chosen | `evidence/summary.json` (`plan`) | — | — |
| C9 | `r` does not write a term | chosen | writing only | — | — |

## Derived

| ID | Statement | Status | Evidence | Axioms | What would falsify it |
|---|---|---|---|---|---|
| D1 | `a` and `b` are two terms | derived | Lean `given_distinct` | none | a legal asserting with `a = b` and `arb` |
| D2 | On the given terms exactly two legal states contain `arb`; they differ; each is one change from the other | derived + computed | Lean `two_states_on_given_terms`, `two_states_differ`, `givenA_to_givenB`, `givenB_to_givenA`; `evidence/given.json` (`count: 2`) | std; `two_states_differ`: `propext` | a third legal state on `a`, `b` with `arb` |
| D3 | Obstructed changes are exactly: adding `xrx`; identifying `u`, `v` with `urv` or `vru` asserted | derived + computed | Lean `identify_legal_iff`, `addAssertion_legal_iff`, `remove_legal`, `addTerm_legal`, `identification_obstructed_iff`, `image_loop_iff`; `tests/test_changes.py::test_obstructed_exactly_when_some_xrx_would_be_asserted` | std; `image_loop_iff`: none; `identification_obstructed_iff`: `propext` | a legal state and a change where the rule and the outcome disagree |
| D4 | Adding `xrx` is obstructed in every state | derived | Lean `adding_xrx_always_obstructed` | std | a state in which adding `xrx` leaves no `xrx` |
| D5 | An obstruction to identifying `u`, `v` is cleared only by removing `urv`, `vru`; once asserted, `xrx` survives replacements and additions | derived | Lean, for one change: `obstruction_persists`, `identify_keeps_apart`; for a sequence of changes: paper §4 (D5), not in Lean (O6); Lean `loop_survives_replacement`, `loop_survives_additions`, `only_removal_restores` | std; the two `loop_survives_*`: none | a performed change other than the removal after which `u`, `v` (or their replacements) are unrelated |
| D6 | Every result is legal, finite, and has at least one term | derived | Lean `Step.legal`, `Step.wf`, `Step.nonempty`, `Reach.legal`, `Reach.wf`, `Reach.nonempty`; finiteness: paper §4 | std | a sequence of changes ending with no term, or with `xrx` |
| D7 | (ANCHORED) Once `a`, `b` are one term they stay one term and `arb` is never asserted again | derived | Lean `Step.names_stay_merged`, `Reach.names_stay_merged`, `Reach.arb_gone_for_good` | std | a sequence of changes after which `a ≠ b` again |
| D8 | Fewest changes to a result = terms + assertions − size of what is given + 2 · destroyed givens | derived + computed | Lean `Step.costA_le`, `Step.costB_le`, `fewest_changes_lower_A`, `fewest_changes_lower_B`, `reach_by_edits`, `edits_count`, `givenA_to_oneTerm`, `givenB_to_oneTerm`, `fewest_changes_A`, `fewest_changes_B`; rewriting step and FREE closed form: paper §4; `evidence/results_*.csv` (columns `round_first_reached`, `fewest_changes_by_formula`), `evidence/summary.json` (`round_equals_cost_formula_for_every_result: true`, `free_cost_closed_form_checked_on: 476`, `free_cost_closed_form_mismatches: []`) | std | one explored result whose round differs from the formula; a Lean build failure |
| D9 | Every finite legal state with at least one term, names anywhere, is a result under either beginning | derived + computed | Lean `reach_by_edits`, `givenA_to_oneTerm`, `givenB_to_oneTerm` (names at `a = 0`, `b = 1` or `a = b = 0`); names elsewhere: rewriting step, paper §4 (D8), open in Lean (O3); `evidence/summary.json` (`explored_equals_independent_count: true`) | std | a legal state within the bound missing from `evidence/results_*.csv` |
| D10 | Every answer is a sequence of unobstructed changes; the results are those of unobstructed changes alone; removing first or last gives the same state | derived + computed | Lean `remove_obstruction_first_or_last`, `remove_answer_one_way`, `remove_answer_two_way` (only `vru` asserted: rewriting step, O3), `build_answer`, `build_answer_reverse`; `evidence/summary.json` (`answers_reaching_something_new: []`, for the answers within the bound; those beyond it belong to the frontier) | std | an answer within the bound whose result is unexplored or appears later than the state's round plus the answer's changes |
| D11 | Fewest-addition builds for `xrx` add one term and one assertion; identifying the term back gives the would-be outcome; no build does with less | derived + computed | Lean `build_gives_back`, `build_reverse_gives_back`, `build_needs_term_and_assertion` (a new assertion mentions a term outside the old terms; that this term belongs to the build is not in the Lean statement, which assumes no well-formedness of the build); `tests/test_changes.py::test_every_build_with_one_added_term` (one state, `d = 2`); `evidence/given.json` (`builds_answering_xrx_on_one_term`) | std | a build with no new term or no new assertion |
| D12 | Within the bound the exploration is complete, rounds equal fewest changes without bound, and the frontier is exact | derived + computed | paper §4 (D12); `evidence/summary.json`, `evidence/counts.csv`, `evidence/frontier_*.csv`, `frontier_entries_are_1_plus_2N_per_state_with_N_terms` | — | a mismatch between explored counts and `evidence/counts.csv`; a frontier state with other than `1 + N` leaving attempts or `1 + 2N` frontier entries |

## Computed

| ID | Statement | Status | Evidence | Axioms | What would falsify it |
|---|---|---|---|---|---|
| K1 | Legal states up to FREE sameness with 1–6 terms: 1, 3, 16, 218, 9 608, 1 540 944; never both ways: 1, 2, 7, 42, 582, 21 480; with names (ANCHORED): 1, 8, 100, 2 864, 224 904, 54 411 072 | computed | `evidence/counts.csv`, `evidence/summary.json`; cross-checked by listing for 1–3 terms (`tests/test_orbits.py`) and by the exploration for 1–5 / 1–4 terms | — | a regenerated file with another hash; a listing that disagrees |
| K2 | Results within the bound: 9 846 (FREE), 2 973 (ANCHORED); last round with a new result 22 / 21 (FREE without / with `bra`), 17 / 18 (ANCHORED) | computed | `evidence/rounds_*.csv`, `evidence/summary.json` | — | regeneration gives other numbers |
| K3 | New results per round without bound, rounds 0–20, all four combinations (e.g. round 20, ANCHORED without `bra`: 33 748 590 999) | computed from D8 | `evidence/rounds_*.csv` (last column); agreement with the exploration in rounds `0 … N − 2` (`rounds_agreeing_with_unbounded_formula`) | — | D8 false; or disagreement in an early round |
| K4 | Attempts and obstructed attempts within the bound: 351 130 / 121 792 (FREE), 67 222 / 24 859 (ANCHORED); frontier 9 608 states / 57 648 attempts / 105 688 entries (FREE) and 2 864 / 14 320 / 25 776 (ANCHORED) | computed | `evidence/rounds_*.csv`, `evidence/frontier_*.csv`, `evidence/summary.json` | — | regeneration gives other numbers |
| K5 | Results by terms and assertions added to what is given | computed | `evidence/added_*.csv`, `evidence/results_*.csv` | — | regeneration gives other numbers |
| K6 | Of the statements tested, only "no `xrx`" and "at least one term" hold in every result within the bound; each other statement has a result where it holds and one where it fails | computed | `evidence/follows_*.csv` | — | a listed witness that is not legal or not a result |
| K7 | Evidence is regenerable: a fresh run reproduces every computed file of `evidence/` byte for byte | computed | `python code/generate.py --check`; `tests/test_evidence.py::test_command_line` (the check itself, on a small plan); `evidence/MANIFEST.sha256` | — | `--check` reporting a difference |
| K8 | Tests: 92 passed; line coverage 100.00 %, branch coverage 99.35 % of `code/`; `mypy --strict` clean | computed | `python -m pytest`; `python code/xry/gate.py <coverage.json>`; `python -m mypy` | — | a failing run |

## Refuted

| ID | Statement refuted | Status | Evidence | Axioms | What would falsify the refutation |
|---|---|---|---|---|---|
| R1 | `a` and `b` are one term to begin with | refuted | D1 | none | a legal state asserting `arb` in which `a` and `b` are one term |
| R2 | Some answer makes adding `xrx` performable | refuted | D4 | std | a state in which adding `xrx` leaves no `xrx` |
| R3 | An obstructed identification can be cleared by building, without a removal | refuted | D5 (sequences: paper, not in Lean; O6) | std | a sequence of changes without a removal after which identifying the terms that `u`, `v` became is unobstructed |
| R4 | Some sequence of changes reaches a state without terms | refuted | D6 (`Reach.nonempty`) | std | a sequence of changes ending with no term |
| R5 | After `a`, `b` are identified, some changes tell them apart or assert `arb` again | refuted | D7 | std | a sequence of changes after which `a ≠ b`, or `arb` is asserted again |
| R6 | Some answer reaches a result that unobstructed changes do not reach | refuted | D10 | std | an answer whose result no sequence of unobstructed changes reaches |
| R7 | `bra` is asserted and asserting passes on from `xry`, `yrz` to `xrz` | refuted | Lean `passing_on_refutes_bra` | none | a legal state asserting `arb` and `bra` in which asserting passes on |

## Does not follow

| ID | Statement | Status | Evidence | Axioms | What would falsify it |
|---|---|---|---|---|---|
| N1 | `bra` is asserted | does not follow (derived) | Lean `bra_not_derived` | `propext` | a derivation of `bra` from G3, G4 |
| N2 | `bra` is not asserted | does not follow (derived) | Lean `bra_not_refuted` | none | a derivation of not-`bra` from G3, G4 |
| N3 | Never both ways; passing on; every term first; always both ways | do not follow (computed witnesses: the two beginnings) | `evidence/follows_anchored_*.csv` | — | one of the two beginnings being illegal |
| N4 | `arb` stays asserted; `a`, `b` stay two; exactly two terms; something asserted | do not follow for results (computed witnesses) | `evidence/follows_*.csv` (first rounds 1, 2, 1, 1 without `bra`; 1, 3, 1, 2 with it) | — | a listed witness not being a result |
| N5 | Any statement about the asserting that holds in one finite legal state and fails in another | does not follow (derived from D9) | D9 | std | D9 false |
| N6 | Which answer an obstructed change gets | does not follow (derived from D3, D4, D5, D10) | as cited | std | — |
| N7 | Growth: that terms must be added | does not follow (witnesses: what is given, which adds no term, and a result one change away that adds one); that every result is finite is derived (D6) | `evidence/added_*.csv` | — | what is given not being a result |

## Open

| ID | Statement | Status | Evidence | Axioms | What would settle it |
|---|---|---|---|---|---|
| O1 | The seed read with multiplicity of assertions | open | not explored | — | a model of states with multiplicity and its exploration |
| O2 | Number of new results in rounds 21–100 | open | determined by D8; not computed | — | a count up to sameness for up to 102 terms |
| O3 | Lean proof that changes commute with rewriting of terms (carries `fewest_changes_A/B` to every writing; used by D8, D9, D10) | open in Lean; proved on paper; computed within the bound | paper §4 (D8) | — | a Lean proof |
| O4 | Results beyond the declared bound, listed | open | frontier exported | — | a larger run |
| O5 | Other readings of "build structure" | open as to records; closed as to results (D10) | paper §3 (C7) | — | — |
| O6 | Lean proof of D5 for a sequence of changes (the Lean statements are for one change) | open in Lean; argued on paper (D5) | paper §4 (D5) | — | a Lean proof |
