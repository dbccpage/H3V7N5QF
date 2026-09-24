# Claim ledger, seventh derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/seventh/paper.md`). Lean names in namespace `Seed.Seventh` are in
`lean4/Seventh/`; names in `Seed.Sixth`, `Seed.Fifth`, `Seed.Fourth`, `Seed`
are the earlier derivations' (`lean4/Sixth/`, `lean4/Fifth/`, `lean4/Fourth/`,
`lean4/H3V7N5QF/`). Axiom report: `evidence/seventh/lean_axioms.txt`; "std"
means the theorem depends on `propext`, `Classical.choice`, `Quot.sound` only
(some on a subset); "none" means no axioms. No `sorry`, `admit`, or declared
axiom occurs anywhere in `lean4/` (scanned by `code/seventh/leanreport.py`,
recorded in the same file).

An ID written `1:…` … `6:…` is a claim of the first … sixth derivation. The
column **Re-check** says how a cited earlier result was re-checked from the
seventh seed and whether it *survives with nothing given and no names*: *no
change* (the statement mentions neither the given nor the names), *through
the maps* (a sixth state with its names forgotten is a seventh state and
every sixth change is a seventh change on the forgotten states,
`Step6.forget`, `Reach6.forget`; a seventh state with a term, named, is a
sixth state and every seventh change on it is a sixth change on the named
states, `Step7.name`, `Reach7.name`; the statement is about a change or a
sequence and holds for it here), *without object* (the statement is about the
given, the names, `bra` or the destroyed givens), *re-proved* (proved afresh
for the seventh's states), *computed again* (re-run beside the seventh
exploration and compared on the results with a term), or "—" for a claim new
to this derivation. "Survives" means the earlier statement holds as stated;
"survives on states with a term" means it holds exactly there; "does not
survive" means it is false under the seventh seed, with the witness.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1, G2‴, G6, G7, G11–G14 | The sentences of the seed, as listed in `paper.md` §1, every one the sixth seed's | given | `prompt/seventh/seed_prompt.md`; identical to the sixth seed's (`diff`) | — | no change | a sentence of the seed that says otherwise |
| G3″ | Nothing is given: to begin with there are no terms and nothing is asserted | given | `prompt/seventh/seed_prompt.md`; replaces the sixth's G3′ and G5 (`diff`) | — | — | a sentence of the seed naming a term or asserting something |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C3 | No cap on the number of terms | chosen | harmless: the sequences of D4, D5 stay within the target's terms; those of D8 within `max(terms) + 2` (the sixth's) | — | 6:C3 restated | a seed sentence giving an alphabet and one letter per term |
| C5‴ | Adding an asserted assertion, and adding `xrx`, are changes; removing what is not asserted and identifying a term with itself are not; an identification adds up the multiplicities of the pairs that become one pair | chosen | `code/fifth/state.py`, `code/fifth/changes.py` (imported); Lean `NSt.identify`, `NSt.remove` (the fifth's definitions without names) | — | 6:C5‴ no change; the unchosen "larger of the two" reading gives the same results, reachability and cost (D15) | a seed sentence combining multiplicities otherwise |
| C6 | A result is a counted state up to sameness; every change counts one; round `k` performs the changes of the results first reached in round `k − 1`, fewest additions first; round 0 is the empty state | chosen | `code/seventh/explore.py` | — | 6:C6 with the empty beginning; the round of a result is derived (D4) | — (a convention; D4 makes rounds independent of the order) |
| C8′ | The bound is on terms and on rounds together: 5 terms with 11 rounds; 3 terms with 14; 2 terms with 40; a census at 6 terms with 12 rounds; the full log at 2 terms and 4 rounds; reachability among the results of 3 terms and 6 rounds along the changes among those of 3 terms and 8 rounds; the frontier has two parts | chosen | `code/seventh/evidence.py` (`Plan`); `summary.json` (`plan`); `change_log.md` item 9 (raised after timing) | — | 6:C8′ with one beginning and one reading | — |
| C9 | `r` writes assertions, not terms | chosen | `code/xry/state.py` (`LETTERS`) | — | 1:C9 no change | — |
| C10 | "Separability" (the task's word) is read as telling the two named terms apart, the sixth's one-way property; a second reading, the fewest classes of a split, is also answered | chosen | `paper.md` §7 | — | — | the task meaning a third thing |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D1 | The first change adds a term; the empty state has one change; round 1 is the one-term state asserting nothing | derived + computed | Lean `first_change_adds_term`; `given.json` (`the_first_change_can_only_add_a_term`), `summary.json` (`the_first_round_is_the_one_term_state_alone` true in every run) | std | — (new) | a change listed on the empty state other than a term |
| D2 | A term stays: every change on a state with a term leaves a state with a term, and so does every change on a well-formed state; the empty state is reached only from itself, in zero changes; the sixth's "names stay merged" is vacuous through the naming map | derived + computed | Lean `Step7.nonempty`, `Step7.nonempty_out`, `Reach7.nonempty`, `reach7_empty_iff`, `empty_never_returned`, `no_cycle_at_empty`, `names_merged_vacuous`; `summary.json` (`term_lost` empty, `results_that_reach_what_is_given: 1` in every run) | std | 6:D7, 1:D7 vacuous through the maps, replaced | a sequence from a state with a term to the empty state |
| D3 | A result with `n` terms and `d` asserted pairs (diagonal included) has `C(n, 2) + d + 1 + n²` changes, `1 + n²` of them additions; on a result asserting no `xrx`, `n` plus the related pairs make some `xrx` asserted | derived + computed | `code/seventh/changes.py`, `tests/test_seventh_changes.py` (against the list); `summary.json` (`attempts_equal_formula`, `xrx_making_equal_sixth_formula` true in every run) | — | 6:D3 no change (the count mentions no name; its "obstruction" characterisation through the maps) | a state whose list has another length |
| D4 | Fewest changes = size: (i) every change moves the size by exactly one, so size ≤ length; (ii) additions reach every well-formed state in its size; (iii) the same in every writing; (iv) exactly the additions raise the cost by one; (v) parity; (vi) every shortest sequence is additions only | derived + computed | Lean `Step7.size_step`, `Reach7.size_le`, `fewest_changes7_lower`, `size_addTerm7`, `Contains7.name`, `reach7_of_contains`, `step_first_term`, `reach7_by_additions`, `fewest_changes7`, `cost_oneTerm`, `fewest_changes7_every_writing`, `size_rename7`, `Step7.lowers_or_adds`, `Reach7.size_parity`, `shortest_are_additions`, `Add7.toStep7`, `AddReach7.toReach7`; `summary.json` (`round_equals_cost_formula_for_every_result` true in every run and the census, `cost_rule_disagreements`, `size_not_moved_by_one`, `cost_raised_by_more_than_one` empty, `changes_keeping_the_round: 0`) | std | 6:D8(i), (v) through the maps for the three kinds that need a term (`Seed.Fourth.size_addAssertion`, `Seed.Fifth.size_remove`, `Seed.Fifth.size_identify` on the named state), re-proved for the term; 6:D8(ii)'s `reach6_of_contains` through the maps; the destroyed givens without object | a sequence shorter than the size; an explored result whose round differs from its size |
| D5 | Every well-formed state is a result, the empty one included; the sixth's results (either beginning, either reading) are exactly the results with a term | derived + computed | Lean `result7_iff`, `empty_is_a_result`, `results_forget_A`, `_B`, `results_name`, `sixth_never_empty`, `empty_is_new`; `summary.json` (`same_results_as_sixth_derivation_any_rewriting`, `sixth_round_is_its_cost_formula_on_every_shared_result`, `sixth_results_names_forgotten_are_results`, `results_with_a_term_of_small_size_are_sixth_results_names_forgotten`, `explored_equals_independent_count` true in every run and the census) | std | 6:D9 through the maps (`result6_iff_A`, `_B`; `Reach6.nonempty`); 6:K1, 6:K2 computed again | a well-formed state the exploration misses within the bound; a sixth result missing, or at a round other than its sixth cost |
| D6 | Every result is well formed and finite; a result other than the empty state has a term | derived | Lean `Reach7.wf`, `Step7.wf`, `Reach7.nonempty` | std | 6:D6's `Step6.wf` through the maps for three kinds, `addTerm_wf` re-proved | a reached state asserting between terms that are not there |
| D7 | Changes commute with one-to-one rewriting; sequences keep their length; the size is the same in every writing; the empty state is its own only writing | derived | Lean `rename4_name`, `forget_rename4`, `rename7_addTerm`, `rename7_addAssertion`, `rename7_remove`, `rename7_identify`, `Step7.rename`, `Reach7.rename`, `size_rename7`, `wf_rename7`, `rename7_empty` | std | 4:D11, 5:D11, 6:D11 through the maps (`rename4_addTerm`, `rename4_addAssertion`, `rename4_remove`, `rename4_identify`, `size_rename4`, no change) | a change whose rewriting is not a change of the same kind |
| D8 | A well-formed state is reachable from a well-formed state exactly when it has a term or the start is empty; the sixth's criterion says "always" on states with a term | derived + computed | Lean `reach7_of_nonempty`, `reach7_iff`, `criterion_survives`; `reach_bound3_rounds6.csv`, `summary.json` (`criterion_agrees_with_search` true on 7 921 ordered pairs; `sixth_criterion_agrees_on_results_with_a_term` true on 7 744 pairs) | std | 6:D12's `reach6_of_names`, `reach6_iff` through the maps (survive on states with a term); 6:K8 computed again | a pair the criterion admits with no sequence, or the reverse |
| D9 | Reachability is mutual among the results with a term, one-way out of the empty state; any two results are comparable; every result with a term reaches itself in two changes, the empty state never | derived + computed | Lean `reach7_symm`, `reach7_total`, `empty_never_returned`, `cycle2_7`, `Reach7.cycles`, `Reach7.unbounded`, `no_cycle_at_empty`, `no_return_fails7`, `antisymm_fails7`, `length_not_unique7`, `identify_twoTerms7`, `oneTerm7_wf`; `summary.json` (`results_with_a_two_change_cycle = results − 1`, `unordered_pairs_reachable_both_ways: 3828`, `ordered_pairs_unreachable: 88`) | std | 6:D13 through the maps (`cycle2_6`) on states with a term; the empty-state clauses new | two results with a term not reaching each other; a cycle at the empty state |
| D10 | Within the bound the exploration is complete; the independent count with the empty state added certifies it; the frontier is one entry per result at the bound; the shortest-sequence counts are exact for every result; rounds `0 … N` agree with the unbounded counts | derived (paper §4) + computed | `code/seventh/orbits.py`; `summary.json` (`explored_equals_independent_count`, `frontier_entries_are_1_per_state_with_N_terms`, `results_with_exact_sequence_count = results`, `rounds_agreeing_with_unbounded_formula` all true), `counts.csv`, `tests/test_seventh_orbits.py` (counts against listing every writing) | — | 6:D14 with `count_free` no change (`n = 0` added); its exactness clauses about the names without object; "`N − 2`" becomes "`N`" | a mismatch with the independent count; a frontier result with other than one entry |
| D11 | With at most two terms the results of round `r` are `[r = 0] + [r ≥ 1] + [r ≥ 2]·(C(r+1, 3) + [r even]·r/2)/2`, cubic; one-term results have one shortest sequence | derived (paper §4) + computed | `code/seventh/orbits.py` (`two_term_count`, `two_term_round_count`), `summary.json` (`two_term_rounds_equal_closed_form` true on all 40 rounds, `two_term_closed_form_mismatches` empty, `one_term_results_have_one_shortest_sequence` true), `tests/test_seventh_orbits.py` | — | 6:D17 replaced (its forms had the names kept) | a round with another count |
| D12 | The two readings of sameness coincide: with no names every rewriting keeps the names | derived (paper §4) + computed | paper §4; `summary.json` (`sixth_results_names_forgotten` = `sixth_results_any_rewriting` in every run) | — | 1:C4, 6:C4 (two readings) collapse to one | a rewriting barred under one reading and not the other |
| D13 | The sixth's cost does not survive (the one-term state: one change here, two there); the size difference survives with `size(given) = 0` | derived + computed | Lean `sixth_cost_fails`, `costA6_oneTerm7`, `size_difference_survives`; `given.json` (the sixth's beginnings cost 3 and 4 from here), `summary.json` (`results_where_the_sixth_cost_equals_the_cost: 0` without `bra` in every run) | std | 6:D8, 5:D8, 1:D8 do not survive; 4:D8's size difference survives | a result whose fewest changes is the sixth's formula |
| D14 | No statement about the asserting holds in every result; the sixth's "at least one term" fails at round 0 | derived (from D5) + computed | `follows_*.csv`, `summary.json` (`statements_holding_in_every_result` empty in every run) | — | 6:N3's everywhere-true statement does not survive | a statement holding in every well-formed state other than a tautology |
| D15 | The unchosen reading of identification (the larger of the two) gives the same results, reachability and cost | derived (paper §4) | paper §4 D15 | — | 6:D19 without object (no `bra`) | a proof that the costs differ under this seed |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | Results within the bounds: 22 686 (5 terms, 11 rounds), 29 191 (3 terms, 14 rounds), 56 111 (2 terms, 40 rounds); of which the sixth's results with a term within its rounds 7 177 / 11 018, 16 258 / 23 273, 50 729 / 54 625 (without / with `bra`); every count equals the independent count; census 82 749 at 6 terms and 12 rounds; `counts.csv` for `n ≤ 6`, total `≤ 12` (1, 13, 924, 49 357, 1 278 844, 15 677 058, 99 876 431) | computed | `summary.json`, `results_*.csv`, `counts.csv` | — | 6:K1 computed again: the sixth's counts for `n ≥ 1` are these | regeneration gives other numbers; a mismatch with the independent count |
| K2 | Results per round: 5 terms 1, 1, 2, 4, 10, 24, 64, 177, 516, 1 563, 4 869, 15 455 (without bound 1, 1, 2, 4, 10, 24, 65, 180, 530, 1 629, 5 226, 17 412); 3 terms 1, 1, 2, 4, 9, 21, 51, 119, 267, 581, 1 176, 2 291, 4 237, 7 539, 12 892; two terms the closed form of D11; every round has a new result | computed | `rounds_*.csv`, `summary.json` | — | 6:K2 computed again (the sixth's rounds are its cost formula) | regeneration gives other numbers |
| K3 | Attempts: `C(n, 2) + d + 1 + n²` per result whose changes were attempted (192 540 in the 5-term run, 282 739 in the 3-term run, 487 619 in the two-term run, 785 407 in the census), none obstructed; 12 783 / 7 804 / 1 140 / 47 759 making some `xrx` asserted on results asserting none; of the 190 936 changes within the bound of the 5-term run 118 771 raise the round and 72 165 lower it, none keeps it | computed | `rounds_*.csv`, `summary.json` | — | 6:K3's counts recovered by the sixth's function on the results with a term | a run whose totals differ |
| K4 | Full log of 29 attempts at 2 terms and 4 rounds, every one performed, the first being the term | computed | `attempts_bound2_rounds4.jsonl`, `summary.json` (`attempts_in_full_log`) | — | 6:K4 (records without obstruction) same shape | an attempt recorded as anything but performed |
| K5 | Frontier: one entry per result with `N` terms whose changes were attempted (1 604 / 15 592 / 50 730 / 1 953); results of the last round awaiting: 15 455 (483 162 changes), 12 892 (232 689), 5 341 (51 841), 58 110 | computed | `frontier_*.csv`, `summary.json` | — | 6:K5 computed again | a frontier result with other counts |
| K6 | Results by additions (5 terms): one adds (0, 0), one adds (1, `k`) for each `k ≤ 10`, the two-term counts of D11 add (2, `t`), …; nothing negative | computed | `added_*.csv` | — | 6:K6 without object (nothing to fall below); the shape is new | regeneration gives other numbers |
| K7 | Statements: none of the eighteen holds in every result; shortest sequences: totals 2 281 479 967 / 71 513 837 362 / about 1.3·10^23; 16 / 17 / 42 results with one shortest sequence; every count exact | computed | `follows_*.csv`, `results_*.csv`, `summary.json` | — | 6:K7 computed again on the results with a term; the counts are from the empty state, not from `arb` | a listed witness not being a result |
| K8 | Reachability within 3 terms and 6 rounds: 7 833 of 7 921 ordered pairs reachable, the 88 unreachable being those into the empty state; 3 828 unordered pairs both ways; the criterion agrees with the search on every pair; the sixth's criterion agrees on its 7 744 pairs | computed | `reach_bound3_rounds6.csv`, `summary.json` (`reachability`) | — | 6:K8 computed again | a disagreement |
| K9 | Evidence is regenerable: a fresh run reproduces every computed file of `evidence/seventh/` byte for byte; the six earlier derivations' evidence still regenerates | computed | `python code/generate_seventh.py --check`; the six earlier `--check`s and Lean reports (`change_log.md` item 12) | — | — | a `--check` reporting a difference |
| K10 | Tests: 570 passed (seven derivations, the prose-watchlist gate included); line coverage 100.00 %, branch coverage 99.68 % of `code/`, every evidence module fully covered; `mypy --strict` clean; prose watchlist clean with every pinned hit of the seventh paper in its §10 | computed | `python -m pytest`; `python code/xry/gate.py coverage.json`; `python -m mypy`; `python ci/check_prose_watchlist.py` | — | — | a failing run |

## Refuted

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| R1 | A change other than adding a term on the empty state | refuted | D1 (`first_change_adds_term`) | std | — (new) | — |
| R2 | Reaching the empty state from a state with a term; a non-empty sequence from the empty state to itself | refuted | D2 (`empty_never_returned`, `no_cycle_at_empty`) | std | 6:R5 (telling the names apart again) replaced | — |
| R3 | A sequence of changes to a result shorter than its size | refuted | D4 (`fewest_changes7_lower`) | std | 6:R8 re-proved with the size alone | — |
| R4 | A well-formed state that is not a result | refuted | D5 (`result7_iff`) | std | 6:R9 re-proved from the empty beginning, the empty state added | — |
| R5 | A change that keeps the size, or the round, where it was | refuted | D4(v) (`Step7.size_step`, `Reach7.size_parity`; `changes_keeping_the_round: 0`) | std | 6:R10 survives through the maps and re-proved for the term | — |
| R6 | A shortest sequence containing a removal or an identification | refuted | D4(vi) (`shortest_are_additions`) | std | — (new) | — |
| R7 | Two results with a term that do not reach each other; two results neither of which reaches the other | refuted | D9 (`reach7_symm`, `reach7_total`) | std | 6:R12 survives on states with a term | — |
| R8 | A rewriting barred by the names: the two readings of sameness differing | refuted | D12 | — | 1:C4's second reading loses its object | — |
| R9 | The sixth's cost as the fewest changes here | refuted | D13 (`sixth_cost_fails`) | std | 6:D8 does not survive | — |
| R10 | A result reached by no sequence; a result with no shortest sequence | refuted | D5, D10 (`reach7_by_additions`; every count ≥ 1) | std | — | — |

## Does not follow

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| N1 | Anything about the asserting: every one of the eighteen statements tested, "at least one term" included | do not follow (derived from D5; computed witnesses) | `follows_*.csv`, `summary.json` (`statements_that_do_not_follow`) | — | 6:N3's "at least one term" does not survive as everywhere-true | a listed witness not being a result |
| N2 | That there is a term; exactly two; at least two | do not follow (computed witnesses: rounds 0, 1, 2, 3) | `follows_*.csv` | — | 6:N4 with the empty state as a witness | — |
| N3 | Growth: that terms, or assertions, must be added or must stay | does not follow (witnesses: the empty state; one change each way from every result with a term) | `added_*.csv`, `summary.json` (`changes_lowering`) | — | 6:N7 survives through the maps | — |
| N4 | That a result is reached by one sequence, or finitely many; that results of one round have equally many shortest sequences | do not follow (derived: infinitely many for every result with a term, D9; computed counts 1, 1, 2, 3, 8) | Lean `Reach7.unbounded`; `results_*.csv` | std | 6:N8 survives with new witnesses; the empty state is reached by one sequence | — |
| N5 | That results of one round with equally many terms have equally many changes | does not follow (D3: 6 for `a b; nothing asserted`, 7 for `a b; bra`) | column `changes` of `results_*.csv` | — | 6:N9 survives | — |
| N6 | That a multiplicity, the number of terms, the total, the size or the fewest classes never falls; that no `xrx` stays asserted | refuted (witnesses; 29 602 / 42 563 / 29 602 / 72 165 / 1 161 / 12 783 changes in the 5-term run) | `summary.json` (`changes_lowering`); `tests/test_seventh_follows_invariants.py` | — | 6:N13 survives through the maps | — |
| N7 | That a state is contained in its outcome; that a sequence carries every assertion somewhere | refuted (witness: `a; ara` and its removal) | `attempts_bound2_rounds4.jsonl` | — | 6:N14 survives through the maps | — |
| N8 | The sixth's notions of `bra`, the names, the given assertion and the destroyed givens | without object | — | — | 6:N1, 6:N2, 6:C2′, 6:D1, 6:D7, 6:D8's `lost` without object | — |
| N9 | That reachability among the results with a term is one-way, or that two results can be incomparable | refuted / follows (D9) | Lean `antisymm_fails7`, `reach7_total` | std | 6:N12 survives on states with a term | — |
| N10 | That the beginning is returned to, or has a cycle | refuted (D2) | Lean `reach7_empty_iff`, `no_cycle_at_empty` | std | — (new; the sixth's beginnings were returned to) | — |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would settle it |
|---|---|---|---|---|---|---|
| O1 | A closed form for the number of shortest sequences reaching a result with two or more terms | open: computed per result within the bound (K7), exact there (D10); one for one-term results (D11) | `results_*.csv` | — | 6:O5 restated from the empty beginning | a formula agreeing with every computed count |
| O2 | Results beyond the declared bounds, listed | open: the frontier exported (both parts); the census counts at 6 terms; the two-term rounds in closed form (D11) | `frontier_*.csv`, `summary.json` | — | 6:O3 | a larger run |
| O3 | Lean statements of D10's completeness, D11's closed form, D12 and D15 | open: proved in the paper, checked by computation | paper §4; `summary.json` | — | 6:O7 | the Lean proofs |
| O4 | The earlier papers' O1 (multiplicity) and O2 (results beyond the bound, counted) | closed by the fourth seed; given by the series for any round (D10) | `prompt/fourth/seed_prompt.md`; D10 `layer_counts`; `rounds_*.csv` | — | 6:O1, 6:O2 | — |
