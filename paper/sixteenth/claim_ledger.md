# Claim ledger, sixteenth derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/sixteenth/paper.md`). Lean names in namespace `Seed.Sixteenth` are in
`lean4/Sixteenth/`; names in `Seed.Ninth`, `Seed.Fourteenth` and `Seed.Seventh`
are the earlier derivations'. Axiom report: `evidence/sixteenth/lean_axioms.txt`;
"std" means the theorem depends on `propext`, `Classical.choice`, `Quot.sound`
only (some on a subset); "none" means no axioms. No `sorry`, `admit`, or
declared axiom occurs anywhere in `lean4/` (scanned by
`code/sixteenth/leanreport.py`).

The column **Re-check** says how a cited earlier result was re-checked from
the sixteenth seed and whether it *survives the record feeding back*: *no
change* (the statement mentions no record), *through the maps* (`RSt.toNDSt`,
`NDSt.ofRSt`, `Step16.proj`, `Add9.embed`, `Step9.embed`), *re-proved*,
*computed again* (the sixteenth exploration against the ninth's on the
empty-record results), *by construction* (definitional, disclosed), or "—" for
a claim new to this derivation.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The ninth seed, word for word | given | `diff` of `prompt/sixteenth/seed_prompt.md` against `prompt/ninth/seed_prompt.md` | — | 9:G* no change | a sentence of the sixteenth seed that differs elsewhere |
| G15′ | After every change, record what that change leaves; a leftover is written neither `xry` nor `xsy`; a recorded leftover `xℓy` may be admitted, adding the assertion `xry` or the assertion `xsy`; an unadmitted leftover is not an assertion | given | `prompt/sixteenth/seed_prompt.md`; `diff` against `prompt/fourteenth/seed_prompt.md` (one sentence replaced) | — | 14:G15 replaced | a sentence keeping the leftover inert, or admitting a merge writing |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C-R1 | A state is a ninth state with its record (a count of unadmitted leftovers per ordered pair); a removal records one leftover of its pair, additions record nothing, the merge writing is on the change and not admissible; an admission is a change of the fourth kind that consumes one leftover and adds `xry` or `xsy`; an identification carries the record with the terms (the merged counts add up); sameness rewrites all three functions | chosen | `code/sixteenth/state.py`, `code/sixteenth/changes.py`, `code/sixteenth/leftover.py`; Lean `RSt`, `RSt.remove`, `RSt.admitLeftover`, `RSt.identify`, `Step16` | — | 14:C-F1 kept for the writings; 9:C5⁗ applied to the record | a seed sentence keeping the record off the state, making admission free, or bounding a pair's leftovers |
| C-R2 | Unchosen, kept: the record is a set | chosen (unchosen) | `Reading.SET`; `alternatives.json` | — | — | — |
| C-R3 | Unchosen, kept: an identification drops the leftovers naming a merged term | chosen (unchosen) | `Reading.DROP`; `alternatives.json` | — | — | — |
| C8′ | Bounds: 3 terms / 8 rounds; 4 / 7; 2 / 10; log 2 / 3; reachability 3 / 5 along 7; alternatives 2 / 6, their reachability 2 / 5 along 8; counts to 4 terms and weight 8 | chosen | `code/sixteenth/evidence.py` `Plan`; `summary.json` `plan` | — | 9:C8′ lowered in terms, raised in the alternatives | — |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D1 | Removing `xqy` and admitting its leftover back into `q` is the identity on the state, record included | derived + computed | Lean `remove_admit_same` (`remove_add9` on the ninth state, the record lowered back); `records.same_relation_not_identity` empty in every run (7 494 removals checked at 3 terms / 8 rounds); `given.json` `same_relation` | std | — (14:D6 fails by it, §9) | a removal whose leftover admitted back gives another state |
| D2 | Admitting the leftover into the other relation gives a result different from the start and from the direct addition; the two outcomes have the same ninth state | derived + computed; the last clause by construction | Lean `remove_admit_other_ne`, `remove_admit_other_ne_direct`; `remove_admit_other_st` is `rfl` (definitional, disclosed); `records.other_relation_same_as_start`, `other_relation_same_as_direct` empty (up to rewriting); `given.json` `other_relation` | std | — | a rewriting carrying the outcome onto the start or onto the direct addition |
| D3 | The fewest changes to a result is its potential, the size plus twice the record; every change moves the potential by exactly one, up for a term, a direct assertion and a removal, down for an admission and an identification; parity | derived + computed | Lean `potential_addTerm`, `potential_addAssertion`, `potential_remove`, `potential_admit`, `potential_identify`, `Step16.potential_step`, `Reach16.potential_le`, `fewest_changes16_lower`, `reach16_record`, `reach16_by_additions`, `fewest_changes16`, `Reach16.potential_parity`; `round_not_potential`, `potential_not_moved_by_one`, `direction_mismatch` empty in every run; `rounds_agreeing_with_unbounded_series` all true | std | 9:D4 re-proved: survives on the empty-record results (`fewest_changes16_of_empty_record`), fails off them (`ninth_cost_fails_off_empty_record`) | a result whose round is not its potential; a change moving it by other than one |
| D4 | No shortest sequence from the empty beginning admits or identifies; an assertion arriving by admission costs three changes where a direct addition costs one | derived + computed | Lean `Rise16`, `Fall16`, `Step16.rise_or_fall`, `ReachD.potential`, `Reach16.toReachD`, `no_fall_on_shortest16`, `admission_costs_three`; `count_shortest_sequences16` refuses a round-raising change that lowers the potential; `given.json` `admission_costs_three` (potentials `0, 1, 2, 3, 2` along the route) | std | 9:D4(vi) re-proved: fails as "additions only", survives as "no fall" | a shortest sequence from the empty state containing an admission |
| D5 | The mass (both totals plus the record) never falls along a change; the has-a-term criterion fails; reachability among the states with a term is one-way | derived + computed | Lean `mass_addTerm`, `mass_addAssertion`, `mass_remove`, `mass_admit`, `mass_identify`, `Step16.mass_le`, `Reach16.mass_le`, `has_term_criterion_fails16`, `one_way16`; `records.mass_fell`, `diagonal_mass_fell` empty in every run; `given.json` `mass` | std | 9:D8, 9:D9 re-proved: do not survive (witness `ara` → one term) | a change lowering the mass; a sequence from `ara` once to the one-term state asserting nothing |
| D6 | A result reaches another exactly when the first is empty or some map of its terms into the other's carries at most each pair's mass onto it | computed (the criterion against search); necessity derived through the mass, sufficiency from the empty state and by admitting every leftover | `code/sixteenth/reach.py` `carries`; `reach_bound3_rounds5.csv`, `summary.json` `reachability` (`criterion_agrees_with_search` on 27 889 pairs; 17 624 pairs the ninth admits and this seed refuses; none the reverse; 4 227 pairs the two invariants admit and the criterion refuses); Lean `Reach16.mass_le`, `reach16_by_additions`, `reach16_admit_all` | std | 9:D8 computed again: the ninth's criterion admits every pair this seed admits and more | a pair the criterion admits with no sequence within a larger bound, or the reverse |
| D7 | The record grows without bound; the one-term results of round `k ≥ 1` number `(⌊(k−1)/2⌋+1)(⌈(k−1)/2⌉+1)` | computed (closed form checked against the exploration and the series in every run) | `code/sixteenth/orbits.py` `one_term_round_count`; `one_term_rounds_equal_closed_form` true in every run; `counts.csv` | — | 9:D11 replaced (the one-term count `k` does not survive) | a round whose one-term results differ from the closed form |
| D8 | Every well-formed state is a result; the ninth's results are exactly the empty-record results at the ninth's rounds and sequence counts; results are jointly free with any record; the count is the orbit count with a third factor `1/(1 − x^{2L})`, its record-free part the ninth's, not a product from two terms on | derived + computed | Lean `result16_iff`, `results_ninth_iff16`, `ninth_round_survives`, `results_pair16`, `leftOne_is_new`; `explored_equals_independent_count`, `ninth_derivation.empty_record_results_are_the_ninth_results` true in every run (7 271 / 2 301 / 6 526 empty-record results); `counts.csv`, `empty_record_counts_are_the_ninth_counts`, `count_exceeds_product_for_two_or_more_terms` | std | 9:D5 re-proved with any record; 9:D10 computed again as the record-free part | a well-formed state the exploration misses; a ninth result at another round; an explored count off the series |
| D9 | The feedback does not terminate: remove-then-admit is a two-change cycle at every state with an assertion, a term added and identified away at every state with a term; the ninth's add-then-remove is not a cycle | derived + computed | Lean `cycle2_assert16`, `admit_remove_unbounded`, `cycle2_16`, `identify_addTerm16`, `NSt.identify_addTerm`, `Reach16.unbounded`, `add_remove_ne`, `add_remove_st`; `results_with_a_two_change_cycle` = results − 1 in every run; `given.json` `cycles` | std | 9:D9's cycle survives with other changes; 9:D9's witness (add then remove) does not | a state with a term and no two-change cycle; a bound on the length of sequences to a result |
| D10 | The record is a count per pair carried by the state, not raised by any addition, lowered only by an admission, raised only by a removal; it is not an assertion | derived (the record's moves) + by construction (its place in the state, C-R1) | Lean `record_not_raised_by_addition` (`rfl`, definitional, disclosed), `record_moved_only_by_removal_and_admission`, `admitted_leftover_is_the_assertion`; `given.json` `direct_additions_that_change_the_record` empty | std | 14:D7 re-examined: fails as "not a third multiplicity", survives as "not a third relation" | a change of the four kinds other than a removal raising the record |
| D11 | A leftover left by a removal in `r` is admitted into `s`; the record of a removal does not depend on the relation | derived + by construction (the second clause is `rfl`, disclosed) | Lean `r_leftover_admitted_into_s`; `record_names_no_relation` (definitional); `given.json` `the_fourteenth_witness` (`asb` twice) | std | 14:D5 by construction, now with force | a removal in `r` whose leftover is not admissible into `s` |
| D12 | The exchange of the two relations is a symmetry of the results, the potential and the mass; the record is unchanged by it | derived + computed | Lean `Step16.swap`, `Reach16.swap`, `result16_swap`, `exchange_symmetry16`, `potential_swap`; `given.json` `exchange_keeps_the_record`; `results_*.csv` column `exchange` | std | 9:D16 re-proved | a result whose exchange is not a result |
| D13 | Every change projects to a change of the ninth on the ninth state, an admission to a direct addition; additions and identifications of the ninth embed; a removal of the ninth embeds into a state with one leftover recorded; well-formedness, a term, the first change and the one-way exit from the empty state are as the ninth's | derived | Lean `Step16.proj`, `Reach16.proj`, `Add9.embed`, `AddReach9.embed`, `Step9.embed_identify`, `Step9.embed`, `Step16.wf`, `Step16.nonempty_out`, `Step16.nonempty`, `Reach16.nonempty`, `first_change_adds_term16`, `reach16_empty_iff` | std | 9:D1, 9:D2, 9:D6 through the maps and re-proved | a change of the sixteenth with no ninth projection |
| D14 | Under C-R2 the same-relation identity fails; under C-R3 it holds and the ninth's has-a-term criterion agrees with search on every pair, the carrying criterion not | computed | `alternatives.json` (`same_relation_identity_failures` 10 / 0; `reachability`); `given.json` `set_reading` | — | 9:D8 computed again under C-R3: survives there | a set-reading removal whose admission is the identity everywhere; a C-R3 pair disagreeing with the ninth's criterion |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | Results within the bounds: 10 697 (3 terms, 8 rounds; by terms 1 / 70 / 2 749 / 7 877), 3 033 (4 terms, 7 rounds), 15 561 (2 terms, 10 rounds); of which with an empty record 7 271 / 2 301 / 6 526 = the ninth's; every count equals the independent count; totals by terms up to weight 8: 1, 95, 15 435, 523 915, 5 443 147 | computed | `summary.json`, `results_*.csv`, `counts.csv` | — | 9:K1 computed again as the empty-record part | regeneration gives other numbers |
| K2 | Results per round: 3 terms 1, 1, 3, 9, 32, 121, 490, 1 994, 8 046; 4 terms 1, 1, 3, 9, 33, 125, 529, 2 332; 2 terms 1, 1, 3, 8, 28, 85, 260, 692, 1 742, 4 005, 8 736 (the series with at most two terms); without bound 1, 1, 3, 9, 33, 126, 534, 2 376, 11 285, 56 345, 294 522 | computed | `rounds_*.csv`, `summary.json` | — | 9:K2 computed again (column `new_results_of_the_ninth_seed_within_bound`) | regeneration gives other numbers |
| K3 | Attempts: 53 993 / 13 165 / 97 864, of which admissions 1 472 / 290 / 8 268, every one performed, equal to the formula; changes checked 52 420, among them removals 7 494 / 1 584 / 22 020, checked 52 420 / 13 121 / 91 135, raising 45 202 / 11 403 / 76 138, lowering 7 218 / 1 718 / 14 997 | computed | `summary.json` (`records`) | — | 9:K3 with the admissions added | a run whose totals differ |
| K4 | Full log of 22 attempts at 2 terms and 3 rounds, every one performed, the first the term, each with its leftover writing and whether it is admissible on the outcome | computed | `attempts_bound2_rounds3.jsonl` | — | 9:K4 same shape | an attempt recorded as anything but performed |
| K5 | Frontier: one entry per result with `N` terms whose changes were attempted (1 573 / 44 / 6 729); results of the last round awaiting: 8 046 (190 340 changes), 2 332 (56 754), 8 736 (132 904) | computed | `frontier_*.csv`, `summary.json` | — | 9:K5 computed again | a frontier result with other counts |
| K6 | Reachability within 3 terms and 5 rounds: 10 099 of 27 889 ordered pairs reachable, 596 unordered pairs both ways; the criterion agrees with the search on every pair; the ninth's criterion admits 27 723 | computed | `reach_bound3_rounds5.csv`, `summary.json` (`reachability`) | — | 9:K8 computed again | a disagreement |
| K7 | Shortest sequences: totals 7 665 306 / 516 931 / 163 062 241; 18 / 17 / 21 results with one; every count exact | computed | `results_*.csv`, `summary.json` | — | 9:K7 computed again | a count not exact within the bound |
| K8 | Statements: none of the forty-six about a state holds in every result; none of the six about a change holds of every change | computed | `follows_*.csv`, `summary.json` | — | 9:D14 survives | a statement holding everywhere other than a tautology |
| K9 | Evidence is regenerable: a fresh run reproduces every computed file of `evidence/sixteenth/` byte for byte | computed | `python code/generate_sixteenth.py --check` | — | — | a `--check` reporting a difference |
| K10 | Tests of `code/sixteenth/` plus the fifteen earlier derivations; line and branch coverage of all of `code/` above the gate, every evidence module fully covered; `mypy --strict` clean; the prose watchlist clean, the sixteenth paper's hits in §14; the vacuous-check, definitional-citation and mutation-bite gates clean, the last with a sixteenth panel of twelve fields each biting | computed | `python -m pytest`; `python code/xry/gate.py coverage.json`; `python -m mypy`; `python ci/check_prose_watchlist.py`; `python ci/check_vacuous_checks.py`; `python ci/check_definitional_citations.py`; `python ci/check_mutation_bite.py` | — | — | a failing gate |

## Refuted

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| R1 | A change other than adding a term on the empty state | refuted | D13 (`first_change_adds_term16`) | std | 9:R1 re-proved | — |
| R2 | Reaching the empty state from a state with a term | refuted | D13 (`reach16_empty_iff`) | std | 9:R2 re-proved | — |
| R3 | A sequence to a result shorter than its potential; a shortest sequence with an admission | refuted | D3, D4 (`fewest_changes16_lower`, `no_fall_on_shortest16`) | std | 9:R3 re-proved with the record | — |
| R4 | A well-formed state that is not a result | refuted | D8 (`result16_iff`) | std | 9:R4 re-proved | — |
| R5 | A change that keeps the potential | refuted | D3 (`Step16.potential_step`) | std | 9:R5 re-proved | — |
| R6 | The size as the fewest changes off the empty-record results | refuted | D3 (`ninth_cost_fails_off_empty_record`) | std | 9:D4 does not survive there | — |
| R7 | The has-a-term criterion; mutual reachability among the states with a term | refuted | D5 (`has_term_criterion_fails16`, `one_way16`) | std | 9:D8, 9:D9 do not survive | — |
| R8 | The ninth's add-then-remove as a cycle; a bound on the feedback | refuted | D9 (`add_remove_ne`, `admit_remove_unbounded`) | std | 9:D9's witness does not survive | — |
| R9 | The count as the ninth's count times the record's, from two terms on | refuted | D8 (`count_exceeds_product_for_two_or_more_terms`) | — | 9:R12's shape | — |
| R10 | Clearing a leftover is not one of the four kinds | refuted | D10 (`clearing_is_a_kind16`) | std | 14:D6 does not survive | — |
| R11 | An admission raises the record, or a direct addition changes it | refuted | D10 (`record_moved_only_by_removal_and_admission`) | std | — | — |

## Does not follow

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| N1 | Anything about the asserting (forty-two ninth statements read on the ninth state) or about the record (empty; something recorded; a recorded pair asserted; every recorded pair unasserted) | do not follow (computed witnesses) | `follows_*.csv` | — | 9:N1 survives | a listed witness not being a result |
| N2 | That a change leaves nothing, a pair, a merge, an admissible writing, or is an admission | do not follow (computed witnesses) | `change_statements_that_do_not_follow` | — | 14:K2 with the admission added | — |
| N3 | That the two mass invariants decide reachability | refuted (4 227 pairs) | `summary.json` (`ordered_pairs_the_two_mass_invariants_admit_and_the_criterion_refuses`) | — | — | — |
| N4 | That a result is reached by finitely many sequences | refuted (D9) | Lean `Reach16.unbounded` | std | 9:N4 survives | — |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would settle it |
|---|---|---|---|---|---|---|
| O1 | Results beyond the declared bounds | open: the frontier exported; the series gives every round | `frontier_*.csv`, `counts.csv` | — | 9:O2 | a larger run |
| O2 | A reachability criterion for the set reading C-R2 | open: neither the ninth's nor the carrying criterion agrees with search | `alternatives.json` | — | — | a criterion agreeing with search |
| O3 | The sufficiency half of the carrying criterion in Lean | open: computed on 27 889 pairs; necessity in Lean through the mass | `summary.json` (`reachability`); Lean `Reach16.mass_le` | — | — | the Lean proof |
| O4 | The diagonal mass in Lean | open: computed (`diagonal_mass_fell` empty) | `summary.json` | — | — | the Lean proof |
| O5 | A closed form for the shortest-sequence counts with two or more terms | open: exact counts within the bounds | `results_*.csv` | — | 9:O1 | a formula |
| O6 | Changes commute with rewriting (`rename16`) in Lean | not attempted in Lean; the sameness is implemented and every check is up to it | `code/sixteenth/state.py` `canonical16` | — | 9:D7 not carried over | the Lean proof |
