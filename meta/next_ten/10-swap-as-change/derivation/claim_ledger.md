# Claim Ledger: Problem 10 (swap-as-change)

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**.  
Parent derivation: `paper/ninth/` (`code/ninth/`, `lean4/Ninth/`, `evidence/ninth/`).  
Formalization: `meta/next_ten/10-swap-as-change/derivation/Derivation.lean` (`Seed.Problem10`), on the aggregate `(n, total_r, total_s)` projection.  
Model and tests: `meta/next_ten/10-swap-as-change/derivation/model.py`, `test_derivation.py`.  
Evidence: `meta/next_ten/10-swap-as-change/derivation/evidence/` (`MANIFEST.sha256`).

---

## 1. Given

| ID | Statement | Status | Evidence | Re-check | What would falsify it |
|---|---|---|---|---|---|
| G1 | Terms are written with letters. An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. | given | `meta/next_ten/10-swap-as-change/seed_prompt.md` | 9:G2⁗ no change | A seed sentence dropping multiplicity or naming a third relation |
| G2 | Nothing is given: to begin with there are no terms and nothing is asserted. | given | `meta/next_ten/10-swap-as-change/seed_prompt.md` | 9:G3″ no change | A seed sentence naming an initial term or assertion |
| G3 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion; exchanging the relations. Nothing else is a change. Identifying two terms replaces both by one term in every assertion. Exchanging the relations replaces every `xry` with `xsy` and every `xsy` with `xry`, preserving each multiplicity. | given | `meta/next_ten/10-swap-as-change/seed_prompt.md`, `diff.patch` | Replaces Ninth's four kinds with five kinds | A seed sentence omitting exchanging relations or naming a sixth kind |
| G4 | Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. Two results that differ only in how their terms are written are the same result. | given | `meta/next_ten/10-swap-as-change/seed_prompt.md` | 9:G9 no change | A seed sentence altering the definition of sameness |
| G5 | Attempt 100 changes along each alternative, finishing earlier changes on every alternative before later ones. Do not invent a change to reach 100. If the alternatives exceed what can be completed, declare a finite bound, export the exact frontier, and prove what is complete within it. Any outcome is valid. | given | `meta/next_ten/10-swap-as-change/seed_prompt.md` | 9:G11–G14 no change | A seed sentence requiring invention of changes |

---

## 2. Chosen

| ID | Statement | Status | Evidence | Re-check | What would falsify it |
|---|---|---|---|---|---|
| C1 | Asserted means multiplicity at least 1; a full state consists of terms and a multiplicity per ordered pair in each relation, without names. | chosen | `model.py` (`DState`); Lean `NDSt` retains only total counts | 9:C1′ no change | A seed sentence interpreting asserted as a boolean flag |
| C2 | The chosen reading of exchanging the relations: a swap counts as a change only when it changes the exact written state (`state.r != state.s`). The unchosen reading: allow self-swap as a counted step on symmetric states. | chosen | `model.py` (`changes(allow_self_swap=False)`); Lean `Step10.swap` applies this rule on aggregate counts only | Proposal candidate C17 | A seed sentence specifying that identity swaps are counted |
| C3 | Fewest additions first ordering: identifications, removals, swap (0 additions), followed by adding a term, then adding assertions in `r` and `s` (1 addition). | chosen | `model.py` (`changes`) | Extends 9:C6 with swap among 0 additions | A seed sentence specifying a different priority order |
| C4 | Bound and scope of finite exploration: at most 2 terms, 4 rounds, keeping all results up to 2 assertions per relation for all-pairs shortest path analysis. | chosen | `model.py`, `evidence.py` | Declared finite bound in `plan.md` | Exploration exceeding declared memory or time limits |

---

## 3. Derived

| ID | Statement | Status | Evidence | Re-check | What would falsify it |
|---|---|---|---|---|---|
| D1 | Exchanging relations is an involution: `swap(swap(s)) = s`, preserves `n`, total multiplicity `m`, size (`size(swap(s)) = size(s)`), and well-formedness. | derived | Lean `swap_involution`, `swap_size`, `swap_wf`; `test_swap_involution` | 9:D4 re-proved | An instance where swapping twice alters terms or multiplicities |
| D2 | Every full-state change preserves well-formedness and increases size by at most 1. | derived | Per-pair step analysis in `paper.md` §3; Lean `Step10.wf`, `Step10.size_le` on aggregate counts; `test_perform` | Extends 9:D3 with swap case | A change producing an ill-formed state or increasing size by > 1 |
| D3 | Any sequence of changes reaching `g` from `empty9` requires at least `g.size` changes. | derived | Size argument in `paper.md` §4; Lean `fewest_changes10_lower` on aggregate counts | Re-proved from the step-size bound | A sequence from `empty9` reaching `g` in fewer than `g.size` changes |
| D4 | Additions alone reach every well-formed full state from `empty9` in `g.size` changes. | derived | Per-pair construction in `paper.md` §4; Lean `reach10_by_additions` on aggregate counts | 9:D4 rechecked | A well-formed state unreachable by additions |
| D5 | Fewest changes from `empty9` to `g` is exactly `g.size`, identical to Ninth. All BFS exploration rounds from `empty9` equal Ninth's rounds. | derived | Upper and lower bounds in `paper.md` §4; Lean `fewest_changes10_empty` on aggregate counts; `model.compare_with_ninth` | Full-state construction and size bound | A state reached from `empty9` in a round different from Ninth |
| D6 | Shortest sequences from `empty9` contain no swaps and are identical in count to Ninth. | derived | `model.count_shortest_sequences`; `test_exploration_comparison_with_ninth` | Follows from swap adding 0 to size | A shortest sequence from `empty9` containing a swap |
| D7 | For any asymmetric state `s` (`s.swap ≠ s`), Problem 10 reaches `s.swap` in 1 change, whereas Ninth requires at least 2 changes. | derived | Seed swap step and size-parity argument in `paper.md` §5; Lean `swap_cost_reduction` for unequal aggregate counts; `test_cost_reductions_and_formula` | New to Problem 10 | A sequence in Ninth reaching `s.swap` in 1 change |
| D8 | Any shortest path between arbitrary states uses at most one swap. | derived | `model.verify_swap_reduction_formula`; commutation of swap with Ninth changes | New to Problem 10 | A pair requiring two swaps on every shortest path |
| D9 | Closed-form reduction formula: $\text{dist}_{10}(S, T) = \min(\text{dist}_9(S, T), 1 + \text{dist}_9(\text{swap}(S), T))$ holds for all state pairs. | derived | `model.verify_swap_reduction_formula`; `reduction_formula_verification.json` | New to Problem 10 | A pair where the formula fails |
| D10 | What does not follow: swap does not reduce shortest path cost from `empty9`; Ninth costs are not preserved between arbitrary asymmetric pairs. | derived | Full-state argument and witnesses in `paper.md` §§4–5; Lean `what_does_not_follow_empty_cost_reduction`, `what_does_not_follow_ninth_costs_equal` on aggregate counts | Refutation by legal witnesses | A reduction from `empty9` or an equality for all asymmetric pairs |

---

## 4. Computed

| ID | Statement | Status | Evidence | Re-check | What would falsify it |
|---|---|---|---|---|---|
| C_EXP | BFS exploration from `empty9` up to bound 2 terms and 4 rounds yields 36 canonical states with identical depths and new results per round as Ninth (`[1, 1, 3, 9, 22]`). | computed | `exploration_summary.json`, `comparison_with_ninth.json` | Re-checks Ninth exploration beside Tenth | A discrepancy in state depths or counts |
| C_ATT | Exploration of Problem 10 performs 87 total attempts (8 more than Ninth's 79) across 4 rounds due to swap attempts on asymmetric states. | computed | `comparison_with_ninth.json` | Re-checked by test suite | Total attempts differing from 87 |
| C_RED | Among 32 canonical states with `n ≤ 2, m ≤ 2` (1024 pairs), exactly 220 pairs exhibit strictly shorter paths under Problem 10 than under Ninth, with maximum cost reduction of 3. | computed | `cost_reductions_sample.csv`, `reduction_formula_verification.json` | Checked by all-pairs BFS | A pair where cost reduction does not match |
| C_FORM | The closed-form reduction formula $\text{dist}_{10}(S, T) = \min(\text{dist}_9(S, T), 1 + \text{dist}_9(\text{swap}(S), T))$ holds on all 1024 state pairs. | computed | `reduction_formula_verification.json`; `test_cost_reductions_and_formula` | Exhaustive check | Any pair with a discrepancy |
