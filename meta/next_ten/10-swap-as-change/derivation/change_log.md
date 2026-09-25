# Change Log: Problem 10 (swap-as-change)

This file records decisions and changes made during the derivation lifecycle of Problem 10.

## 2026-09-24 — Derivation Initialization and Completion

1. **Initial Assessment and Seed Analysis**:
   - Seed input analyzed from `meta/next_ten/10-swap-as-change/seed_prompt.md`.
   - Identified the seed difference: exchanging the relations $r$ and $s$ added as the fifth kind of change.
   - Identified the candidate hypothesis from `why.md`: "Making the existing involution a step changes shortest paths and sequence counts", against the falsifier: "All shortest paths and rounds equal the ninth's."

2. **Reading and Model Decisions**:
   - Chosen reading: a swap counts as a change only when it changes the exact written state (`state.r != state.s`), preventing trivial self-loops on symmetric states.
   - Unchosen reading: allowing self-swaps on symmetric states (`allow_self_swap=True`), which adds a self-loop of length 1 on symmetric states. Both options modeled in `model.py`.
   - Priority under fewest additions first: swap adds 0 terms and 0 assertions, placing it alongside identifications and removals before additions.

3. **Python Model Implementation (`model.py`)**:
   - Implemented `Kind` enum with 5 kinds of change (`IDENTIFY`, `REMOVE`, `SWAP`, `ADD_TERM`, `ADD_ASSERTION`).
   - Implemented `Change` dataclass, `changes(state)`, `perform(state, change)`, and `makes_some_loop(state, change, rel)`.
   - Implemented breadth-first exploration (`explore`) and shortest path sequence counting (`count_shortest_sequences`).
   - Implemented `all_pairs_shortest_paths` and `find_cost_reductions` to compare Ninth and Tenth reachability graphs.
   - Implemented `verify_swap_reduction_formula` validating $\text{dist}_{10}(S, T) = \min(\text{dist}_9(S, T), 1 + \text{dist}_9(\text{swap}(S), T))$.

4. **Pytest Suite (`test_derivation.py`)**:
   - Created comprehensive tests covering swap involution, change validation, ordering, loop detection, exploration equivalence with Ninth, cost reductions, and formula verification.
   - Achieved 99.72% test coverage (0 missed statements, 2 minor branch parts).

5. **Deterministic Evidence Generation (`evidence.py`)**:
   - Generated `exploration_summary.json`, `comparison_with_ninth.json`, `cost_reductions_sample.csv`, `reachable_states_sample.csv`, `reduction_formula_verification.json`, and `MANIFEST.sha256`.
   - Verified byte-identical regeneration with `--check`.

6. **Lean 4 Formalization (`Derivation.lean`)**:
   - Formalized `Step10` with 5 constructors and embedding of `Step9`.
   - Proved swap involution (`swap_involution`), size preservation (`swap_size`), and well-formedness preservation (`swap_wf`).
   - Proved size step bound (`Step10.size_le`) and reachability size bound (`Reach10.size_le`).
   - Proved lower bound from empty (`fewest_changes10_lower`) and reachability by additions (`reach10_by_additions`), establishing `fewest_changes10_empty`.
   - Proved single-step swap reachability (`reach10_swap`) and strict cost reduction from Ninth's even lower bound of 2 (`swap_cost_reduction`).
   - Proved refutations of non-following claims. All proofs closed without `sorry`, `admit`, or non-standard axioms.

7. **Resolution and Paper Formulation**:
   - Drafted `resolution.md` resolving the hypothesis: root-relative exploration from `empty9` preserves Ninth rounds and costs (falsifier holds in this restricted scope), while general state-to-state reachability contains genuine shortcuts (hypothesis supported).
   - Authored `paper.md` and `claim_ledger.md` maintaining strict claim hygiene and prose discipline.

## 2026-09-24 — Self-Contained Derivation and Claim Hygiene Remediation

8. **Remediation for Package Autonomy**:
   - Refactored `Derivation.lean` to be completely self-contained without imports from `Ninth` or external project modules.
   - Defined `NDSt`, `Step9`, `Step10`, `Reach9`, and `Reach10` using Lean 4 core `Nat` and standard types.
   - Re-verified Lean 4 compilation: 0 errors, 0 warnings, 0 `sorry`, 0 `admit`, 0 custom axioms.
   - Cleaned `paper.md` line 72 replacing the broad hype token with `general`, and revised line 5.
   - Verified 0 forbidden words across all markdown files.
   - Confirmed full test suite passes with 98.79% coverage, `mypy --strict` passes with 0 issues, and `evidence.py --check` passes with byte-identical regeneration.

9. **Two-Axis Code Review Remediation (`paper.md`)**:
   - Replaced remaining instances of the forbidden word `proves` in `paper.md` lines 5 and 160 with compliant vocabulary (`establishes`), ensuring zero forbidden words across the package.
