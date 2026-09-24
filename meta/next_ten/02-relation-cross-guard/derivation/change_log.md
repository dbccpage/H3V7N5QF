# Change Log: Problem 02 (relation-cross-guard)

Each material change and design decision for the derivation lifecycle of candidate C21 (`meta/next_ten/02-relation-cross-guard/`).

---

1. **State Model (`model.py`) Created**
   - **Reason**: Implement typed semantics reflecting the seed modification:
     `Adding xry is a change only if xsy is not asserted, and adding xsy is a change only if xry is not asserted.`
   - **Details**:
     - Imported base primitives (`DState`, `canonical`, `empty`, `same`, `perform_base`) from `eighth` and `ninth`.
     - Defined `other_relation(rel)`, `is_cross_guarded(state, rel, x, y)`, and `can_add_assertion(state, rel, x, y)`.
     - Structured `guarded_changes` preserving canonical ordering: IDENTIFY, REMOVE, ADD_TERM, ADD_ASSERTION.
     - Implemented `is_disjoint_support` checking whether `r` and `s` share any asserted pairs.
     - Created `GuardedExploration` and `explore` BFS engine tracking depth, discovery waves, attempts, and bound exits.
     - Added `compare_with_ninth` producing round-by-round differential checks against ninth exploration.
     - Provided constructive witness generators: `witness_blocked_pair`, `witness_identification_bypass` (5 steps), and `witness_two_term_bypass` (6 steps with intermediate term inflation to `n = 3`).

2. **Test Suite (`test_derivation.py`) Created**
   - **Reason**: Verify correctness of guarded semantics, test invariants, and satisfy test coverage requirements.
   - **Details**:
     - 11 unit and integration tests covering:
       - Relation swapping and error handling.
       - Guarded addition gating and blocked pair rejection.
       - Identification and removal admissibility.
       - Invariant preservation: disjoint support under pure additions.
       - 1-term identification bypass in 5 steps.
       - 2-term identification bypass in 6 steps requiring term inflation (`n = 3`).
       - Divergence from ninth derivation at round 3.
       - Deterministic evidence writing and byte-identical `--check` verification.
     - Achieved 98.6% total coverage across all derivation files (98% on `evidence.py`, 99% on `model.py`, 99% on `test_derivation.py`).

3. **Deterministic Evidence Suite (`evidence.py`) Created**
   - **Reason**: Produce reproducible machine-readable evidence artifacts with SHA-256 manifest.
   - **Details**:
     - Generated `run.json`: parameters, summary stats, wave sizes, and exit counts.
     - Generated `frontier.json`: full enumeration of exit attempts hitting term or assertion bounds.
     - Generated `witnesses.json`: concrete witness step-paths for blocked pairs and identification bypasses.
     - Generated `differential.json`: round-by-round differential analysis against ninth derivation and term inflation checks.
     - Generated `disjoint_counts.json`: census of disjoint support states across term and assertion counts.
     - Generated `lean_axioms.txt`: machine-checked Lean 4 axiom dependencies for all theorems.
     - Generated `MANIFEST.sha256`: cryptographic verification of all artifacts.
     - Verified byte-identical reproduction under `python evidence.py --check`.

4. **Lean 4 Formalization (`Derivation.lean`) Created**
   - **Reason**: Provide machine-checked proofs of step embeddings, guard blocking, addition disjointness invariant, and identification bypass.
   - **Details**:
     - Self-contained Lean 4 core formulation (`Derivation02` namespace) without mathlib external dependencies.
     - Defined `NDSt`, `StepG`, and `ReachG`.
     - Proved `StepG.toStep9` and `ReachG.toReach9`: every guarded step embeds into a ninth step.
     - Proved `blocked_pair_cannot_add` and `s_witness_blocks_s`: an assertion cannot be added when the complementary relation is asserted.
     - Proved `reach_add_preserves_disjoint` and `overlapping_unreachable_by_additions`: additions preserve disjoint assertion support; overlapping states are unreachable by pure additions.
     - Proved `identification_bypasses_guard`: explicit 5-step sequence reaching `1::0-0*1|0-0*1` via term addition, disjoint assertion, and identification.
     - Verified: 0 sorry, 0 admit, 0 declared axioms; only standard core axioms `propext` and `Quot.sound` on identification theorems.

5. **Formal Resolution (`resolution.md`) Delivered**
   - **Reason**: Formally resolve the proposal hypothesis and falsifier from `why.md`.
   - **Details**:
     - Falsifier status: Falsified at round 3 (ninth reaches 8 states, guarded reaches 7 states; difference `{"1::0-0*1|0-0*1"}`).
     - Hypothesis status: Confirmed. Addition independence is broken (disjoint support invariant); bypass by identification is verified with cost elevation (+2) and term inflation for `n >= 2`.

6. **Ledger and Paper Delivered (`claim_ledger.md`, `paper.md`)**
   - **Reason**: Full research record maintaining source status discipline (given, chosen, derived, computed, refuted, open) and claim hygiene.

7. **Canonical Status Normalization (`claim_ledger.md`, `paper.md`)**
   - **Reason**: Ensure strict adherence to single canonical source status tokens (no compound statuses).
   - **Details**:
     - Normalized status of `D6_guard` (Term inflation effect) from `derived + computed` to single canonical token `derived`.
     - Moved computation reference into the Evidence column (`computed check in evidence/differential.json`).
     - Aligned notion table in `paper.md` accordingly.
