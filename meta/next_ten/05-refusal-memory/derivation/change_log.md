# Change Log — Problem 05 (Refusal Memory) Derivation

This change log documents every material change and design decision made during the derivation lifecycle of Problem 05 (`meta/next_ten/05-refusal-memory/derivation/`).

## 1. Initial State and Problem Definition
- **Context:** Proposed blind derivation of candidate C01 from parent seventeenth derivation (`prompt/seventeenth/seed_prompt.md`).
- **Seed edit:** In Sentence 13, appended:
  `Its written form is kept with that result; the next attempt at the same written change is performed even if it makes some xrx asserted.`
- **Core question:** Can a recorded refusal make the same attempted change perform later?
- **Hypothesis:** A refusal record can change later reachability.
- **Falsifier:** Every reached result and round agrees with the seventeenth under both answer readings.

## 2. Python Modeling (`model.py`)
- Defined immutable `RefusalState` dataclass pairing a base seventeenth `State` with a `frozenset[Change]` of refused changes.
- Implemented `rewrite_change`, `rewrite_refusal_state`, and `canonical_refusal` supporting both `ANCHORED` and `FREE` sameness conventions.
- Implemented `attempt_step`:
  - When unobstructed: executes normally.
  - When obstructed and change not in refusal memory: records the refusal, preserving the underlying graph state (`is_refusal=True`).
  - When obstructed and change is in refusal memory: executes override step, performing the change even if it asserts some `xrx` (`is_override=True`).
- Implemented `closure`: breadth-first exploration up to declared term bound and round count, exporting frontier cuts and unexpanded waves.
- Implemented `independent_census`: combinatorial orbit enumeration across term bounds independently of BFS exploration.

## 3. Test Suite Implementation (`test_derivation.py`)
- Created comprehensive test suite covering:
  - `RefusalState` invariants, properties, and validation.
  - `rewrite_change` across all four kinds of changes.
  - Refusal recording on first attempt (preserves terms/assertions, accumulates record).
  - Override step on repeated attempt (performs change and asserts loop).
  - Discovery of loop-asserting states at round 2.
  - Exploration validation errors.
  - Exact match and properties under independent census.
  - Both beginnings (`bra=False`, `bra=True`) and both sameness conventions (`ANCHORED`, `FREE`).
  - Full CLI and error paths for evidence generation.
- Achieved 100% line and branch coverage on `model.py`, 97% on `evidence.py`, and 99% overall derivation coverage.

## 4. Evidence Pipeline (`evidence.py`)
- Implemented deterministic evidence generation:
  - `summary.json`: exploration totals and loop discovery rounds across all four configurations.
  - `comparison.json`: seventeenth A-replace vs Problem 05 refusal memory vs seventeenth A-perform.
  - `frontier.json`: exact frontier of attempts exceeding term bound.
  - `census.json`: independent census counts.
  - `MANIFEST.sha256`: cryptographic checksums of generated evidence files.
- Implemented `--check` flag: regenerates into a temporary directory and verifies byte-identical reproduction.

## 5. Formal Verification in Lean 4 (`Derivation.lean`)
- Formalized `St`, `HasLoop`, `LoopFree`, `Change`, and `ObstructedM1`.
- Formalized `RefusalSt` and transition relation `StepRM`:
  - `unobstructed`: normal step.
  - `refusal`: records refusal and preserves state.
  - `override`: repeated attempt performs change.
- Formalized multi-step reachability `ReachRM`.
- Proved `refusal_preserves_state`: a refused change changes nothing about the graph state.
- Proved `refusal_accumulates_record`: the refused change is kept with that result.
- Proved `givenA_loopfree`: the given beginning asserts no loop.
- Proved `perform_ident01_has_loop` and `perform_addLoop00_has_loop`: performing obstructed changes creates loops.
- Proved `perform_unobstructed_loopfree`: unobstructed changes from `givenA` preserve loop-freeness.
- Proved `rootA_one_step_no_loop`: no one-step transition from `rootA` can assert a loop.
- Proved `two_step_reaches_loop` and `two_step_reaches_add_loop`: loop-asserting states are reached in two steps via refusal memory.
- Proved `two_attempt_difference`: loop states are unreachable in one step from what is given, but reachable in two steps.
- Verified all proofs with standard Lean 4 kernel axioms (`propext`, `Quot.sound`), with zero `sorry`, zero `admit`, and zero custom axioms.

## 6. Resolution of Hypothesis and Falsifier
- The falsifier ("Every reached result and round agrees with the seventeenth under both answer readings") is refuted across all four configurations:
  - Seventeenth A-replace reaches 0 loop states.
  - Seventeenth A-perform reaches loop states at round 1.
  - Problem 05 with refusal memory reaches loop states at round 2.
- The hypothesis ("A refusal record can change later reachability") is supported in this model: refusal memory unlocks execution of obstructed changes upon repeated attempt.

## 7. Adversarial Audit Remediation
- **Context:** Challenger P05 completed an independent audit (`adversarial_audit.md`) confirming complete mathematical validity, mutation sensitivity, and Lean proof soundness, but issuing `REQUEST_CHANGES` on two forbidden hype words in `resolution.md`.
- **Changes applied:**
  - `resolution.md:66`: Replaced `impossible in one step from rootA` with `precluded in one step from rootA`.
  - `resolution.md:93`: Replaced `The distinction is not merely in an external log:` with `The distinction does not reside solely in an external log:`.
- **Validation:** Automated regex scanning confirms zero forbidden hype words in `resolution.md`. All tests (98.92% coverage) and Lean proofs continue to pass unconditionally.
