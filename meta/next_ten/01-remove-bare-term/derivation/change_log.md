# Change Log: Problem 01 (Remove Bare Term)

This document logs all architectural and theoretical decisions made during the derivation lifecycle for Problem 01 under `meta/next_ten/01-remove-bare-term/derivation/`.

## 1. Initial Inspection and Foundation
- **Date**: 2026-09-24
- **Event**: Received task dispatch for Problem 01 (`meta/next_ten/01-remove-bare-term`).
- **Diff Analysis**: Inspected `diff.patch` against parent Seventh seed. Identified that paragraph 3 adds: *"removing a term that names no assertion. Nothing else is a change. ... Removing a term that names no assertion deletes that term and nothing asserted."*
- **Hypothesis and Falsifier Identification**: Extracted stakes from `why.md`:
  - Hypothesis: *"A bare-term removal destroys the empty state's one-way reachability."*
  - Falsifier: *"No nonempty result reaches the empty beginning within two changes."*

## 2. Model Design and Transition Semantics (`model.py`)
- **Date**: 2026-09-24
- **Decision**: Implemented `Kind` enum with 5 kinds of changes: `IDENTIFY`, `REMOVE`, `ADD_TERM`, `ADD_ASSERTION`, `REMOVE_BARE_TERM`.
- **Decision**: Defined bare term condition: a term $t \in \{0, \dots, n-1\}$ is bare iff for all $y \in \{0, \dots, n-1\}$, $M(t, y) = 0$ and $M(y, t) = 0$.
- **Decision**: Implemented bare-term removal: when $t$ is removed, $n \to n - 1$, terms $> t$ shift to $u - 1$, and assertion multiplicities are preserved. For $n = 1$, returns the canonical `empty` state.
- **Decision**: Established order of attempted changes: fewest additions first (0 additions: identifications, assertion removals, bare-term removals; then 1 addition: add term, add assertion).
- **Decision**: Integrated combinatorial Burnside orbit counting using the cycle index of $S_n$ on directed pairs to serve as an independent completeness oracle.

## 3. Test Suite Implementation and Coverage (`test_derivation.py`)
- **Date**: 2026-09-24
- **Decision**: Authored comprehensive test suite covering:
  - Input validation and state creation invariants.
  - Identification, assertion removal, term addition, assertion addition, and bare-term removal semantics.
  - The 2-step cycle `empty -> oneTermBare -> empty`.
  - Concrete refutation of the candidate falsifier.
  - BFS exploration waves, frontier exits, and log generation.
  - Independent Burnside orbit counts vs BFS wave discovery.
  - Mutation tests verifying that forbidding bare-term removal restores empty state in-degree 0.
- **Result**: Achieved 98.70% line and branch coverage (exceeding the 95% threshold) with all 16 tests passing.

## 4. Formalization in Lean 4 (`Derivation.lean`)
- **Date**: 2026-09-24
- **Decision**: Formalized `State` structure with `@[ext]`, well-formedness predicate `WF`, and bare-term removal transition.
- **Decision**: Formally proved well-formedness preservation (`removeBare_wf`) and well-formedness of term addition (`addTerm_wf`).
- **Decision**: Formally established the existence of the 2-step cycle (`two_step_cycle`), that empty returns in 2 changes (`empty_returns_in_two_steps`), the refutation of the falsifier (`falsifier_refuted`), and that the empty state has positive in-degree (`empty_state_in_degree_positive`).
- **Verification**: Verified using `lean meta/next_ten/01-remove-bare-term/derivation/Derivation.lean`. Completed with exit code 0, zero warnings, zero errors, zero `sorry`, zero `admit`, and zero declared axioms.

## 5. Evidence Generation and Verification (`evidence.py`)
- **Date**: 2026-09-24
- **Decision**: Built deterministic evidence generator emitting `frontier.txt`, `waves.json`, `cycle_witness.json`, `resolution.json`, `differential_checks.json`, and `MANIFEST.sha256`.
- **Decision**: Implemented byte-identical regeneration verification via `--check` flag comparing against fresh temporary generation.
- **Verification**: Ran `python evidence.py` and `python evidence.py --check`; verified byte-identical match.

## 6. Formal Resolution and Documentation (`resolution.md`, `paper.md`, `claim_ledger.md`)
- **Date**: 2026-09-24
- **Decision**: Synthesized detailed resolution document `resolution.md` resolving hypothesis as supported and falsifier as refuted.
- **Decision**: Drafted full scientific paper `paper.md` adhering strictly to Claim Hygiene (no forbidden hype words, precise narrow claims, summary checklist included).
- **Decision**: Built claim ledger `claim_ledger.md` mapping all 11 claims to verification evidence.

## 7. Remediation and Claim Hygiene Standardization
- **Date**: 2026-09-24
- **Event**: Remediated status discipline and claim hygiene.
- **Decision**: Converted compound statuses `derived / computed` in `claim_ledger.md` (claims P01-4, P01-5, and P01-7) to single-token `derived` per Bookkeeping Rule 1, maintaining computational verification references in the Evidence column.
- **Decision**: Remediated `adversarial_audit.md` (lines 110, 124, 130) to eliminate the flagged forbidden verb and replace with `shows in this model`, and neutralized scan listings.
- **Verification**: Verified 0 forbidden hype words across all 5 markdown files in the package.
- **Verification**: Confirmed `lean meta/next_ten/01-remove-bare-term/derivation/Derivation.lean` compiles with exit code 0.
