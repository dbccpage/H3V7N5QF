# Change Log — Problem 06 (Written Budget) Derivation

This change log documents every material change and design decision made during the derivation lifecycle of Problem 06 (`meta/next_ten/06-written-budget/derivation/`).

## 1. Initial State and Problem Definition
- **Context:** Proposed blind derivation of candidate C04 from parent Ninth derivation (`prompt/ninth/seed_prompt.md`).
- **Seed edit:** In Sentence 5, replaced:
  `Nothing is given: to begin with there are no terms and nothing is asserted.`
  with:
  `Nothing is given: to begin with there are no terms and nothing is asserted. Each alternative begins with four changes available; each performed change uses one, an attempt with none available changes nothing, and every result records how many remain.`
- **Core question:** Does a state-carried budget change reachability beyond a study's round bound?

## 2. Python Modeling (`model.py`)
- Defined immutable `BudgetedState` dataclass pairing a canonical Ninth `DState` with an integer budget $b \in \{0, 1, 2, 3, 4\}$.
- Implemented `perform_change`:
  - When $b > 0$, executes the Ninth transition and decrements the budget ($b' = b - 1$).
  - When $b = 0$, returns the unchanged state ($b' = 0$, identity transition).
- Implemented `attempt`: returns `AttemptRecord` tracking whether a change was performed and budget used.
- Implemented `explore`: breadth-first exploration from `(empty, 4)` up to budget exhaustion ($b = 0$).
- Implemented `independent_census_counts`: closed-form count of reachable states per budget based on Ninth orbit formulas and parity:
  - Budget 4 ($k = 0$): 1 state
  - Budget 3 ($k = 1$): 1 state
  - Budget 2 ($k = 2$): 3 states
  - Budget 1 ($k = 3$): 9 states (1 of size 1, 8 of size 3)
  - Budget 0 ($k = 4$): 32 states (3 of size 2, 29 of size 4)
  Total reachable budgeted states = 46.
- Implemented `compare_with_parent`: evaluates wave-by-wave discovery versus Ninth parent BFS.

## 3. Test Suite Implementation (`test_derivation.py`)
- Created comprehensive test suite covering:
  - Budget validation and boundary conditions ($b \in 0..4$, rejection of named states).
  - Canonical form preservation across term permutations.
  - Step consumption and strict budget decrement.
  - Invariant that attempts at budget 0 change nothing.
  - Full exploration wave verification.
  - Exact match between exploration results and independent census.
  - Detailed comparison with Ninth parent derivation.
  - Empirical resolution tests comparing budget waves against parent BFS waves.
  - Full CLI and error handling tests for evidence generator.
- Achieved 100% line and branch coverage on `model.py` and `evidence.py`, and 99.08% overall derivation coverage.

## 4. Evidence Pipeline (`evidence.py`)
- Implemented deterministic evidence generation:
  - `budget_census.json`: census comparison.
  - `parent_comparison.json`: parent BFS comparison.
  - `budgeted_states.csv`: catalog of all 46 canonical budgeted states.
  - `summary.json`: exploration and attempt totals.
  - `MANIFEST.sha256`: cryptographic integrity checksums.
- Implemented `--check` flag: generates into a temporary directory and verifies byte-identical reproduction.

## 5. Formal Verification in Lean 4 (`Derivation.lean`)
- Formalized `BSt`, `emptyB`, and `BSt.WF`.
- Formalized `BStep` and `BReach`.
- Proved `BStep.budget_eq` and `BStep.budget_lt`: every performed change strictly decreases budget by 1.
- Proved `BReach.budget_eq` and `BReach.strictly_decreasing`: sequence of length $n$ decreases budget by $n$.
- Proved `BReach.four_step_max`: every path from `emptyB` has length $n \le 4$.
- Proved `BStep.not_step_at_zero`: no performed change is possible from budget 0.
- Proved `BReach.characterization`: full bidirectional characterization showing that $t$ is reachable from `emptyB` in $n$ steps iff $n \le 4$, $t.\text{budget} = 4 - n$, and `Reach9 empty9 t.state n`.
- Proved bounds on size ($t.\text{state}.\text{size} \le n \le 4$) and terms ($t.\text{state}.T.\text{card} \le 4$).
- All proofs verified without `sorry`, `admit`, or non-standard axioms.

## 6. Resolution of Core Question (`resolution.md`)
- Detailed proof resolving the open hypothesis versus the falsifier.
- Demonstrated that the falsifier fails under both wave-discovery interpretation (at $b = 1$ and $b = 0$) and unbounded-horizon interpretation ($k \ge 5$).
- Confirmed that a state-carried budget intrinsically restructures the state space into a finite 46-state universe with strict 4-step termination.
