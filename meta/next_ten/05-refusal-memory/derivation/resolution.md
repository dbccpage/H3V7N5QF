# Resolution of Hypothesis and Falsifier for Problem 05 (Refusal Memory)

## 1. Candidate Context and Stated Stakes

Candidate ID: **C01** (`meta/next_ten/05-refusal-memory/`)  
Parent Derivation: **Seventeenth** (`code/seventeenth/`, `lean4/Seventeenth/`, `paper/seventeenth/`)  

- **Hypothesis, open:** A refusal record can change later reachability.
- **Falsifier:** Every reached result and round agrees with the seventeenth under both answer readings.

## 2. Definitional Clarification of Terms

In the parent seventeenth derivation, the obstruction sentence reads:
> "A change that makes some `xrx` asserted is obstructed. An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which, and record the change, the obstruction, and the answer. A refused change is recorded and changes nothing."

Seventeenth investigated two answer readings:
1. **A-replace (Refusal without Memory):**
   An obstructed change is refused and changes nothing. In seventeenth, the obstructed change was not entered into the closure of results. Consequently, every reached state was loop-free (`HasLoop s` was false for all reached results).
2. **A-perform (Perform Immediately):**
   Every change is entered, obstructed or not. Loop-asserting states (such as `oneLoop`, obtained by identifying `a` and `b` in `givenA`) were entered immediately at round 1.

In Problem 05, the seed adds one sentence:
> "Its written form is kept with that result; the next attempt at the same written change is performed even if it makes some `xrx` asserted."

This establishes a two-phase dynamic for obstructed changes under the refusal reading:
- **First Attempt (Refusal Step):** The change is obstructed. Being absent from the result's refusal memory, it is refused. It changes nothing about terms or assertions (`(⟨s, c :: R⟩).st = s`), but its written form is stored with that result.
- **Repeated Attempt (Override Step):** When the same written change is attempted on a result that already holds that change in its refusal memory, the override triggers: the change is performed via `perform`, even if it makes some `xrx` asserted.

## 3. Empirical and Formal Verification

The exact enumeration of Problem 05 results and transitions (`model.py`, `evidence.py`) and formal Lean 4 verification (`Derivation.lean`) establish the following comparison at bound 3 across 4 rounds:

| Configuration | Seventeenth A-replace (Total / Loops / `oneLoop` Round) | Problem 05 Refusal Memory (Total / Loops / `oneLoop` Round) | Seventeenth A-perform (Total / Loops / `oneLoop` Round) | Falsifier Agrees with Seventeenth? |
|:---|:---:|:---:|:---:|:---:|
| `bra_False_anchored` | 51 / 0 / — | 298 / 57 / round 2 | 165 / 114 / round 1 | **No** (refuted) |
| `bra_False_free` | 18 / 0 / — | 144 / 37 / round 2 | 63 / 45 / round 1 | **No** (refuted) |
| `bra_True_anchored` | 48 / 0 / — | 303 / 59 / round 2 | 165 / 114 / round 1 | **No** (refuted) |
| `bra_True_free` | 17 / 0 / — | 144 / 31 / round 2 | 63 / 45 / round 1 | **No** (refuted) |

### 3.1 Refutation of the Falsifier

The falsifier states:
> "Every reached result and round agrees with the seventeenth under both answer readings."

This claim is refuted across all four evaluated configurations on two distinct grounds:

1. **Disagreement with Seventeenth A-replace:**
   - In seventeenth A-replace, obstructed changes are refused and not entered into the closure of results. Exactly 0 loop-asserting states are ever reached (`loop_states_count = 0`).
   - In Problem 05 under refusal memory, obstructed changes are recorded on the first attempt and executed on the second attempt. At round 2, loop-asserting states emerge (57 in `bra_False_anchored`, 37 in `bra_False_free`).
   - Even projecting results to their underlying graph states by forgetting refusal records, the set of reached graph states in Problem 05 strictly contains states that seventeenth A-replace never reaches.

2. **Disagreement with Seventeenth A-perform:**
   - In seventeenth A-perform, obstructed changes are performed on the very first attempt without requiring prior refusal. `oneLoop` (the one-term state asserting a loop, formed by identifying `a` with `b`) is reached at round 1.
   - In Problem 05 under refusal memory, `oneLoop` cannot be reached at round 1 because identifying `a` and `b` is obstructed and must first be refused. `oneLoop` is reached at round 2 via the override step.
   - The round of first discovery for `oneLoop` shifts from round 1 to round 2 ($2 \ne 1$).

Because Problem 05 agrees neither with seventeenth A-replace nor with seventeenth A-perform in either reached results or discovery rounds, the falsifier is refuted.

### 3.2 Formal Lean 4 Derivation

The divergence in reachability is proved in Lean 4 without non-standard axioms (`Derivation.lean`):
- `refusal_preserves_state`: Refusal preserves terms and assertions (`(⟨s, c :: R⟩).st = s`).
- `refusal_accumulates_record`: The refused change is stored in the result's record (`c ∈ (⟨s, c :: R⟩).refused`).
- `rootA_one_step_no_loop`: Every 1-step transition from `rootA = ⟨givenA, []⟩` produces a loop-free state (`∀ rs', StepRM rootA rs' → ¬ HasLoop rs'.st`).
- `two_step_reaches_loop`: In two steps, the sequence `step1_ident01_refusal` followed by `step2_ident01_override` reaches `⟨perform givenA ident01, []⟩`, which asserts a loop (`(0, 0) ∈ s.A`).
- `two_attempt_difference`: Loop-asserting states are precluded in one step from `rootA`, but reachable in two steps.

## 4. Resolution of the Hypothesis

Under the claim hygiene discipline:

1. **What it supports:**
   - The evidence supports the hypothesis that a refusal record changes later reachability.
   - Under the refusal answer reading, keeping a record of refused written changes enables an override transition on repeated attempt, making loop-asserting states reachable that were previously unreachable under seventeenth A-replace.
   - Compared to seventeenth A-perform, the refusal memory model enforces a two-attempt latency: loop-asserting states require a preparatory refusal step and emerge at round 2 rather than round 1.

2. **What it does not support:**
   - It does not support any claim that refusal memory alters reachability if the exploration reading is fixed to A-perform (where obstructed changes are performed immediately and refusal is never invoked).
   - It does not show that refusal memory makes unreachable states reachable when restricted entirely to loop-free graph states.

3. **Narrowest defensible claim:**
   In this model, pairing results with a refusal memory of attempted written changes allows repeated attempts at obstructed changes to perform, reaching loop-asserting states in two steps from what is given, whereas seventeenth A-replace reaches no loop-asserting states at any round and seventeenth A-perform reaches them in one step.

4. **Next test needed:**
   A test extending the model to term bounds $N \ge 4$ under longer round bounds ($\ge 6$), examining whether multi-element refusal records ($\|R\| \ge 2$) induce distinct reachability lattices when refusal records are inherited across transitions (`RecordScope.CARRIED`) versus kept strictly per-result (`RecordScope.LOCAL`).

## 5. Drop Condition Assessment

`why.md` specified:
> "Drop or rewrite the proposal if its edited seed has an unresolved contradiction, if every new distinction sits only in an external log or chosen label, if the finite test finds the stated falsifier and no distinct claim remains, or if its required state/step map cannot be made precise without a third seed sentence."

- The seed edit contains no unresolved contradiction.
- The distinction does not reside solely in an external log: refusal memory directly controls whether a state transition performs or refuses, altering the reachable graph states and their discovery rounds.
- The finite test refutes the falsifier; the distinct claim is verified in typed Python and proved in Lean 4.
- The state/step map is precise without additional seed sentences.
Therefore, the proposal stands validated and resolved.
