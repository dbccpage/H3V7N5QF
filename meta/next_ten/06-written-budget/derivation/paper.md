# What follows from a state-carried budget: four available changes, strictly decreasing budget, and bounded reachability from nothing

Derivation of candidate C04 (`meta/next_ten/06-written-budget/`). Input: `meta/next_ten/06-written-budget/seed_prompt.md`. Parent: ninth derivation (`prompt/ninth/seed_prompt.md`, `paper/ninth/paper.md`). Task: `meta/next_ten/06-written-budget/prompt.md`. Claim IDs refer to `meta/next_ten/06-written-budget/derivation/claim_ledger.md`; IDs written `9:…` refer to the ninth derivation's ledger (`paper/ninth/claim_ledger.md`). Lean declarations in namespace `Seed.Problem06` are in `meta/next_ten/06-written-budget/derivation/Derivation.lean`. Axiom report: standard Lean 4 kernel axioms (`propext`, `Classical.choice`, `Quot.sound`). No `sorry`, `admit`, or declared axioms occur. Computed evidence files are in `meta/next_ten/06-written-budget/derivation/evidence/`, generated deterministically by `evidence.py` and validated by `--check`.

Every notion below carries one source status: **given** (stated in the seed), **chosen** (a reading fixed where the seed is silent or ambiguous), **derived** (proved by Lean or exhaustive bounded check), **computed** (output of typed code), **refuted** (proved false in this model), **open** (neither proved nor refuted).

---

## 0. Findings in brief

1. **A state-carried budget replaces an unbounded state space with an intrinsically finite universe.**  
   The ninth seed admits an unbounded sequence of changes; any well-formed state is reachable. In contrast, under this seed each alternative begins with four available changes, each performed change consumes one, and attempts at budget zero change nothing. The maximum length of any sequence of performed changes from `(empty, 4)` is exactly 4 (Lean `BReach.four_step_max`).

2. **Every performed change strictly decreases the remaining budget.**  
   For any performed transition $s \to t$, $s.\text{budget} = t.\text{budget} + 1$ (Lean `BStep.budget_eq`, `BStep.budget_lt`). Along any sequence of $n$ changes, $s.\text{budget} = t.\text{budget} + n$ (Lean `BReach.budget_eq`). When budget reaches 0, no further change can be performed (Lean `BStep.not_step_at_zero`).

3. **Reachable states number exactly 46 across five discrete budget levels.**  
   Breadth-first exploration from `(empty, 4)` terminates completely after round 4. The distribution of reachable canonical states by remaining budget is:
   - Budget 4 ($k = 0$ changes performed): 1 state
   - Budget 3 ($k = 1$ change performed): 1 state
   - Budget 2 ($k = 2$ changes performed): 3 states
   - Budget 1 ($k = 3$ changes performed): 9 states (1 of size 1, 8 of size 3)
   - Budget 0 ($k = 4$ changes performed): 32 states (3 of size 2, 29 of size 4)
   Total: 46 states (`evidence/budget_census.json`).

4. **An independent mathematical census certifies exploration completeness.**  
   A state $s$ is reachable in $k \le 4$ changes from empty if and only if $s.\text{WF}$, $\text{size}(s) \le k$, $\text{size}(s) \equiv k \pmod 2$, and (for $k > 0$) $s$ has at least one term. Decomposing by total multiplicity and orbit counts (the ninth derivation's `two_term_count` and single-relation counts) reproduces the counts $1, 1, 3, 9, 32$ without running a search.

5. **The term bound frontier is empty for bound $\ge 4$.**  
   Because initial terms are 0 and each change adds at most one term, every reachable state has at most 4 terms (Lean `BReach.terms_le`). No path exits the bound; termination occurs through budget exhaustion rather than an arbitrary term cap.

6. **The falsifier is refuted under both wave-discovery and unbounded-horizon readings.**  
   The candidate hypothesis asked whether a state-carried budget changes reachability beyond the study's round bound, with the candidate falsifier asserting: "At every recorded budget, the reachable states are the parent's states at the same round." Under breadth-first discovery waves, the falsifier fails at budget 1 (9 states vs 8 parent wave states) and budget 0 (32 states vs 29 parent wave states) because non-minimal paths revisit lower-size states carrying lower budgets. Globally, the falsifier fails for all rounds $k \ge 5$, where the parent continues to reach new states while this model is exhausted.

---

## 1. The Seed and the Readings

The seed prompt differs from the ninth seed by exactly Sentence 5 (`meta/next_ten/06-written-budget/diff.patch`):

> "Nothing is given: to begin with there are no terms and nothing is asserted. Each alternative begins with four changes available; each performed change uses one, an attempt with none available changes nothing, and every result records how many remain."

### Notion Table with Source Statuses

| Notion | Status | Definition / Citation |
|---|---|---|
| Term, assertion, relation $r, s$, multiplicity | given | Seed sentences 1–4; identical to ninth seed |
| Empty beginning | given | Seed sentence 5: "to begin with there are no terms and nothing is asserted" |
| Available budget of 4 | given | Seed sentence 5: "Each alternative begins with four changes available" |
| Unit budget consumption | given | Seed sentence 5: "each performed change uses one" |
| Attempt at zero changes nothing | given | Seed sentence 5: "an attempt with none available changes nothing" |
| Result records remaining budget | given | Seed sentence 5: "every result records how many remain" |
| Four kinds of change | given | Seed sentences 7–8; identical to ninth seed |
| Sameness under term rewriting | given | Seed sentence 9; identical to ninth seed |
| Budgeted state representation | chosen (C1) | A pair `(state, budget)` where `state` is a canonical Ninth `DState` and `budget ∈ {0, 1, ..., 4}` |
| Sameness of budgeted results | chosen (C2) | Two results agree iff their canonical underlying states and remaining budgets both agree |
| Performed change semantics | chosen (C3) | If `budget > 0`, execute Ninth change and set `budget' = budget - 1` |
| Zero-budget attempt semantics | chosen (C4) | If `budget = 0`, transition is an identity step `s → s` with `budget' = 0` |
| BFS exploration protocol | chosen (C5) | Explore wave by wave from `(empty, 4)` until all wave states have `budget = 0` |
| Strictly decreasing budget | derived (D1) | Lean `BStep.budget_lt`, `BStep.budget_eq` |
| Path budget equation | derived (D2) | Lean `BReach.budget_eq` ($s.\text{budget} = t.\text{budget} + n$) |
| 4-step maximum bound | derived (D3) | Lean `BReach.four_step_max` ($n \le 4$ from `emptyB`) |
| Budget zero equivalence | derived (D4) | Lean `BReach.budget_zero_iff_four` ($t.\text{budget} = 0 \leftrightarrow n = 4$) |
| Non-step at budget zero | derived (D5) | Lean `BStep.not_step_at_zero` (no valid `BStep` from `budget = 0`) |
| Reachability characterization | derived (D6) | Lean `BReach.characterization` |
| Size bound $\le 4$ | derived (D7) | Step-size argument in §7, plus the bounded census; no corresponding theorem in this Lean file |
| Term bound $\le 4$ | derived (D8) | Lean `BReach.terms_le` ($t.\text{state}.n \le 4$) |
| Reachable state counts {1, 1, 3, 9, 32} | computed (K1) | `model.py`, `evidence/budget_census.json` |
| Completeness certificate | computed (K2) | Independent census matches BFS exploration |
| Empty frontier at bound 4 | computed (K3) | `evidence/summary.json` |
| Discrepancy with parent waves | computed (K4) | `evidence/parent_comparison.json` |
| Refutation of falsifier | refuted (R1, R2) | `resolution.md`, `test_derivation.py` |
| Paths of length $> 4$ | refuted (R3) | Lean `BReach.four_step_max` |
| States of size $> 4$ | refuted (R4) | Step-size argument in §7 |

---

## 2. States and Sameness

A state of this seed carries two dials:
1. An underlying two-relation state without names (`DState`), specifying $n$ terms and a multiplicity function for $r$ and for $s$.
2. A recorded budget $b \in \{0, 1, 2, 3, 4\}$.

The beginning is `emptyB = (empty9, 4)`: 0 terms, 0 assertions in either relation, and 4 changes available.

Sentence 9 specifies:
> "Two results that differ only in how their terms are written are the same result."

Sentence 5 specifies:
> "every result records how many remain."

Therefore, two budgeted states $(s_1, b_1)$ and $(s_2, b_2)$ represent the same result if and only if:
$$b_1 = b_2 \quad \text{and} \quad \text{canonical}(s_1) = \text{canonical}(s_2)$$
where $\text{canonical}$ normalizes the term labels to the least lexicographical writing under $S_n$.

Two states with identical underlying term and assertion structure but differing remaining budgets are distinct results. For example, the 1-term empty state carrying budget 3 (reached in 1 change) is distinct from the 1-term empty state carrying budget 1 (reached in 3 changes).

---

## 3. Changes and Step Consumption

The four kinds of change are those of the ninth seed:
1. Adding a term.
2. Adding an assertion in $r$ or $s$.
3. Removing an asserted assertion in $r$ or $s$.
4. Identifying two terms in every assertion of both relations.

Sentence 5 introduces the budget dynamics:
> "Each alternative begins with four changes available; each performed change uses one, an attempt with none available changes nothing, and every result records how many remain."

### Formalization of Performed Change
A performed change is modeled by the inductive relation `BStep`:
```lean
inductive BStep : BSt → BSt → Prop where
  | step (s : BSt) (t : NDSt) (hst : Step9 s.state t) (hb : s.budget > 0) :
      BStep s ⟨t, s.budget - 1⟩
```

From this definition, two consequences follow immediately:
- **Strict budget decrement:** Every performed change satisfies $s.\text{budget} = t.\text{budget} + 1$ (Lean `BStep.budget_eq`) and $t.\text{budget} < s.\text{budget}$ (Lean `BStep.budget_lt`).
- **Stopping at budget zero:** If $s.\text{budget} = 0$, the premise $s.\text{budget} > 0$ cannot be satisfied. Thus no performed step exists from a state with budget 0 (Lean `BStep.not_step_at_zero`). An attempt at budget zero "changes nothing": the system remains at $(s, 0)$.

---

## 4. Exploration and the Finite Frontier

Starting from `emptyB = (empty9, 4)`, exploration proceeds round by round, attempting every legal change on each alternative:

- **Round 0 (Budget 4):**
  The initial state `(empty, 4)` alone. Size is 0.

- **Round 1 (Budget 3):**
  From empty, the only legal change is adding a term.
  Reaches 1 canonical state: `(1-term empty, 3)`. Size is 1.

- **Round 2 (Budget 2):**
  From `(1-term empty, 3)`, three legal changes exist:
  - Add a term $\to$ `(2-term empty, 2)`
  - Add assertion `0r0` $\to$ `(1-term 0r0, 2)`
  - Add assertion `0s0` $\to$ `(1-term 0s0, 2)`
  Reaches 3 canonical states, all of size 2.

- **Round 3 (Budget 1):**
  From the three states at budget 2:
  - Additions produce 8 states of size 3.
  - Identification from `(2-term empty, 2)` merges 0 and 1, producing `(1-term empty, 1)`.
  - Removals from `(1-term 0r0, 2)` and `(1-term 0s0, 2)` produce `(1-term empty, 1)`.
  Reaches 9 canonical states: 1 of size 1 and 8 of size 3.

- **Round 4 (Budget 0):**
  From the nine states at budget 1:
  - Additions from size 3 produce 29 states of size 4.
  - Additions from `(1-term empty, 1)` produce 3 states of size 2.
  - Reductions (removals and identifications) from size 3 also produce the 3 states of size 2.
  Reaches 32 canonical states: 3 of size 2 and 29 of size 4.

- **Round 5:**
  All states in round 4 have budget 0.
  Attempts on these states change nothing.
  Zero new states are produced. Exploration terminates completely.

Total states explored: $1 + 1 + 3 + 9 + 32 = 46$ states.  
With term bound $\ge 4$, the frontier is empty (`evidence/summary.json`).

---

## 5. Independent Census and Completeness Certificate

The completeness of the exploration is certified by an independent mathematical count derived from ninth-derivation orbit formulas and parity invariants:

1. **Parity and Size Invariant:**
   In Ninth, every change changes size by $\pm 1$. Thus, for any state $s$ reached from `empty` in $k$ steps:
   $$\text{size}(s) \le k \quad \text{and} \quad \text{size}(s) \equiv k \pmod 2$$
   For $k > 0$, $s$ must have at least one term ($n \ge 1$).

2. **Census by Performed Steps $k$ (Remaining Budget $b = 4 - k$):**
   - **$k = 0$ ($b = 4$):** Size 0. Exactly 1 state (`empty`).
   - **$k = 1$ ($b = 3$):** Size 1. $n = 1, m = 0$. Exactly 1 state (`1-term empty`).
   - **$k = 2$ ($b = 2$):** Size 2.
     - $n = 2, m = 0$: 1 state (`2-term empty`).
     - $n = 1, m = 1$: $\binom{1+1}{1} = 2$ states (`0r0`, `0s0`).
     Total: $1 + 2 = 3$ states.
   - **$k = 3$ ($b = 1$):** Sizes $\{1, 3\}$.
     - Size 1: 1 state.
     - Size 3:
       - $n = 3, m = 0$: 1 state.
       - $n = 2, m = 1$: 4 states (loop/edge in $r/s$).
       - $n = 1, m = 2$: $\binom{2+1}{1} = 3$ states (`2r`, `1r1s`, `2s`).
       Total size 3 = $1 + 4 + 3 = 8$ states.
     Total: $1 + 8 = 9$ states.
   - **$k = 4$ ($b = 0$):** Sizes $\{2, 4\}$.
     - Size 2: 3 states.
     - Size 4:
       - $n = 4, m = 0$: 1 state.
       - $n = 3, m = 1$: 4 states (loop/edge in $r/s$ under $S_3$).
       - $n = 2, m = 2$: 20 states (given by Ninth's `two_term_count(2)`).
       - $n = 1, m = 3$: $\binom{3+1}{1} = 4$ states.
       Total size 4 = $1 + 4 + 20 + 4 = 29$ states.
     Total: $3 + 29 = 32$ states.

The independent census yields $\{4: 1, 3: 1, 2: 3, 1: 9, 0: 32\}$, matching the BFS exploration byte-identically (`evidence/budget_census.json`).

---

## 6. Comparison with Parent Ninth Derivation

The comparison against the parent Ninth derivation clarifies the precise structural impact of the state-carried budget (`evidence/parent_comparison.json`):

1. **Wave Size Divergence:**
   In parent Ninth, BFS wave $k$ contains only states of cost (size) $k$:
   - Wave 1: 1 state (size 1)
   - Wave 2: 3 states (size 2)
   - Wave 3: 8 states (size 3)
   - Wave 4: 29 states (size 4)
   In Problem 06, budget 1 ($k = 3$) contains 9 states: the 8 size-3 states plus the revisited size-1 state. Budget 0 ($k = 4$) contains 32 states: the 29 size-4 states plus the 3 revisited size-2 states.

2. **Reachability Termination:**
   Parent Ninth reaches an unbounded space: wave 5 has 104 states, wave 6 has 402 states, etc.
   Problem 06 terminates completely at budget 0 ($k = 4$). Wave 5 is empty.

---

## 7. What Does Not Follow

To maintain strict claim discipline, the following negative results are established:

1. **Paths exceeding 4 changes do not follow.**  
   *Witness:* From `(empty, 4)`, any sequence of 4 changes reaches budget 0. At budget 0, attempting any change produces the identical state with budget 0 (Lean `BStep.not_step_at_zero`). No 5-step path of performed changes exists (refuted by Lean `BReach.four_step_max`).

2. **Reaching states of size $> 4$ does not follow.**  
   *Argument:* Each legal addition raises size by 1, each removal lowers it by 1, and identification preserves assertion multiplicity while removing one term. Since initial size is 0 and a path has at most 4 performed changes (`BReach.four_step_max`), every reachable state has size $\le 4$. States of size 5 (such as `5-term empty` or `1-term with 5 assertions`) are unreachable from `emptyB`.

3. **Equality of budget sets with parent BFS discovery waves does not follow.**  
   *Witness:* At budget 1, the state `DState(1, (0,), (0,))` (1-term empty) is reachable carrying budget 1. In parent Ninth, this state belongs to wave 1, not wave 3. Thus the set of underlying states reachable at budget 1 is not equal to parent wave 3.

---

## 8. Nearest Known Results and Differences

*(House words only in earlier sections; outside results named only here.)*

1. **Resource-Bounded Transition Systems and Timed Automata:**  
   The budget mechanism behaves like a discrete countdown clock or resource token in resource-bounded Petri nets and timed transition systems. In timed automata, clocks advance continuously; here, the budget decrements discretely by 1 per performed operation.

2. **Bounded Rewriting Systems:**  
   Unlike term rewriting systems with termination guaranteed by termination orderings (e.g., Knuth-Bendix or polynomial interpretations), termination here is enforced externally by a state-carried counter rather than structural simplifications.

3. **Subsumption of External Round Bound by State Invariants:**  
   In standard model checking, round bounds are meta-parameters passed to exploration algorithms. Here, the bound is internalized into the state algebra, transforming an infinite-state BFS into a finite closed graph.

---

## Artifact Summary

1. **What this paper supports:**
   - Supports the strict decrement of budget on each performed change.
   - Supports the 4-step maximum bound from `emptyB`.
   - Supports the exact census of 46 reachable budgeted states.
   - Supports the refutation of the candidate falsifier.

2. **What this paper does not support:**
   - Does not support reachability of any state once budget reaches 0.
   - Does not support reachability of any state of size $> 4$.

3. **Narrowest defensible claim:**
   Under an initial budget of 4 and unit consumption per performed change, the reachable state space from `(empty, 4)` is finite, contains exactly 46 canonical states, and strictly terminates within at most 4 performed changes.

4. **Next test needed:**
   Evaluation of non-uniform consumption models where removals or identifications carry zero or differential cost.
