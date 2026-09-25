# Resolution of Hypothesis — Problem 07: Two-Term Readings

## 1. Candidate Hypothesis and Falsifier

- **Hypothesis (from `why.md`):**
  *"Sameness by local readings differs from both written equality and FREE rewriting."*

- **Falsifier (from `why.md`):**
  *"The bounded partitions agree with one of the parent's two equivalences."*

## 2. Definitive Status

- **Hypothesis:** **CONFIRMED** (demonstrated in this bounded setting).
- **Falsifier:** **REFUTED**.

## 3. Quantitative Evidence

In the exploration from the nameless initial state `given(False, Sameness.FREE)` under a bound of 3 terms and 12 rounds:

| Equivalence Relation | Equivalence Classes at Bound 3 | Comparison to Local Readings |
|---|---|---|
| Written equality (Eighteenth sameness) | 69 | Strictly finer (69 > 8) |
| FREE canonical rewriting (Base isomorphism) | 20 | Strictly finer (20 > 8) |
| Multiset local reading equality (Alternative) | 14 | Strictly finer (14 > 8) |
| **Set local reading equality (Chosen)** | **8** | **Baseline under test** |

For the named initial state `given(False, Sameness.ANCHORED)` under the same bound:
- Written states: 137
- ANCHORED canonical classes: 109
- Set local reading classes: 8

Because $8 \neq 69$ and $8 \neq 20$ (and $8 \neq 137$ and $8 \neq 109$), the local reading partition does not agree with written equality, nor does it agree with FREE rewriting. The falsifier is therefore refuted, and the hypothesis is confirmed.

## 4. Key Structural Findings

1. **Collapsing of distinct written states:**
   At $n = 2$, `arb` and `bra` are distinct written states, but yield identical local record sets:
   $$\{(0, ()), (1, ()), (2, \text{fwd}), (2, \text{bwd})\}.$$
   Proved in Lean 4 (`arb_equiv_bra`).

2. **Collapsing of non-isomorphic states:**
   At $n = 3$, state $s_A$ (2 assertions, one 2-cycle) and state $s_B$ (4 assertions, two 2-cycles) have different edge counts and are non-isomorphic under FREE rewriting, yet yield the identical set of 2-term sub-reading records:
   $$\{(0, ()), (1, ()), (2, \text{none}), (2, \text{both})\}.$$
   Proved in Lean 4 (`s_A_equiv_s_B`).

3. **Step non-congruence:**
   The one-step transition relation fails to descend to equivalence classes of local readings. A single assertion removal from $s_A$ reaches a state with no 2-cycles, whereas every single assertion removal from $s_B$ retains at least one 2-cycle. Lean theorems `s_A_next_not_equiv_s_B_rem1` through `rem4` confirm that no single step from $s_B$ can match this transition. Across the 69 bounded states, 31 transition failures are detected.

## 5. Claim Discipline Summary

1. **What this supports:**
   In the declared bounded universe ($\le 3$ terms), sameness by 0-, 1-, and 2-term sub-reading record sets defines an equivalence relation that is strictly coarser than graph isomorphism and written equality, and does not preserve one-step transition simulation.

2. **What this does not support:**
   This does not demonstrate that sub-readings of larger size ($k \ge 3$) fail to identify graphs, nor does it establish an unbounded closed form for the partition sequence across all $n$.

3. **Narrowest defensible claim:**
   For legal states on at most 3 terms, agreement of the sets of records across all readings of at most two terms partitions the 69 reachable states into exactly 8 equivalence classes, strictly fewer than the 20 isomorphism classes and 69 written representations, and fails to form a congruence with the change step relation.

4. **Next test needed:**
   Evaluate $k$-term sub-reading equivalence for $k = 3$ on graphs with $n \ge 4$ vertices to determine the minimum reading size required to recover isomorphism.
