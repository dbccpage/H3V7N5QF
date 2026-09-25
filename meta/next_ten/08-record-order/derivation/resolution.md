# Resolution of Problem 08: Record-Order

## Question and Target Hypotheses

- **Question:** Does the order of unadmitted leftovers affect which one can be admitted?
- **Hypothesis (from `why.md`):** Order-sensitive feedback changes the result quotient and admission paths.
- **Falsifier (from `why.md`):** All bounded results are classified by the old count alone.

---

## Verdict

- **Falsifier:** **REFUTED.**
- **Hypothesis:** **SUPPORTED.**

---

## Detailed Evidence Chain

### 1. Concrete Non-Isomorphic Witness
Consider the two states on $n=2$ terms with empty asserted relations:
- $\text{State 1}: \text{record} = ((0, 0), (0, 1))$
- $\text{State 2}: \text{record} = ((0, 1), (0, 0))$

Both states have identical sixteenth count projections:
$$\pi(\text{State 1}) = \pi(\text{State 2}) = \{(0, 0): 1, (0, 1): 1\}$$
In sixteenth, $\text{canonical}_{16}(\text{State 1}) = \text{canonical}_{16}(\text{State 2})$, classifying them as the exact same result.

In the record-order model:
- The non-trivial permutation on $\{0, 1\}$ is $(0 \; 1)$, which maps $((0, 0), (0, 1))$ to $((1, 1), (1, 0))$.
- Neither the identity nor $(0 \; 1)$ maps $((0, 0), (0, 1))$ to $((0, 1), (0, 0))$.
- Therefore, $\text{State 1}$ and $\text{State 2}$ belong to distinct isomorphism classes (distinct results).

### 2. Disjoint Next-Step Admissions
The seed specifies:
> "Only the most recently recorded leftover may be admitted, adding the assertion `xry` or the assertion `xsy`; an unadmitted leftover is not an assertion."

- On State 1, the top leftover is $(0, 1)$. The only admissible admissions are:
  - admit $(0, 1)$ into $r$
  - admit $(0, 1)$ into $s$
  The leftover $(0, 0)$ is blocked and cannot be admitted.
- On State 2, the top leftover is $(0, 0)$. The only admissible admissions are:
  - admit $(0, 0)$ into $r$
  - admit $(0, 0)$ into $s$
  The leftover $(0, 1)$ is blocked and cannot be admitted.

The admissible admission sets of State 1 and State 2 are strictly disjoint, demonstrating that sequence order directly controls the admissible transitions.

### 3. Reachability from Empty State
Both states are reachable from the empty state in 6 changes:
- Common prefix:
  1. Add term $0$
  2. Add term $1$
  3. Add assertion $0r0$
  4. Add assertion $0r1$
- Branch 1:
  5. Remove $0r0$ (leaves $0\ell0$)
  6. Remove $0r1$ (leaves $0\ell1$) $\implies ((0, 0), (0, 1))$ (State 1)
- Branch 2:
  5. Remove $0r1$ (leaves $0\ell1$)
  6. Remove $0r0$ (leaves $0\ell0$) $\implies ((0, 1), (0, 0))$ (State 2)

Both branches reside within the declared finite exploration bound ($n \le 2$ terms, $\le 6$ rounds).

### 4. Bounded Exploration Census
Exhaustive breadth-first exploration from the empty state through round 6 with bound $n \le 2$ demonstrates:
- Total ordered canonical results: 388
- Total sixteenth canonical results: 386
- Number of split classes: 2
- Minimal split witness pair: reached at depth 6.

This computational census confirms that the result quotient is strictly finer than sixteenth's quotient.

### 5. Machine-Checked Proof
The Lean 4 formalization in `Derivation.lean` provides constructive machine verification:
- `theorem witness_count_eq`: identical counts for all pairs.
- `theorem witness1_admissible` & `theorem witness1_not_admissible_other`: verifies LIFO admission on State 1.
- `theorem witness2_admissible` & `theorem witness2_not_admissible_other`: verifies LIFO admission on State 2.
- `theorem witness_different_admissions`: shows in this model that admission predicates are not equivalent.
- `theorem falsifier_refuted`: refutes the falsifier with zero `sorry`, zero `admit`, and zero non-standard axioms.

---

## Claim Hygiene Summary

### 1. What This Evidence Supports
- In this model, ordering unadmitted leftovers into a sequence where only the most recent leftover may be admitted refines the equivalence relation of results compared to the sixteenth derivation.
- In this model, two reachable states with identical counts of leftovers can have disjoint sets of admissible next-step admissions.
- The falsifier "all bounded results are classified by the old count alone" is refuted by an explicit, reachable 2-term counterexample.

### 2. What This Evidence Does Not Support
- This evidence does not support claims about unbounded term sizes ($n > 2$) or unbounded round depths ($> 6$) beyond the certified witnesses.
- This evidence does not assert equivalence to any specific external computing model outside the formal definitions provided in the seed.

### 3. The Narrowest Defensible Claim
Under the record-order seed, the order in which leftovers are recorded restricts admissible admissions to the most recent leftover, distinguishing states that share identical sixteenth leftover counts and altering the available admission paths.

### 4. The Next Test Needed
Explore whether term identifications ($u < v$) can permute or collapse leftovers in longer sequences ($k \ge 3$) into orbits that reconnect previously split classes.
