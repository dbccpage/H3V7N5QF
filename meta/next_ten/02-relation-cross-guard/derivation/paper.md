# Derivation Report: Problem 02 (relation-cross-guard)

**Candidate**: C21 (`meta/next_ten/02-relation-cross-guard/`)  
**Derived From**: Ninth derivation (`code/ninth/`, `lean4/Ninth/`, `paper/ninth/`)  
**Working Directory**: `meta/next_ten/02-relation-cross-guard/derivation/`  
**Status**: Completed  

---

## 1. Reading the Seed

The task prompt introduces a local modification to the ninth derivation's seed prompt (`diff.patch`):
```text
-Terms are written with letters. An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one.
+Terms are written with letters. An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. Adding `xry` is a change only if `xsy` is not asserted, and adding `xsy` is a change only if `xry` is not asserted.
```

Every other sentence of the ninth seed remains in place:
1. "Terms are written with letters."
2. "An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity."
3. "Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one."
4. [Added guard]: "Adding `xry` is a change only if `xsy` is not asserted, and adding `xsy` is a change only if `xry` is not asserted."
5. "Identifying two terms replaces every occurrence of one with the other."
6. "Adding a term introduces a new letter."
7. "Nothing is given: to begin with there are no terms and nothing is asserted."
8. "A result is what is obtained by a sequence of changes."
9. "Two results are the same if a one-to-one renaming of terms transforms one into the other, preserving relations and multiplicities."

### Notion Table with Source Statuses

| Notion | Status | Description |
|---|---|---|
| Term, Letter | given | An element of the finite term set $\{0, \dots, n-1\}$. |
| Relation (`r`, `s`) | given | Two distinct directed relation labels. |
| Assertion | given | An ordered pair $(x, y)$ in relation $r$ or $s$. |
| Multiplicity | given | Non-negative integer count of an assertion on an ordered pair. |
| Cross-relation guard | given | Adding $xry$ requires $xsy$ not asserted; adding $xsy$ requires $xry$ not asserted. |
| Not asserted | chosen | Defined as multiplicity equal to zero on that ordered pair. |
| Identification | given | Merging term $y$ into term $x$ ($x < y$), summing multiplicities on mapped pairs. |
| Removal | given | Decrementing multiplicity by one on an asserted pair. |
| Empty beginning | given | State with $n = 0$ terms and empty assertion multisets. |
| Sameness | given | Isomorphism under term bijection preserving $r$ and $s$ multiplicities. |
| Step embedding (`StepG -> Step9`) | derived | Every guarded step maps to an admitted ninth step. |
| Disjoint support invariant | derived | Pure additions from empty preserve disjointness between $r$ and $s$ supports. |
| Overlap unreachability by additions | derived | States with $r(x, y) \ge 1$ and $s(x, y) \ge 1$ cannot be reached by additions alone. |
| Identification bypass | derived | Overlapping states can be reached via term addition, disjoint assertions, and identification. |
| Term inflation effect | derived | Overlapping states on $n \ge 2$ terms require passing through an intermediate state of $\ge n+1$ terms. |
| Round 3 divergence | computed | Ninth discovers 8 states in round 3; guarded discovers 7 states (difference: `1::0-0*1\|0-0*1`). |
| Falsifier condition | refuted | The falsifier ("result sets agree in every bounded round") fails at round 3. |

---

## 2. Guarded Step Semantics and Embeddings

Let a state $S = (n, M_r, M_s)$ consist of term count $n \in \mathbb{N}$ and relation multisets $M_r, M_s: n \times n \to \mathbb{N}$.

The admitted changes under the guarded seed are:
1. **Add term**: $(n, M_r, M_s) \to (n+1, M_r, M_s)$.
2. **Remove assertion**: $(n, M_r, M_s) \to (n, M_r - 1_{(x,y)}, M_s)$ if $M_r(x, y) \ge 1$ (analogously for $s$).
3. **Identify terms**: $(n, M_r, M_s) \to (n-1, M'_r, M'_s)$ for $0 \le x < y < n$.
4. **Guarded add assertion**:
   - $xry$ is admitted if and only if $M_s(x, y) = 0$.
   - $xsy$ is admitted if and only if $M_r(x, y) = 0$.

### Embedding into Ninth Derivation
Every guarded step is an admitted ninth step:
$$\mathrm{StepG}(S, c, S') \implies \mathrm{Step9}(S, c, S')$$
This is formalized in Lean 4 as `StepG.toStep9` with zero axiom dependencies.
Consequently, any state reachable in the guarded system is reachable in the ninth system:
$$\mathrm{ReachG}(S_0, S) \implies \mathrm{Reach9}(S_0, S)$$
formalized as `ReachG.toReach9`. The converse fails because ninth steps allow adding $xry$ even when $M_s(x, y) \ge 1$.

---

## 3. What Follows

### 3.1 Refutation of the Falsifier
The candidate proposal in `why.md` states the falsifier:
> "The guarded and ninth result sets agree in every bounded round."

Differential execution over rounds 0 to 5 demonstrates that divergence occurs at round 3:
- **Round 0**: 1 state (`0::`).
- **Round 1**: 1 state (`1::`).
- **Round 2**: 3 states (`2::`, `1::0-0*1|`, `1::|0-0*1`).
- **Round 3**:
  - Ninth discovers 8 new states.
  - Guarded discovers 7 new states.
  - Difference: `{"1::0-0*1|0-0*1"}` is reached in ninth by adding $0s0$ to $1::0-0*1|$, but is blocked in guarded because $0r0$ is already asserted.

Thus the falsifier is **refuted**.

### 3.2 Invariant: Disjoint Support under Pure Additions
When exploration is restricted to additions (adding terms and adding assertions without identification or removal):
- The empty state has disjoint support.
- Adding a term introduces an isolated vertex, preserving disjoint support.
- Adding $xry$ is admitted only when $M_s(x, y) = 0$, ensuring the updated pair has $M_s(x, y) = 0$, so disjointness is preserved.

**Theorem (Lean 4: `reach_add_preserves_disjoint`)**:
If state $S$ is reached from the empty state by additions alone, then for all $x, y$:
$$M_r(x, y) = 0 \quad \lor \quad M_s(x, y) = 0$$

**Corollary (Lean 4: `overlapping_unreachable_by_additions`)**:
Any state having a pair $(x, y)$ with $M_r(x, y) \ge 1$ and $M_s(x, y) \ge 1$ cannot be reached from the empty state by additions alone.

### 3.3 Identification Bypass and Cost Elevation
Although direct addition cannot produce overlapping assertions on the same pair, identification provides a non-local bypass:

1. **1-term witness (`1::0-0*1|0-0*1`)**:
   - Reached in 5 steps:
     1. Add term $\to 1::$
     2. Add term $\to 2::$
     3. Add assertion $1r1 \to 2::1-1*1|$
     4. Add assertion $0s0 \to 2::1-1*1|0-0*1$ (disjoint pairs $(1,1)$ and $(0,0)$)
     5. Identify $0$ and $1 \to 1::0-0*1|0-0*1$.
   - Formalized in Lean 4 (`identification_bypasses_guard`).
   - Cost in ninth system: 3 steps. Cost in guarded system: 5 steps. Cost elevation: $+2$.

2. **2-term witness and Term Inflation (`2::0-1*1|0-1*1`)**:
   - Reached in 6 steps:
     1. Add term $\to 1::$
     2. Add term $\to 2::$
     3. Add term $\to 3::$ (inflates term count to 3)
     4. Add assertion $2r1 \to 3::2-1*1|$
     5. Add assertion $0s1 \to 3::2-1*1|0-1*1$ (disjoint pairs $(2,1)$ and $(0,1)$)
     6. Identify $0$ and $2 \to 2::0-1*1|0-1*1$.
   - Cost in ninth system: 4 steps. Cost in guarded system: 6 steps.
   - **Term Inflation Invariant**: State `2::0-1*1|0-1*1` cannot be reached within a strict bound of $n \le 2$ terms under guarded changes. Because additions cannot produce overlap on $n \le 2$, any identification on $n \le 2$ terms produces an $n = 1$ term state, never an $n = 2$ term state. Reaching it requires expanding to $n = 3$ terms before contracting.

---

## 4. What Does Not Follow

1. **Claim: "Adding an assertion never alters the admissibility of other additions."**
   - *Status*: Refuted.
   - *Witness 1 (holds)*: In state `1::`, adding $0s0$ is an admitted change.
   - *Witness 2 (fails)*: In state `1::0-0*1|`, adding $0s0$ is not an admitted change because $0r0$ is asserted.

2. **Claim: "Every state reachable under guarded changes can be reached by additions alone."**
   - *Status*: Refuted.
   - *Witness 1 (holds)*: State `1::0-0*1|` is reachable by additions alone (2 steps).
   - *Witness 2 (fails)*: State `1::0-0*1|0-0*1` is reachable under guarded changes (5 steps), but is unreachable by additions alone (Lean: `overlapping_unreachable_by_additions`).

3. **Claim: "Reaching an overlapping state on $n$ terms can always be achieved using at most $n$ terms."**
   - *Status*: Refuted.
   - *Witness 1 (holds)*: State `1::0-0*1|0-0*1` ($n = 1$) can be reached via an intermediate state of $n = 2$ terms, which exceeds $n = 1$.
   - *Witness 2 (fails)*: For $n = 2$, state `2::0-1*1|0-1*1` cannot be reached within $n \le 2$ terms; it requires $n = 3$ terms (`differential.json`).

---

## 5. Exploration and Evidence Summary

Systematic exploration within bound $n \le 3$ terms, $m \le 3$ assertions, and 6 rounds yields:
- **Total states discovered**: 284 distinct canonical states.
- **Wave distribution**:
  - Round 0: 1 state
  - Round 1: 1 state
  - Round 2: 3 states
  - Round 3: 7 states
  - Round 4: 25 states
  - Round 5: 88 states
  - Round 6: 159 states
- **Bound exits (frontier)**: 133 exit attempts recorded in `frontier.json`.
- **Disjoint support census**: 280 states maintain disjoint support; 4 states exhibit overlapping support via identification bypass.
- **Byte-identical check**: `python evidence.py --check` succeeds with exit code 0.

---

## 6. Nearest Known Results and Differences

*(This final section names connections to external literature, as permitted by repository conventions.)*

The cross-relation guard modifies the generative multigraph grammar by introducing a negative application condition (NAC) localized to individual directed edges.

1. **Graph Grammars with Negative Application Conditions**:
   In algebraic graph rewriting (Ehrig et al.), rules equipped with negative application conditions prohibit rule firing when specific forbidden subgraphs are present. In our toy setting, the guard acts as an edge-level NAC: rule $\mathrm{add\_edge}(r, x, y)$ is inhibited by the precondition pattern $xsy$. Our finding that vertex identification circumvents the NAC reflects the known property that NACs defined on distinct nodes do not inhibit rules whose patterns merge under non-injective morphisms.

2. **Petri Nets with Inhibitor Arcs**:
   The cross-relation guard mirrors inhibitor arcs in Petri net theory, which test for the absence of tokens in a place. Unchecked multigraph addition corresponds to ordinary vector addition systems (VAS); the presence of cross-inhibition breaks the monotonicity of reachable markings under pure transitions, but the contracting operation (identification) restores reachability of the overlapping markings.

3. **Comparison with Ninth Derivation**:
   In the parent ninth derivation, additions across relations are completely independent: $M_r$ and $M_s$ evolve as orthogonal multisets. The introduction of the cross-relation guard couples the two relations, breaking independent addition, enforcing disjoint support under additions, elevating shortest path costs, and requiring term inflation for compact overlapping structures.
