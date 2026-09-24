# Derivation of Problem 08: Record-Order

## 1. Reading of the Seed

The seed modifies the sixteenth seed by replacing the sentence governing leftovers with two new sentences:

> "Recorded leftovers are kept in the order they arise. Only the most recently recorded leftover may be admitted, adding the assertion `xry` or the assertion `xsy`; an unadmitted leftover is not an assertion."

Every other sentence of the seed prompt is unchanged from the sixteenth derivation:
- Terms are written with letters.
- An assertion is written `xry` or `xsy`; it has a multiplicity raised by adding and lowered by removing.
- Nothing is given: to begin with there are no terms and nothing is asserted.
- The four kinds of change are identifying two terms, removing an assertion, adding a term, and adding an assertion.
- After every change, record what that change leaves. A leftover is written neither `xry` nor `xsy`.
- Attempt every change, fewest additions first.
- Two results that differ only in how their terms are written are the same result.
- Attempt 100 changes along each alternative within a declared finite bound.

### Notions and Source Statuses

| Notion | Source Status | Description |
| :--- | :--- | :--- |
| Term | given | Written with letters; indexed by natural numbers $0 \le t < n$. |
| Assertion | given | Directed pair under relation $r$ or $s$, carrying an integer multiplicity. |
| Change | given | One of four operations: identify, remove, add term, add assertion. |
| Leftover | given | Written neither $xry$ nor $xsy$; left by a removal as $x\ell y$. |
| Recorded Order | given | Leftovers are kept in the order they arise. |
| Most Recent Leftover | given | The latest element in the arrival sequence. |
| Admissibility | given | Only the most recently recorded leftover may be admitted into $r$ or $s$. |
| Unadmitted Status | given | An unadmitted leftover is not an assertion. |
| Same Result | given | Equality up to a permutation of term names. |
| Ordered Record (Stack) | chosen | The sequence of unadmitted leftovers represented as a sequence with newest at the end. |
| LIFO Discipline | derived | Admitting pops the most recent leftover; earlier leftovers are blocked until uncovered. |
| Term Identification Action | derived | Identifying terms $u < v$ remaps endpoints in assertions and in the leftover sequence while preserving sequence positions. |
| Count Projection | derived | Forgetting sequence order yields sixteenth's multiset count vector. |
| Result Quotient Refinement | computed | The equivalence relation under term permutations is strictly finer than sixteenth's quotient. |
| Admission Path Restriction | derived | Next-step admissions are constrained to at most two choices (top into $r$ or $s$), regardless of record size. |
| Falsifier Refutation | refuted | The claim "all bounded results are classified by the old count alone" is refuted by witness states. |
| Hypothesis Validation | derived | Order-sensitive feedback changes the result quotient and admission paths. |

---

## 2. What Follows

### 2.1 The Ordered Record and LIFO Admission
Under the sixteenth derivation, unadmitted leftovers were held as an unordered multiset (a counted relation $x\ell y$). Any pair with non-zero count could be admitted at any step, yielding $2 \cdot d_\ell$ possible admission changes.

Under the current seed, leftovers form a chronological sequence. When a removal of $xry$ or $xsy$ occurs, the pair $(x, y)$ is appended to the sequence. The phrase "only the most recently recorded leftover may be admitted" establishes a Last-In-First-Out (LIFO) discipline:
1. If the sequence is empty, no admission is admissible.
2. If the sequence has length $k \ge 1$, only the top leftover $(x_k, y_k)$ may be admitted.
3. Admitting $(x_k, y_k)$ into $r$ adds assertion $x_k r y_k$ and leaves the sequence of length $k-1$.
4. Earlier leftovers $(x_j, y_j)$ for $j < k$ cannot be admitted while $(x_k, y_k)$ remains on top.

### 2.2 Term Rewritings and Canonical Form
The seed states: "Two results that differ only in how their terms are written are the same result."
A rewriting of terms is a permutation $p$ of the term set $\{0, \dots, n-1\}$. The permutation acts on relation matrices:
$$p(r)_{p(x), p(y)} = r_{x, y}, \quad p(s)_{p(x), p(y)} = s_{x, y}$$
and on each element of the leftover sequence:
$$p((x_1, y_1), \dots, (x_k, y_k)) = ((p(x_1), p(y_1)), \dots, (p(x_k), p(y_k))).$$
Crucially, the permutation renames the endpoints of each leftover but does not reorder the sequence. The chronological order is an invariant of the history, not a term label.

### 2.3 Quotient Refinement
Forgetting sequence order defines a canonical projection map:
$$\pi : \text{OrderedState} \to \text{SixteenthState}$$
mapping each ordered record to its pair multiplicity function:
$$\pi(\text{record})(x, y) = \#\{i \mid (x_i, y_i) = (x, y)\}.$$

In this model:
- If two states are isomorphic in the ordered setting ($s_1 \cong s_2$), their projections are isomorphic in the sixteenth setting ($\pi(s_1) \cong \pi(s_2)$).
- The converse does not hold. Two states may have $\pi(s_1) \cong \pi(s_2)$ while $s_1 \not\cong s_2$.

### 2.4 Minimal Witness
Consider the two states on $n=2$ terms with empty relations:
- State 1: record $= ((0, 0), (0, 1))$. Top element is $(0, 1)$.
- State 2: record $= ((0, 1), (0, 0))$. Top element is $(0, 0)$.

Both states have count projection:
$$\pi(s_1) = \pi(s_2) = \{(0, 0): 1, (0, 1): 1\}.$$
Under the sixteenth model, $s_1$ and $s_2$ are the same result.
Under the ordered model, the only non-trivial permutation on $\{0, 1\}$ is the transposition $(0 \; 1)$, which maps $((0, 0), (0, 1))$ to $((1, 1), (1, 0)) \ne ((0, 1), (0, 0))$. Hence no permutation maps State 1 to State 2. They are distinct results.

Furthermore, their admissible next steps differ:
- From State 1, the only admissible admissions are $0r1$ and $0s1$. The leftover $0\ell0$ cannot be admitted.
- From State 2, the only admissible admissions are $0r0$ and $0s0$. The leftover $0\ell1$ cannot be admitted.

Both states are reachable from the empty state in 6 changes:
1. Add term $0$
2. Add term $1$
3. Add assertion $0r0$
4. Add assertion $0r1$
- Branch 1: remove $0r0$ (leaves $0\ell0$), then remove $0r1$ (leaves $0\ell1$) $\implies ((0, 0), (0, 1))$.
- Branch 2: remove $0r1$ (leaves $0\ell1$), then remove $0r0$ (leaves $0\ell0$) $\implies ((0, 1), (0, 0))$.

---

## 3. What Does Not Follow

1. **"The order of unadmitted leftovers does not affect which one can be admitted."**
   - Refuted by Witness 1 and Witness 2: Witness 1 admits $(0, 1)$ and blocks $(0, 0)$; Witness 2 admits $(0, 0)$ and blocks $(0, 1)$.

2. **"All bounded results are classified by the old count alone."**
   - Refuted by the existence of split equivalence classes under $\pi$. Within bound $n \le 2$ and 6 rounds, 388 ordered results project to 386 sixteenth results.

3. **"Two results with identical leftover counts have the same reachable successors."**
   - Refuted: immediate admission from State 1 leads to states with an assertion on $(0, 1)$, whereas immediate admission from State 2 leads to states with an assertion on $(0, 0)$.

---

## 4. Formalization in Lean 4

The file `Derivation.lean` provides machine-checked verification of the core claims:
- `OrderedRecord` defined as `List Pair`.
- `toCount` defined as the occurrence count projection.
- `isAdmissible rec p` defined as `mostRecentLeftover rec = some p`.
- `theorem witness_count_eq`: formal proof that `toCount witness1 p = toCount witness2 p` for all $p$.
- `theorem witness1_admissible` and `theorem witness1_not_admissible_other`: verification of LIFO admission and blocking.
- `theorem witness2_admissible` and `theorem witness2_not_admissible_other`: verification of the dual witness.
- `theorem witness_different_admissions`: proof that the admission predicates are not equivalent.
- `theorem falsifier_refuted`: constructive refutation of the falsifier.

The formalization relies on zero `sorry`, zero `admit`, and no axioms outside Lean's standard propositional extensionality (`propext`).

---

## 5. Computed Exploration and Census

The exploration from the empty state up to bound $n \le 2$ terms and 6 rounds records:

| Round | New Results | Cumulative Results | Attempts | Admissions |
| :---: | :---: | :---: | :---: | :---: |
| 0 | 1 | 1 | 0 | 0 |
| 1 | 1 | 2 | 1 | 0 |
| 2 | 2 | 4 | 4 | 0 |
| 3 | 7 | 11 | 18 | 0 |
| 4 | 22 | 33 | 91 | 0 |
| 5 | 88 | 121 | 436 | 6 |
| 6 | 267 | 388 | 2154 | 74 |

Comparison with sixteenth at round 6:
- Total ordered canonical results: 388
- Total sixteenth canonical results: 386
- Number of split classes: 2
- Minimal split witness pair: reached at depth 6.

All evidence regenerates byte-identically under `python evidence.py --check`.

---

## 6. Nearest Known Results

In external computational terminology (confined to this final section per repository rules):
The sixteenth derivation corresponds to a Petri net or commutative vector addition system where leftover resources accumulate in an unordered bag (multiset place) and can be consumed in any order.

The present seed introduces a pushdown stack discipline: the leftover storage operates as a LIFO stack. In formal language and automata theory, replacing a commutative multiset counter with a non-commutative stack strictly expands the computational and distinguishing power of the model (transitioning from vector addition reachability to pushdown automaton reachability). The order-sensitive feedback restricts transitions to top-of-stack operations and refines the state quotient by distinguishing permutation orbits of words over the pair alphabet.
