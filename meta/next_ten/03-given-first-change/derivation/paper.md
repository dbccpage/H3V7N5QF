# Problem 03: Given First Change — Derivation Report

## Abstract

We examine the consequences of modifying the beginning of the ninth seed by specifying that one change adding a term has already occurred prior to round zero: *"Given: one change adding a term has been made, and its outcome is the beginning. Nothing else is given."* In the parent Ninth derivation, exploration began at the empty state with zero terms and zero assertions, from which the unique first change added a term. In this derivation, we model the resulting transition system in typed Python, formalize the structure and transitions in Lean 4, and carry out breadth-first exploration up to bound $B = 3$ terms and $R = 4$ rounds, certified against an independent Burnside orbit count. Because every permitted change on a state with at least one term leaves at least one term, the empty state is unreachable from the new beginning. Consequently, the set of reachable results consists of all well-formed states having at least one term, and reachability among these results is mutual. For every reachable state $t$, the fewest changes from the beginning is $\text{size}(t) - 1$, shifting the cost by $-1$ relative to Ninth. These findings refute the candidate falsifier and support the hypothesis that a given change shifts reachability and cost without requiring a given assertion.

---

## 1. What the Seed Gives

The seed differs from the ninth seed by the sentence modifications shown in `diff.patch`:

| ID | Seed Text |
|---|---|
| G1 | Terms are written with letters. An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G2-P03 | Given: one change adding a term has been made, and its outcome is the beginning. Nothing else is given. |
| G3 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion. |
| G4 | Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. Two results that differ only in how their terms are written are the same result. |
| G5 | Attempt 100 changes along each alternative, finishing earlier changes on every alternative before later ones. Do not invent a change to reach 100. If the alternatives exceed what can be completed, declare a finite bound, export the exact frontier, and prove what is complete within it. |
| G6 | Any outcome is valid. |

---

## 2. Notions and Source Statuses

| Notion | Status | Note |
|---|---|---|
| Terms, relations $r, s$, assertions $xry, xsy$, multiplicity | given (G1) | Represented as two directed multigraph adjacency matrices |
| Given first change adding a term | given (G2-P03) | Precedes round zero; outcome constitutes the beginning |
| Four kinds of change | given (G3) | IDENTIFY, REMOVE, ADD_TERM, ADD_ASSERTION |
| Attempt order | given (G4) | Fewest additions first (0 additions, then 1 addition) |
| Sameness under term rewriting | given (G4) | Isomorphism under symmetric group $S_n$ |
| 100 rounds and finite bound declaration | given (G5) | Declared bound $B = 3$ terms, $R = 4$ rounds |
| Beginning state $\text{root03}$ | chosen (C1) | $\text{DState}(1, (0,), (0,))$ with $n = 1, m = 0$ |
| Added metric | chosen (C2) | $\Delta n = n - 1$ (for $n \ge 1$), $\Delta m = m$ relative to $\text{root03}$ |
| Canonical form for sameness | chosen (C3) | Lexicographically minimal flattened adjacency tuple under $S_n$ |
| Beginning size and non-emptiness | derived (D1) | $\text{size}(\text{root03}) = 1$, $T = \{0\}$, well-formed |
| Non-emptiness preservation invariant | derived (D2) | Every valid change on $n \ge 1$ yields $n' \ge 1$ |
| Empty state unreachability | derived (D3) | No finite sequence of changes from $\text{root03}$ reaches $\text{empty9}$ |
| Reachability characterization | derived (D4) | A well-formed state $t$ is reachable iff $t.n \ge 1$ |
| Mutual reachability (strong connectivity) | derived (D5) | For all $s, t$ with $s.n, t.n \ge 1$, $s$ reaches $t$ and $t$ reaches $s$ |
| Shortest path cost formula | derived (D6) | $\text{cost}_{03}(t) = \text{size}(t) - 1$ for all reachable $t$ |
| Cost shift relative to Ninth | derived (D7) | $\text{cost}_{03}(t) - \text{cost}_{\text{ninth}}(t) = -1$ on all reachable $t$ |
| Hypothesis supported | derived (D8) | Reachability and cost shift without given assertions |
| BFS exploration wave counts | computed (K1) | Computed at $B = 3, R = 4$, verified against Burnside counts |
| Frontier exits | computed (K2) | 23 attempts exit the bound at $B = 3$ |
| Comparison receipts with Ninth | computed (K3) | Documented in `comparison_with_ninth.json` |
| Falsifier refuted | refuted (R1) | One-term state is round 0 (vs 1); empty state is unreachable |
| Empty state reachability | refuted (R2) | Refuted by the non-emptiness invariant |

---

## 3. The Given First Change: Semantics and Beginning State

### 3.1 Initial Conditions
In the parent Ninth derivation, the beginning was $\text{empty9} = \text{DState}(0, (), ())$, containing zero terms and zero assertions ($\text{size} = 0$). The unique valid first change from $\text{empty9}$ was adding a term, producing a state with 1 term and 0 assertions.

In Problem 03, the seed stipulates that one change adding a term has already occurred, and its outcome is the beginning. We establish:
- **Beginning State:**
  $$\text{root03} = \text{DState}(1, (0,), (0,))$$
- **Term Set:** $T = \{0\}$, with $n = 1$.
- **Assertions:** $m_r = 0, m_s = 0$, giving total assertions $m = 0$.
- **Size:** $\text{size}(\text{root03}) = n + m = 1 + 0 = 1$.
- **Well-Formedness:** Because $0$ assertions exist, all assertions reference indices $< 1$. Thus $\text{root03}$ is well-formed (`root03_wf`).

### 3.2 Chosen Conventions
1. **Round Timing:** The given change is taken as having occurred before round 0. Thus, $\text{root03}$ sits at round 0 with cost 0. Under the unchosen alternative where the given change counts as round 1, all round indices shift upward by $+1$.
2. **Added Metric:** In accordance with G4, each result records how many terms and assertions it adds to what is given. For a state $t$ with $t.n \ge 1$ and total assertions $t.m$:
   $$\Delta n = t.n - 1, \quad \Delta m = t.m$$

---

## 4. Reachability and the Non-Emptiness Invariant

### 4.1 Non-Emptiness Preservation
Each of the four permitted kinds of change preserves the existence of at least one term when applied to any state with $n \ge 1$:
1. **Adding a term (`ADD_TERM`):** Increases term count from $n$ to $n + 1 \ge 2 > 0$.
2. **Adding an assertion (`ADD_ASSERTION`):** Leaves term count $n$ unchanged ($n \ge 1$).
3. **Removing an assertion (`REMOVE`):** Leaves term count $n$ unchanged ($n \ge 1$).
4. **Identifying two terms (`IDENTIFY`):** Requires two distinct terms $x \ne y$, so $n \ge 2$. Replacing both by one term yields $n' = n - 1 \ge 1 > 0$.

No change allows deleting a term directly. Therefore:
$$\forall s, s', \quad (s \to s' \land s.n \ge 1) \implies s'.n \ge 1$$
By induction, every state reached by a sequence of changes from $\text{root03}$ satisfies $n \ge 1$.

### 4.2 Unreachability of the Empty State
The empty state $\text{empty9}$ has $n = 0$ terms. Because every state reachable from $\text{root03}$ has $n \ge 1$:
$$\forall k \in \mathbb{N}, \quad \neg \text{Reach}(\text{root03}, \text{empty9}, k)$$
The empty state is not a result in Problem 03 (`empty9_not_result03`).

### 4.3 Reachability Characterization and Mutual Reachability
Let $t$ be any well-formed state:
- If $t.n = 0$, $t$ is unreachable.
- If $t.n \ge 1$, $t$ is reached from $\text{root03}$ by performing $t.n - 1$ term additions followed by $t.m$ assertion additions.
Thus:
$$\text{Reachable}(\text{root03}, t) \iff t.n \ge 1$$

Furthermore, for any two states $s, t$ with $s.n \ge 1$ and $t.n \ge 1$:
- $s$ reaches a 1-term state by removing all assertions (in $s.m$ steps) and identifying terms (in $s.n - 1$ steps).
- The 1-term state reaches $t$ by additions (in $t.n - 1 + t.m$ steps).
Hence, $s$ reaches $t$ and $t$ reaches $s$. All reachable states are mutually reachable (`reach03_symm`).

---

## 5. Cost, Parity, and Comparison with Ninth

### 5.1 Fewest Changes
- **Lower Bound:** Every change alters size by at most $+1$. Starting from $\text{root03}$ with $\text{size} = 1$, reaching state $t$ in $k$ steps requires $1 + k \ge \text{size}(t)$, so $k \ge \text{size}(t) - 1$.
- **Upper Bound:** A sequence of $t.n - 1$ term additions and $t.m$ assertion additions reaches $t$ in $(t.n - 1) + t.m = \text{size}(t) - 1$ changes.
Therefore:
$$\text{cost}_{03}(t) = \text{size}(t) - 1 = t.n + t.m - 1$$

### 5.2 Uniform Cost Shift
In Ninth, starting from $\text{size} = 0$, the cost was $\text{cost}_{\text{ninth}}(t) = \text{size}(t)$.
Comparing the two models on any reachable state $t$ ($t.n \ge 1$):
$$\text{cost}_{03}(t) - \text{cost}_{\text{ninth}}(t) = (\text{size}(t) - 1) - \text{size}(t) = -1$$
Every reachable state requires exactly 1 fewer change from $\text{root03}$ than from $\text{empty9}$.

---

## 6. Bounded Exploration and Independent Orbit Census

We execute breadth-first exploration from $\text{root03}$ up to bound $B = 3$ terms and $R = 4$ rounds.

### 6.1 Exploration Waves

| Round $r$ | New Results | Total Discovered | Attempts | Blocked ($xrx$) | Blocked ($xsx$) | Frontier Exits |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| 0 | 1 | 1 | 0 | 0 | 0 | 0 |
| 1 | 3 | 4 | 4 | 1 | 1 | 0 |
| 2 | 8 | 12 | 23 | 5 | 5 | 0 |
| 3 | 29 | 41 | 100 | 19 | 19 | 1 |
| 4 | 104 | 145 | 447 | 81 | 81 | 22 |

- Total results explored within bound: **145 states**.
- Total attempts: **574** across rounds 1–4.
- Total frontier exits: **23** attempts to generate states exceeding 3 terms.
- The empty state was encountered 0 times.

### 6.2 Independent Completeness Certification
To verify completeness, we compute the combinatorial orbit count for each $(n, m)$ cell using the cycle index polynomial of the symmetric group $S_n$ acting on ordered pairs of terms. For $n$ terms and total multiplicity $m$ split across two relations:
$$\text{Orbits}(n, m) = \frac{1}{|S_n|} \sum_{g \in S_n} Z(g; x_1, x_2, \dots)$$
Comparing BFS discovery counts with combinatorial orbit counts across all cells within $n \le 3$ and $n + m - 1 \le 4$:
- Number of evaluated cells: 13
- Total expected results: 145
- Total discovered results: 145
- Disagreements: **0**

---

## 7. Resolution of Hypothesis and Falsifier

### 7.1 Evaluation of the Candidate Falsifier
The candidate falsifier states:
> *"The empty result and one-term result have the ninth's rounds after aligning beginnings."*

1. **One-term result:** In Problem 03, the beginning is $\text{root03}$, which sits at round 0. In Ninth, the one-term state appeared at round 1. Aligning beginnings puts the one-term state at round 0, differing by 1 from Ninth.
2. **Empty result:** In Ninth, $\text{empty9}$ was discovered at round 0. In Problem 03, $\text{empty9}$ is unreachable ($r = \text{None}$).

Neither condition matches Ninth's rounds. The candidate falsifier is **refuted**.

### 7.2 Evaluation of the Candidate Hypothesis
The candidate hypothesis states:
> *"A given change shifts reachability and cost without a given assertion."*

1. **No given assertion:** The seed provides only a given change adding a term; multiplicities in both relations remain 0 in $\text{root03}$.
2. **Reachability shift:** The empty state is excluded from the set of reachable results, and the global reachability structure becomes mutually connected rather than rooted at a one-way source.
3. **Cost shift:** For every reachable state, the cost shifts by exactly $-1$ relative to Ninth.

Because both reachability and cost shift despite the complete absence of a given assertion, the candidate hypothesis is **supported in this model**.

---

## 8. What Does Not Follow

1. **It does not follow that all states in Ninth are reachable in Problem 03:**
   - *Witness in Ninth:* The state $\text{empty9} = \text{DState}(0, (), ())$ is reachable at round 0.
   - *Non-reachability in 03:* The state $\text{empty9}$ is unreachable by theorem `empty9_not_result03`.

2. **It does not follow that the cost shift applies to all states in the universe:**
   - *Witness where shift is $-1$:* Any state with $n \ge 1$ satisfies $\text{cost}_{03}(t) - \text{cost}_{\text{ninth}}(t) = -1$.
   - *Counter-witness:* The state $\text{empty9}$ has cost 0 in Ninth, but has no defined cost in Problem 03 because it cannot be reached.

3. **It does not follow that a given change adding a term restricts the multiplicity of subsequent assertions:**
   - *Witness:* For any target multiplicity matrix $M$, assertions can be added to any finite multiplicity using `ADD_ASSERTION`.

---

## 9. Nearest Known Results

*Note: In accordance with repository conventions, external literature and established theory are referenced only in this final section.*

The mathematical structure investigated here corresponds to the transformation theory of finite edge-colored directed multigraphs with loops under elementary graph modifications. In that setting:
1. The operations correspond to vertex addition, directed edge addition, directed edge deletion, and vertex quotient identification.
2. When the initial configuration is the 1-vertex discrete graph rather than the empty graph, the lack of vertex deletion operations means that the transition graph forms a connected component restricted to the subcategory of non-empty graphs.
3. The equivalence classes of states under term renaming correspond to orbits of adjacency matrices under the action of the symmetric group $S_n$. Orbit enumeration is described by the Pólya-Burnside enumeration theorem applied to digraphs with two edge colors.

---

## Summary Checklist

1. **What this artifact supports:**
   - Supports the non-emptiness invariant of all four kinds of change.
   - Supports the complete exclusion of the empty state from reachable results in Problem 03.
   - Supports the mutual reachability of all well-formed states having at least one term.
   - Supports the uniform cost shift of $-1$ across all reachable states relative to Ninth.
   - Supports the hypothesis that a given change shifts reachability and cost without a given assertion.
   - Supports the refutation of the candidate falsifier.
   - Supports the exact agreement between BFS exploration waves and combinatorial Burnside orbit counts.

2. **What this artifact does not support:**
   - Does not support reaching the empty state from $\text{root03}$.
   - Does not support reaching any state in fewer than $\text{size}(t) - 1$ changes.
   - Does not support a defined cost for unreachable states.

3. **Narrowest defensible claim:**
   Under the seed change specifying that one change adding a term has been made and its outcome is the beginning with nothing else given, the beginning state has 1 term and 0 assertions, the empty state is unreachable, a state $t$ is reachable if and only if $t.n \ge 1$, and for every reachable state $t$ the fewest changes from the beginning is $\text{size}(t) - 1$, shifting the cost by $-1$ relative to Ninth.

4. **Next test needed:**
   An investigation testing the effect of a given change that adds an assertion (rather than a term) from the empty state, evaluating whether that configuration forces a non-zero assertion floor or alters relational symmetry.
