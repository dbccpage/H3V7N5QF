# Problem 01: Remove Bare Term — Derivation Report

## Abstract

We investigate the consequences of adding a fifth kind of change to the seventh seed: *"removing a term that names no assertion deletes that term and nothing asserted"*. In the parent Seventh derivation, the empty state had in-degree 0; once left via term addition, the system could never return, establishing a one-way reachability structure. In this work, we analyze the transition semantics, formalize the operation in Lean 4 and typed Python, and explore the state space breadth-first under a declared term bound. The one-term state asserting nothing possesses an outgoing bare-term removal transition that returns directly to the empty state in 1 change, closing a 2-step cycle from the empty beginning. This result refutes the candidate falsifier and supports the hypothesis that bare-term removal destroys the empty state's one-way reachability. Furthermore, because any state can clear its assertions and then remove its bare terms, every state reaches the empty state, establishing that all states in this system are mutually reachable.

---

## 1. What the Seed Gives

The seed differs from the seventh seed by the sentence modifications shown in `diff.patch`:

| ID | Seed Text |
|---|---|
| G1 | Terms are written with letters. |
| G2 | An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G3 | Nothing is given: to begin with there are no terms and nothing is asserted. |
| G6-P01 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion; removing a term that names no assertion. Nothing else is a change. |
| G7-P01 | Identifying two terms replaces both by one term in every assertion. Removing a term that names no assertion deletes that term and nothing asserted. |
| G11 | Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative, finishing earlier changes on every alternative before later ones. Do not invent a change to reach 100. If the alternatives exceed what can be completed, declare a finite bound, export the exact frontier, and prove what is complete within it. |
| G14 | Any outcome is valid. |

---

## 2. Notions and Source Statuses

| Notion | Status | Note |
|---|---|---|
| Term, assertion `xry`, multiplicity | given (G1, G2) | Counted multigraph representation |
| Empty beginning `empty` | given (G3) | 0 terms, 0 assertions |
| 5 kinds of change | given (G6-P01) | IDENTIFY, REMOVE, ADD_TERM, ADD_ASSERTION, REMOVE_BARE_TERM |
| Bare term condition | given (G6-P01, G7-P01) | A term that names no assertion in either position |
| Bare-term removal semantics | given (G7-P01) | Deletes that term and nothing asserted |
| Well-formedness preservation | derived | Checked in Lean 4 (`removeBare_wf`) and Python |
| Counted assertion preservation | derived | Checked in Lean 4 (`sumGrid`, `removeBare`) and Python |
| Size decrement by one | derived | Bare-term removal lowers term count by 1 and keeps multiplicity sum |
| 1-step return from one-term bare state | derived | Witnessed by `oneTermBare -> empty` |
| 2-step cycle `empty -> oneTermBare -> empty` | derived | Checked in Lean 4 (`two_step_cycle`, `empty_returns_in_two_steps`) |
| Falsifier refutation | refuted | Counterexample $\text{oneTermBare}$ reaches `empty` in 1 change ($\le 2$); computed in Python |
| Hypothesis supported | derived | Empty in-degree is positive; one-way reachability eliminated; computed in Python |
| Strong connectivity (mutual reachability) | derived | Any $s$ reaches `empty` in $\text{size}(s)$ steps; `empty` reaches any $t$ |
| Cost from empty equals size | derived | Lower bound from unit size changes; upper bound via additions |
| Bounded BFS exploration waves | computed | Explored at bounds $B=2, 3$ across declared rounds |
| Independent Burnside orbit counts | computed | Exact combinatorial census matching BFS wave counts |
| Nearest known results | derived | Restricted to Section 9 |

---

## 3. The Fifth Change: Semantics and Invariants

### 3.1 Formal Definition of a Bare Term
In a state $s$ with $n$ terms and multiplicity matrix $M$, a term $t \in \{0, \dots, n-1\}$ is *bare* if and only if:
$$\forall y \in \{0, \dots, n-1\}, \quad M(t, y) = 0 \quad \text{and} \quad M(y, t) = 0$$
That is, $t$ is neither the source nor the target of any assertion with positive multiplicity.

### 3.2 State Transition Under Bare-Term Removal
When a bare term $t$ is removed from a state $s$ with $n \ge 1$ terms:
1. If $n = 1$, the resulting state is the empty state $\text{empty} = \text{State}(0, ())$.
2. If $n > 1$, the new term count is $n - 1$. Terms $k < t$ keep their index $k$, while terms $k > t$ are re-indexed to $k - 1$.
3. For all pairs $(u, v) \in \{0, \dots, n-2\}^2$, the multiplicity is:
   $$M'(u, v) = M(\text{unshift}(t, u), \text{unshift}(t, v))$$
   where $\text{unshift}(t, k) = k$ if $k < t$, and $k + 1$ if $k \ge t$.

### 3.3 Preservation Invariants
- **Well-Formedness:** Because $\text{unshift}(t, k) \ne t$, any positive multiplicity in $M'$ corresponds to a positive multiplicity in $M$ between non-$t$ terms, which are bounded by $n - 1$. Thus $s.\text{WF}$ implies $(s.\text{removeBare}(t)).\text{WF}$.
- **Assertion Preservation:** Since all entries involving $t$ are 0, the sum of multiplicities across all pairs is identical:
  $$\sum_{u, v < n-1} M'(u, v) = \sum_{x, y < n} M(x, y)$$
  Bare-term removal deletes the term and *nothing asserted*.
- **Size Change:** The size of a state is defined as $\text{size}(s) = n + \sum M$. Because $n' = n - 1$ and $\sum M' = \sum M$, we have $\text{size}(s') = \text{size}(s) - 1$.

---

## 4. The Two-Step Cycle and Resolution of Hypothesis

### 4.1 Concrete Witness
Starting from `empty` ($\text{size} = 0$):
1. **Change 1 (ADD_TERM):**
   $$\text{empty} \xrightarrow{\text{ADD\_TERM}} \text{oneTermBare} = \text{State}(1, (0,))$$
   The resulting state has 1 term and 0 assertions.
2. **Change 2 (REMOVE_BARE_TERM):**
   In $\text{oneTermBare}$, term 0 names no assertion. Removing term 0 deletes term 0 and leaves no terms:
   $$\text{oneTermBare} \xrightarrow{\text{REMOVE\_BARE\_TERM}(0)} \text{empty}$$

### 4.2 Resolution of the Falsifier
The candidate falsifier states:
> *"No nonempty result reaches the empty beginning within two changes."*

This statement is refuted in this model. The state $\text{oneTermBare}$ is a nonempty result ($n = 1 > 0$) and reaches $\text{empty}$ in exactly 1 change, which satisfies the condition $\le 2$.

### 4.3 Resolution of the Hypothesis
The candidate hypothesis states:
> *"A bare-term removal destroys the empty state's one-way reachability."*

In the parent Seventh derivation, the empty state had in-degree 0: no transition entered it. In Problem 01, incoming transitions exist from nonempty states. The empty beginning is part of non-trivial cycles. This confirms and supports the hypothesis.

---

## 5. Global Reachability: Strong Connectivity

The addition of bare-term removal transforms the global topology of the state space:

1. **Path to Empty:**
   Let $s$ be any well-formed state with $n$ terms and $m$ assertions.
   - Performing $m$ assertion removals clears all assertions, reaching an assertion-free state with $n$ bare terms.
   - Performing $n$ bare-term removals deletes all terms one by one, reaching $\text{empty}$.
   Total changes: $m + n = \text{size}(s)$.
2. **Path from Empty:**
   From $\text{empty}$, any state $t$ with $n_t$ terms and $m_t$ assertions is reached by $n_t$ term additions followed by $m_t$ assertion additions.
   Total changes: $n_t + m_t = \text{size}(t)$.
3. **Mutual Reachability:**
   For any two states $s$ and $t$, the concatenated path $s \to \text{empty} \to t$ has length $\text{size}(s) + \text{size}(t)$.
   Thus, every state reaches every other state. The state space is strongly connected.

---

## 6. Cost, Parity, and Shortest Sequences

- **Unit Step Invariant:**
  - Additions (`ADD_TERM`, `ADD_ASSERTION`) increase $\text{size}$ by $+1$.
  - Non-additions (`REMOVE`, `IDENTIFY`, `REMOVE_BARE_TERM`) decrease $\text{size}$ by $-1$.
- **Fewest Changes from Empty:**
  Because $\text{size}(\text{empty}) = 0$ and each step increases size by at most 1, reaching state $s$ requires at least $\text{size}(s)$ changes. Since $\text{size}(s)$ additions reach $s$, the cost from `empty` is:
  $$\text{cost}(s) = \text{size}(s) = s.n + s.m$$
- **Parity:**
  Any sequence of $k$ changes from `empty` to $s$ satisfies $k \equiv \text{size}(s) \pmod 2$. In particular, returning to `empty` requires an even number of changes.

---

## 7. Bounded Exploration and Independent Orbit Counts

We conduct breadth-first exploration from `empty` under declared bounds:

### 7.1 Exploration Waves ($B = 2$ terms, $R = 6$ rounds)

| Round $r$ | Discovered Count | Canonical States Discovered | Theoretical Burnside Count | Match? |
|:---:|:---:|---|:---:|:---:|
| 0 | 1 | `State(0, ())` | 1 | Yes |
| 1 | 1 | `State(1, (0,))` | 1 | Yes |
| 2 | 2 | `State(2, 0)` [1], `State(1, 1)` [1] | $1 + 1 = 2$ | Yes |
| 3 | 3 | `State(2, 1)` [2], `State(1, 2)` [1] | $2 + 1 = 3$ | Yes |
| 4 | 7 | `State(2, 2)` [6], `State(1, 3)` [1] | $6 + 1 = 7$ | Yes |
| 5 | 11 | `State(2, 3)` [10], `State(1, 4)` [1] | $10 + 1 = 11$ | Yes |
| 6 | 20 | `State(2, 4)` [19], `State(1, 5)` [1] | $19 + 1 = 20$ | Yes |

Total discovered within bound 2 up to round 6: **45 canonical states**.
At every round $r$, the count of discovered states matches the independent Burnside orbit count:
$$\text{Theoretical}(r) = [r = 0] + [r \ge 1] + [r \ge 2] \cdot \text{two\_term\_count}(r - 2)$$
where $\text{two\_term\_count}(m) = \frac{1}{2} \left( \binom{m+3}{3} + [m \text{ even}]\left(\frac{m}{2} + 1\right) \right)$.

---

## 8. What Does Not Follow

To maintain strict claim discipline, we identify properties that do *not* follow from this model, with concrete legal witnesses:

1. **It does not follow that every term can be removed:**
   - *Witness where term 0 can be removed:* State $s_1 = \text{State}(1, (0,))$. Term 0 names no assertion; removal is valid.
   - *Witness where term 0 cannot be removed:* State $s_2 = \text{State}(1, (1,))$. Term 0 names an assertion (a self-loop); removal as a bare term is invalid under G7-P01.

2. **It does not follow that the empty state can be returned to in an odd number of changes:**
   - *Witness for even steps:* Path `empty` $\to$ `oneTermBare` $\to$ `empty` has length 2 (even).
   - *Impossibility for odd steps:* Every change changes size by $\pm 1$. Starting at size 0, any state reached after an odd number of changes has odd size, whereas `empty` has size 0 (even).

3. **It does not follow that bare-term removal reduces the shortest distance from `empty` to any result:**
   - *Witness:* For any result $s$, the fewest changes from `empty` remains $\text{size}(s)$, which is achieved by pure additions without removals.

---

## 9. Nearest Known Results

*Note: In accordance with repository conventions, known external theory is referenced only in this final section.*

The model investigated here corresponds to the transformation theory of finite directed multigraphs with loops under elementary graph surgery operations. The five kinds of changes correspond to:
1. Vertex contraction / quotient identification.
2. Directed edge deletion.
3. Isolated vertex insertion.
4. Directed edge insertion.
5. Isolated vertex deletion.

In graph-theoretic terms:
- The parent Seventh derivation modeled directed multigraph surgery without isolated vertex deletion, yielding a transition system where the empty graph $\emptyset$ has in-degree 0.
- Introducing isolated vertex deletion restores the inverse transition to vertex insertion, rendering the transition system strongly connected across all finite directed multigraphs.
- Isomorphism classes of states under term renaming correspond to graph orbits under the action of the symmetric group $S_n$. The exact counts of orbits by edge count are given by the cycle index of $S_n$ acting on pairs, formalized via Burnside's Lemma.

---

## Summary Checklist

1. **What this artifact supports:**
   - Supports the existence of the 2-step cycle `empty -> oneTermBare -> empty`.
   - Supports the refutation of the falsifier ("No nonempty result reaches the empty beginning within two changes").
   - Supports the hypothesis that bare-term removal destroys the empty state's one-way reachability.
   - Supports the strong connectivity and mutual reachability of all states in the model.
   - Supports the exact match between BFS exploration waves and closed-form Burnside orbit counts.

2. **What this artifact does not support:**
   - Does not support deletion of vertices that have incident edges.
   - Does not support returning to the empty state in an odd number of steps.

3. **Narrowest defensible claim:**
   Under the seed change adding bare-term removal as a fifth change, the empty beginning has incoming transitions from nonempty states, admits a 2-step cycle with the 1-term assertion-free state, and every state reaches the empty state in $\text{size}(s)$ changes.

4. **Next test needed:**
   A formulation where removing a term with incident assertions is permitted and deletes all incident assertions simultaneously.
