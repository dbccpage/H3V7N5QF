# Written Refusal: Literal Term Identity Under Refusal Semantics

## Abstract

We investigate the interaction between literal written term identity and refusal semantics under the seed change: *"Two results that differ only in how their terms are written are different results"*, replacing the twenty-first seed's identification of isomorphic results. In this setting, an obstructed change (which asserts some self-loop $xrx$) is refused, recorded, and changes nothing. We establish formally and demonstrate computationally over a declared finite bound ($B = 3$ terms, $R = 12$ rounds) that written sameness and refusal do not interact beyond a fiber-wise quotient of the same closure. At every round, the written refusal closure coincides identically with the Eighteenth derivation's written closure, refuting the hypothesis that refusal and written sameness interact dynamically to alter the reachable frontier.

---

## 1. Notions and Source Statuses

| Notion | Status | Description |
|---|---|---|
| The four kinds of changes | given | Identifying two terms; removing an assertion; adding a term; adding an assertion |
| Ban on self-loops | given | For no term $x$ may $xrx$ be asserted |
| Initial alternatives | given | $a \ne b$, $arb$ asserted; whether $bra$ is asserted is not given |
| Refusal semantics | given | An obstructed change is refused, recorded, and changes nothing |
| Written distinction | given | Two results that differ only in how their terms are written are different results |
| Declared finite bound | chosen | At most $B = 3$ terms, explored across $R = 12$ rounds |
| Dual sameness readings | chosen | FREE (permutations over all terms) vs ANCHORED (permutations preserving named terms $a, b$) |
| Refusal changes nothing | derived | If change $c$ on state $s$ asserts some $xrx$, the performed outcome is $s$ itself |
| Wave-by-wave identity with Eighteenth | computed | Reached depths, round waves, and frontier counts match Eighteenth identically |
| Fiber splitting over quotient | computed | Written identity strictly refines Twentyfirst's canonical quotient (fibers up to size 6) |
| Independence of closure from refusal | derived | Refusal transitions form identity loops on already-visited states |
| Hypothesis: non-trivial interaction | refuted | The written refusal closure is exactly Eighteenth's closure at every round |

---

## 2. Theoretical Analysis

### 2.1 Refusal Semantics and State Invariance

Under the seed specification, any attempt to execute a change $c$ on a legal state $s$ that would introduce a self-loop $xrx$ is obstructed:
$$\text{obstructed}(s, c) \iff \exists x, \, (x, x) \in \text{perform}(s, c).A$$
When obstructed, the change is refused:
$$\text{eval}(s, c) = \begin{cases} \text{perform}(s, c) & \text{if } \neg\text{obstructed}(s, c) \\ s & \text{if } \text{obstructed}(s, c) \end{cases}$$
Because $s$ is already present in the exploration set $\mathcal{D}$ prior to expanding its outgoing transitions, the refused outcome $\text{eval}(s, c) = s$ satisfies $s \in \mathcal{D}$. Consequently, a refused attempt never introduces a new state into the breadth-first search frontier.

### 2.2 Equivalence with Eighteenth Closure

In the Eighteenth derivation, obstructed changes were required to be answered by removing the obstruction or building structure. However, removal of the obstruction in an identification either restored the initial state or re-visited an existing state, while structure building introduced additions already reachable through unobstructed paths. Eighteenth's forward exploration (`explore_written`) tracked all states reachable via unobstructed changes as written.

Because Problem 04 expands along identical unobstructed transitions and collapses obstructed attempts to the self-state $s$, the set of novel states discovered at every round $r$ is identical:
$$\mathcal{W}_r^{(\text{P04})} = \mathcal{W}_r^{(\text{P18})} \quad \forall r \ge 0$$
Thus, the written refusal closure is exactly the Eighteenth closure at every round.

---

## 3. Bounded Exploration and Census

We execute exhaustive exploration from what is given up to bound $B = 3$ terms and $R = 12$ rounds across all four canonical configurations:

| Initial State | Reading | Written States | Waves (`new_per_round`) | Refusals | Frontier Exits | Quotient Classes (P21) | Splitting Fibers |
|---|---|---|---|---|---|---|---|
| $arb$ only | ANCHORED | 137 | `[1, 3, 8, 16, 23, 22, 21, 21, 15, 6, 1, 0, 0]` | 695 | 128 | 109 | 28 |
| $arb$ only | FREE | 69 | `[1, 3, 8, 15, 20, 15, 6, 1, 0, 0, 0, 0, 0]` | 348 | 64 | 20 | 15 |
| $arb \land bra$ | ANCHORED | 137 | `[1, 3, 8, 16, 23, 22, 21, 21, 15, 6, 1, 0, 0]` | 695 | 128 | 109 | 28 |
| $arb \land bra$ | FREE | 69 | `[1, 3, 8, 15, 20, 15, 6, 1, 0, 0, 0, 0, 0]` | 348 | 64 | 20 | 15 |

### 3.1 Independent Written State Census

For a graph on $n$ terms with no self-loops, there are $n(n-1)$ possible directed pairs. Each pair may independently be asserted or unasserted, yielding:
$$N_{\text{FREE}}(n) = 2^{n(n-1)}$$
- For $n = 1$: $2^0 = 1$ state.
- For $n = 2$: $2^2 = 4$ states.
- For $n = 3$: $2^6 = 64$ states.
$$\sum_{n=1}^3 N_{\text{FREE}}(n) = 1 + 4 + 64 = 69$$

For ANCHORED states, named vertices $(a, b)$ are tracked:
- For $n = 1$: names must be merged $(0, 0)$, giving $1 \times 1 = 1$ state.
- For $n \ge 2$: names can be distinct $(0, 1)$ or merged $(0, 0)$, giving $2 \times 2^{n(n-1)}$ states.
  - $n = 2$: $2 \times 4 = 8$ states.
  - $n = 3$: $2 \times 64 = 128$ states.
$$\sum_{n=1}^3 N_{\text{ANCHORED}}(n) = 1 + 8 + 128 = 137$$
Both independent counts match the explored totals completely.

### 3.2 Orbit-Stabilizer Consistency

For every reached state $s$, the automorphism group $\text{Aut}(s) = \{\sigma \in S_n \mid \sigma(s) = s\}$ and the orbit $\text{Orb}(s) = \{\sigma(s) \mid \sigma \in S_n\}$ satisfy:
$$n! = |\text{Orb}(s)| \cdot |\text{Aut}(s)|$$
This algebraic identity was verified on all 137 anchored and 69 free states with 0 failures.

---

## 4. What Does Not Follow

1. **It does not follow that refusal generates novel states.**
   - *Witness 1 (holds)*: Unobstructed change adding assertion $(0, 2)$ from 2 terms to 3 terms yields a novel state.
   - *Witness 2 (fails)*: Obstructed identification of $a$ and $b$ in what is given is refused, yielding the initial state itself (0 new states).

2. **It does not follow that literal term writings alter the round at which quotient classes appear.**
   - *Witness 1 (holds)*: The quotient class of the empty relation on 2 terms appears at round 1 in both Twentyfirst and Problem 04.
   - *Witness 2 (fails)*: No canonical quotient class appears earlier or later in the written setting than its minimal representation in Twentyfirst.

3. **It does not follow that the quotient map from written states to Twentyfirst is injective.**
   - *Witness 1 (injective on a one-term state)*: A state on one term has exactly one writing (fiber size 1).
   - *Witness 2 (strictly non-injective)*: The state with assertions $0r1, 1r2$ on three terms and the state with assertions $0r2, 2r1$ differ only in how their terms are written and share one quotient result, while remaining distinct written results; states with fewer symmetries have up to $3! = 6$ writings.

---

## 5. Formalization in Lean 4

The core theorems are formalized in `Derivation.lean`:
1. `written_step_preserves_legal`: Every performed step between written states preserves the `Legal` predicate.
2. `refusal_invariant`: If $\neg t.\text{Legal}$, then $\neg \text{Step } s \, t$.
3. `identify_given_refused`: The attempt to merge $a$ and $b$ in what is given is not a performed step.
4. `adding_self_loop_refused`: Adding $xrx$ to any legal state is refused.
5. `free_witness_distinct` and `anchored_witness_distinct`: Constructive existence of states identical under renaming equivalence but distinct as written results.

All proofs compile without `sorry`, `admit`, or non-standard axioms.

---

## 6. Nearest Known Results and Differences

The formalism connects to classical concepts in discrete mathematics and rewrite systems:
1. **Labeled vs Unlabeled Digraph Enumeration**: Labeled digraphs on $n$ vertices correspond to our literal written states ($2^{n(n-1)}$), whereas unlabeled digraphs correspond to Twentyfirst's canonical quotient classes (A000273 in OEIS).
2. **Guarded Rewriting and Refusal**: In transition systems, refusal semantics corresponds to a guarded command where a violation of the invariant aborts the transition into a no-op stutter step ($\text{skip}$).
3. **Difference from Prior Derivations**: Unlike Twentyfirst (which canonicalizes after every step), Problem 04 retains distinct representations, demonstrating that the refusal closure is fiber-wise conservative over the quotient.
