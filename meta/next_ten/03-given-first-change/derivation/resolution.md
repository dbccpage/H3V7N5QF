# Resolution of Hypothesis and Falsifier for Problem 03 (Given First Change)

## 1. Candidate Context and Stated Stakes

Candidate ID: **C09** (`meta/next_ten/03-given-first-change/`)  
Parent Derivation: **Ninth** (`code/ninth/`, `lean4/Ninth/`, `paper/ninth/`)  

- **Hypothesis, open:** A given change shifts reachability and cost without a given assertion.
- **Falsifier:** The empty result and one-term result have the ninth's rounds after aligning beginnings.

## 2. Definitional Clarification and Background

In the parent Ninth derivation:
1. **The Empty Beginning:**
   The initial state is $\text{empty9} = \text{DState}(0, (), ())$ with no terms and nothing asserted ($\text{size} = 0$).
2. **First Change and One-Way Reachability:**
   From $\text{empty9}$, the only legal first change is adding a term (`first_change_adds_term9`), reaching the unique 1-term state with 0 assertions at round 1.
   Every change applied to a state with at least one term produces a state with at least one term (`Step9.nonempty`). Consequently, $\text{empty9}$ has in-degree 0: once left, it can never be returned to.
3. **Cost in Ninth:**
   The fewest changes from $\text{empty9}$ to any reachable state $t$ is $\text{cost}_{\text{ninth}}(t) = \text{size}(t) = t.n + t.m$.

In Problem 03:
- The seed modifies paragraph 3: *"Given: one change adding a term has been made, and its outcome is the beginning. Nothing else is given."*
- The beginning state is $\text{root03} = \text{DState}(1, (0,), (0,))$, which has $n = 1$ term, $m = 0$ assertions, and $\text{size} = 1$.
- No assertion is given; the multiplicity of every pair under $r$ and $s$ is 0.

## 3. Analysis of Reachability and Cost

### 3.1 Unreachability of the Empty State
Every change in this system preserves non-emptiness:
- Adding a term increases the term count from $n$ to $n + 1 \ge 2 > 0$.
- Identifying two terms requires at least two terms ($n \ge 2$) and decreases the count to $n - 1 \ge 1 > 0$.
- Removing an assertion leaves the term count $n$ invariant.
- Adding an assertion leaves the term count $n$ invariant.

Because the beginning $\text{root03}$ has $n = 1 > 0$, every state reachable from $\text{root03}$ by any finite sequence of changes has $n \ge 1$.
Therefore:
$$\text{empty9} \text{ is not reachable from } \text{root03}$$
Formally checked in Lean 4 as `empty_not_reachable_from_root03` and `empty_not_result03`.

### 3.2 Exact Reachability Characterization
Let $t$ be any well-formed state:
- If $t.n = 0$, then $t = \text{empty9}$, which is unreachable.
- If $t.n \ge 1$, then $t$ can be reached from $\text{root03}$ by adding $t.n - 1$ terms followed by $t.m$ assertion additions.
Hence:
$$\text{Reachable}(\text{root03}, t) \iff t.n \ge 1$$
The constructive addition path above establishes the reverse direction; Lean `empty_not_result03` demonstrates the exclusion of zero-term states. The full equivalence is also checked over the declared finite census.

### 3.3 Mutual Reachability (Strong Connectivity)
In Ninth, reachability from the empty state was strictly one-way: $\text{empty9}$ reached every state, but no state could reach $\text{empty9}$.
In Problem 03, the empty state is excluded. For any two reachable states $s$ and $t$ with $s.n \ge 1$ and $t.n \ge 1$:
- State $s$ can reach a 1-term state by identifying terms and removing assertions.
- A 1-term state can reach state $t$ by term and assertion additions.
Thus, $s$ reaches $t$ and $t$ reaches $s$. Reachability among all results is mutual by the paths just described. The Lean formalization establishes the non-emptiness invariant used here.

### 3.4 Cost Characterization and Shift
For any reachable state $t$ ($t.n \ge 1$):
- Each change increases state size by at most 1.
- Because $\text{size}(\text{root03}) = 1$, any path of length $k$ to $t$ satisfies $\text{size}(t) \le 1 + k$, so $k \ge \text{size}(t) - 1$.
- A pure addition path reaches $t$ in exactly $(t.n - 1) + t.m = \text{size}(t) - 1$ steps.
Therefore:
$$\text{cost}_{03}(t) = \text{size}(t) - 1 = t.n + t.m - 1$$
Compared with Ninth:
$$\text{cost}_{03}(t) - \text{cost}_{\text{ninth}}(t) = (\text{size}(t) - 1) - \text{size}(t) = -1$$
For the empty state:
$$\text{cost}_{\text{ninth}}(\text{empty9}) = 0, \quad \text{cost}_{03}(\text{empty9}) = \text{undefined (unreachable)}$$

## 4. Evaluation of the Falsifier

The candidate falsifier states:
> *"The empty result and one-term result have the ninth's rounds after aligning beginnings."*

We evaluate both conditions after aligning beginnings:
1. **The One-Term Result:**
   - In Problem 03, the beginning is the one-term state $\text{root03}$. Its discovery round is round 0 ($\text{cost}_{03} = 0$).
   - In Ninth, the beginning was $\text{empty9}$ (round 0), and the one-term state was discovered at round 1 ($\text{cost}_{\text{ninth}} = 1$).
   - The round of the one-term state is 0 in Problem 03, differing by 1 from Ninth's round 1.
2. **The Empty Result:**
   - In Ninth, $\text{empty9}$ was discovered at round 0.
   - In Problem 03, $\text{empty9}$ is never reachable at any round ($r = \text{None}$).
   - The empty result does not have Ninth's round (or any round).

Because neither the one-term result nor the empty result exhibits Ninth's rounds after aligning beginnings, the candidate falsifier is **refuted**.

## 5. Evaluation of the Hypothesis

The candidate hypothesis states:
> *"A given change shifts reachability and cost without a given assertion."*

We observe:
1. **No Given Assertion:**
   The seed provides one given change adding a term. No assertions are given; both relations $r$ and $s$ have multiplicity 0 everywhere in $\text{root03}$.
2. **Reachability Shift:**
   The set of reachable results is strictly altered: the empty state is eliminated. Furthermore, the global topology shifts from a directed system with a strict one-way source ($\text{empty9}$) to a strongly connected system where all reachable results are mutually reachable.
3. **Cost Shift:**
   For every reachable state $t$, the fewest changes from the beginning is shifted by exactly $-1$:
   $$\text{cost}_{03}(t) = \text{cost}_{\text{ninth}}(t) - 1$$

Because both reachability and cost shift despite the absence of any given assertion, the candidate hypothesis is **supported in this model**.

## 6. Summary Checklist

1. **What this artifact supports:**
   - Supports the exclusion of the empty state from the set of reachable results under Problem 03.
   - Supports the mutual reachability of all well-formed states having at least one term.
   - Supports the exact cost formula $\text{cost}_{03}(t) = \text{size}(t) - 1$ for all reachable states.
   - Supports the uniform cost shift of $-1$ relative to Ninth across all reachable states.
   - Supports the candidate hypothesis that a given change shifts reachability and cost without a given assertion.
   - Supports the refutation of the candidate falsifier.

2. **What this artifact does not support:**
   - Does not support reaching the empty state from any nonempty state under the four given changes.
   - Does not support reaching any state in fewer than $\text{size}(t) - 1$ changes.
   - Does not support a cost shift on the empty state (as it is not reachable).

3. **Narrowest defensible claim:**
   Under the seed specifying that one change adding a term has been made and its outcome is the beginning with nothing else given, the beginning state has 1 term and 0 assertions, the empty state is unreachable, a state $t$ is reachable if and only if $t.n \ge 1$, and for every reachable state $t$ the fewest changes from the beginning is $\text{size}(t) - 1$, shifting the cost by $-1$ relative to Ninth.

4. **Next test needed:**
   A test evaluating whether a given change adding an assertion (rather than a term) from the one-term state introduces asymmetry between relations or creates an irreducible non-zero assertion floor.
