# Resolution of Hypothesis and Falsifier for Problem 01 (Remove Bare Term)

## 1. Candidate Context and Stated Stakes

Candidate ID: **C19** (`meta/next_ten/01-remove-bare-term/`)  
Parent Derivation: **Seventh** (`code/seventh/`, `lean4/Seventh/`, `paper/seventh/`)  

- **Hypothesis, open:** A bare-term removal destroys the empty state's one-way reachability.
- **Falsifier:** No nonempty result reaches the empty beginning within two changes.

## 2. Definitional Clarification of Terms

In the parent Seventh derivation:
1. **The Empty Beginning:**
   The initial state is `empty = State(0, ())` with no terms and nothing asserted.
2. **One-Way Reachability in Parent (Seventh):**
   In the Seventh derivation, every change from a state with at least one term yields a state with at least one term (formally checked in Lean as `Step7.nonempty`). Consequently, the empty state has in-degree 0: once the system transitions out of the empty state via `ADD_TERM`, it can never return. Reachability from the empty beginning is strictly one-way.
3. **Problem 01 Bare-Term Removal:**
   Problem 01 introduces a fifth kind of change: "removing a term that names no assertion deletes that term and nothing asserted."
   A term $t$ names no assertion if and only if for all terms $y$, the multiplicity of $t r y$ is 0 and the multiplicity of $y r t$ is 0.
   When $t$ is removed, the term count decreases from $n$ to $n - 1$, and all remaining term indices greater than $t$ shift down by one, leaving all asserted multiplicities intact.

## 3. Empirical and Formal Verification

The formal model (`model.py`), test suite (`test_derivation.py`), and formal Lean 4 theorems (`Derivation.lean`) establish the following evidence:

### 3.1 The Concrete Witness State
Consider the state reached by one addition of a term from the empty state:
$$\text{oneTermBare} = \text{State}(1, (0,))$$
This state has:
- Term count: $n = 1 > 0$ (it is a nonempty result).
- Assertion count: $m = 0$.
- Term $0$ has no assertions incident to it in either direction. Thus $0$ is a bare term.

### 3.2 One-Step Transition to Empty
On $\text{oneTermBare}$, term $0$ names no assertion.
The change:
$$c = \text{Change}(\text{Kind.REMOVE\_BARE\_TERM}, 0)$$
is valid under the seed rule.
Performing $c$ on $\text{oneTermBare}$ deletes term $0$ and leaves 0 terms and 0 assertions:
$$\text{perform}(\text{oneTermBare}, c) = \text{empty}$$
This transition takes exactly **1 change**.

### 3.3 The Two-Step Cycle
Beginning from the empty state:
1. Step 1: `empty` $\xrightarrow{\text{ADD\_TERM}}$ `oneTermBare`
2. Step 2: `oneTermBare` $\xrightarrow{\text{REMOVE\_BARE\_TERM}(0)}$ `empty`

This exhibits an explicit, closed 2-step cycle:
$$\text{empty} \to \text{oneTermBare} \to \text{empty}$$
The return to the empty beginning is accomplished in exactly 2 changes from `empty`, and in exactly 1 change from the nonempty result `oneTermBare`.

### 3.4 Global Reachability Classification
Beyond the 2-step cycle, bare-term removal alters the global reachability structure:
- For any state $s$ with $n$ terms and $m$ assertions:
  1. Removing assertions one by one lowers total multiplicity to 0 in $m$ changes, reaching a state with $n$ bare terms.
  2. Removing the bare terms one by one deletes all terms in $n$ changes, reaching `empty`.
  Thus, every state $s$ reaches `empty` in $m + n = \text{size}(s)$ changes.
- From `empty`, any state $t$ is reached by adding $t.n$ terms followed by $t.m$ assertions, taking $t.n + t.m = \text{size}(t)$ changes.
- By path concatenation, every state $s$ reaches every state $t$ in at most $\text{size}(s) + \text{size}(t)$ changes.
All states in the universe of Problem 01 are mutually reachable. The state space is strongly connected.

## 4. Final Resolution

The investigation resolves the two propositions as follows:

1. **The Falsifier is REFUTED:**
   The falsifier asserts that "No nonempty result reaches the empty beginning within two changes."
   This statement is shown false in this model by the concrete counterexample $\text{oneTermBare}$:
   - $\text{oneTermBare}$ is a nonempty result ($n = 1$).
   - It reaches the empty beginning in exactly 1 change, satisfying $1 \le 2$.
   Because a nonempty result reaches `empty` in fewer than two changes, the falsifier condition fails to hold.

2. **The Hypothesis is SUPPORTED in this Model:**
   The hypothesis asserts that "A bare-term removal destroys the empty state's one-way reachability."
   This statement is supported:
   - In the parent Seventh derivation, reachability out of the empty state was strictly one-way (in-degree 0).
   - In Problem 01, incoming transitions to `empty` exist from nonempty results (in-degree $\ge 1$).
   - The empty state can be repeatedly left and re-entered, embedded in cycles of length 2 and greater.
   - All results become mutually reachable, completely eliminating one-way reachability.

## 5. Artifact Index and Summary

1. **What this artifact supports:**
   - Supports the existence of a valid transition from a nonempty result to the empty state in 1 change.
   - Supports the 2-step cycle `empty` $\to$ `oneTermBare` $\to$ `empty`.
   - Supports the refutation of the candidate falsifier.
   - Supports the hypothesis that bare-term removal destroys one-way reachability of the empty state.
   - Supports the strong connectivity of the reachable state space under the declared 5 changes.

2. **What this artifact does not support:**
   - Does not support returning to the empty state without removing all assertions first (a state with positive assertions cannot delete an asserted term directly).
   - Does not support reaching `empty` from any state whose size is odd in an even number of steps (path parity matches $\text{size}(s) \pmod 2$).

3. **Narrowest defensible claim:**
   Under the seed change adding bare-term removal as a fifth kind of change, the empty beginning has positive in-degree, admits a 2-step cycle with the 1-term empty-assertion state, and is reachable from any well-formed state in $\text{size}(s)$ changes.

4. **Next test needed:**
   A candidate model testing whether deleting a term that names an assertion (simultaneously clearing its incident assertions) alters the minimum change distance between arbitrary states.
