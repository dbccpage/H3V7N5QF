# Resolution of Hypothesis and Falsifier: Problem 04 (Written Refusal)

## 1. Problem Identity and Status

- **Problem ID**: Rank 4 / C07 (`04-written-refusal`)
- **Parent Derivation**: `twentyfirst` (`code/twentyfirst/`, `lean4/Twentyfirst/`, `paper/twentyfirst/`)
- **Reference Derivations**: `eighteenth` (`code/eighteenth/`, `lean4/Eighteenth/`, `paper/eighteenth/`), `H3V7N5QF` (base)
- **Target Hypothesis**: "Written sameness and refusal interact beyond a quotient of the same closure."
- **Declared Falsifier**: "The written refusal closure is exactly the eighteenth's closure at every round."
- **Final Verdict**: **HYPOTHESIS FALSIFIED. FALSIFIER CONFIRMED.**

---

## 2. Executive Summary

Under the seed change:
> "Two results that differ only in how their terms are written are different results."

replacing the twenty-first seed's:
> "Two results that differ only in how their terms are written are the same result."

the derivation investigates whether literal term representations interact non-trivially with refusal semantics.

We establish in this formal model and verify exhaustively that **written sameness and refusal do not interact beyond a fiber-wise quotient of the same closure**:
1. At every exploration round $r \in \{0, 1, \dots, 12\}$ and under all four configurations ($\text{bra} \in \{\text{False}, \text{True}\} \times \text{sameness} \in \{\text{ANCHORED}, \text{FREE}\}$), the set of newly discovered written states under refusal semantics is **identical** to the set discovered by Eighteenth's exploration (`explore_written`).
2. There are 0 disagreements in reached states, 0 mismatches in round depths, and exact matching of all wave counts and frontier exit counts.
3. The canonical projection $\pi: \text{State} \to \text{State}/\!\sim$ maps the 69 FREE written states to the 20 quotient states of Twentyfirst, and the 137 ANCHORED written states to the 109 quotient states of Twentyfirst.

---

## 3. Mathematical Proof of Equivalence

Let $\mathcal{S}$ denote the set of legal states on at most $B = 3$ terms.
In Problem 04:
1. An obstructed change $c$ attempted on state $s$ produces an outcome asserting some self-loop $xrx$, which violates legality.
2. The seed stipulates: *"An obstructed change is refused. A refused change is recorded and changes nothing."*
3. Thus, for any obstructed change $c$, $\text{eval}(s, c) = s$.
4. In BFS exploration, state $s$ is already present in the reached set $\mathcal{D}_{\le r}$ at round $r$ (or earlier). Therefore, $\text{eval}(s, c)$ never introduces a novel state:
   $$\mathcal{D}_{r+1} \setminus \mathcal{D}_{\le r} = \{ \text{perform}(s, c) \mid s \in \mathcal{W}_r, c \in \text{changes}(s), \text{perform}(s, c) \text{ is unobstructed and } n \le B \} \setminus \mathcal{D}_{\le r}.$$
5. In Eighteenth, an obstructed change was required to be answered (by removing the obstruction or building structure). However, as established in the Eighteenth derivation, removal either restores the current state or returns to a prior state, and structure-building introduces additions that are already reachable along unobstructed paths. Consequently, Eighteenth's forward BFS exploration (`explore_written`) expanded exclusively across unobstructed changes.
6. Because both BFS procedures start at the identical given state and expand along identical unobstructed transitions without canonical quotienting, their wave sequences and reachable sets coincide identically at every round:
   $$\mathcal{W}_r^{(\text{P04})} = \mathcal{W}_r^{(\text{P18})} \quad \forall r \ge 0.$$

---

## 4. Empirical Verification Matrix

Exhaustive execution at bound $B = 3$, rounds $R = 12$:

| Alternative | Sameness | P04 Written Results | P18 Written Results | Match? | P04 Wave Sequence (`new_per_round`) | Total Refusals | Frontier Exits | Quotient Classes (P21) |
|---|---|---|---|---|---|---|---|---|
| `bra = False` | ANCHORED | 137 | 137 | **Exact** | `[1, 3, 8, 16, 23, 22, 21, 21, 15, 6, 1, 0, 0]` | 695 | 128 | 109 |
| `bra = False` | FREE | 69 | 69 | **Exact** | `[1, 3, 8, 15, 20, 15, 6, 1, 0, 0, 0, 0, 0]` | 348 | 64 | 20 |
| `bra = True` | ANCHORED | 137 | 137 | **Exact** | `[1, 3, 8, 16, 23, 22, 21, 21, 15, 6, 1, 0, 0]` | 695 | 128 | 109 |
| `bra = True` | FREE | 69 | 69 | **Exact** | `[1, 3, 8, 15, 20, 15, 6, 1, 0, 0, 0, 0, 0]` | 348 | 64 | 20 |

- Disagreements between P04 and P18 depth dictionaries: **0**
- Round-level mismatches: **0**
- Independence census check: **Passed** (1 + 4 + 64 = 69 for FREE; 1 + 8 + 128 = 137 for ANCHORED).
- Orbit-stabilizer theorem verification ($n! = |\text{Orb}(s)| \cdot |\text{Aut}(s)|$): **100% Passed across all states**.

---

## 5. Quotient and Fiber Structure

Under canonical quotient projection $\pi$:
- For FREE sameness: the 69 written states project onto 20 isomorphism classes.
  - 15 classes exhibit fiber splitting ($|\pi^{-1}(c)| > 1$).
  - Maximum fiber size is $3! = 6$, occurring for completely asymmetric digraphs on 3 vertices.
- For ANCHORED sameness: the 137 written states project onto 109 classes.
  - 28 classes exhibit fiber splitting ($|\pi^{-1}(c)| = 2$), corresponding to transposition of un-named terms.

This shows in this model that literal written identity strictly refines the quotient without perturbing the dynamics of refusal or generating new topological pathways.
