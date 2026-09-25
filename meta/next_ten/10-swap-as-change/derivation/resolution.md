# Resolution: Problem 10 (swap-as-change)

Parent: `prompt/ninth/seed_prompt.md`  
Target: `meta/next_ten/10-swap-as-change/seed_prompt.md`  
Proposal candidate: C17 (`why.md`, `plan.md`)

## 1. Candidate Hypothesis and Falsifier

- **Hypothesis**: "Making the existing involution a step changes shortest paths and sequence counts."
- **Falsifier**: "All shortest paths and rounds equal the ninth's."

## 2. Definitional Scope

The seed introduces the fifth kind of change:
"Exchanging the relations replaces every `xry` with `xsy` and every `xsy` with `xry`, preserving each multiplicity."

Two distinct reachability settings arise:
1. **Root-relative setting (from the empty beginning `empty9`)**:
   Shortest paths and BFS exploration rounds starting from `empty9`.
2. **State-to-state setting (general transition graph)**:
   Shortest paths and path counts between arbitrary pairs of states `(S, T)`.

## 3. Investigation and Findings

### A. Root-Relative Setting: Falsifier Holds

In BFS exploration from `empty9` across terms bound `n ≤ 2` and 4 rounds:
- **Rounds**: Every result `T` is first reached in round `size(T) = n + m`, identical to Ninth (`depth_10 == depth_9`).
- **New results per round**: Exactly identical to Ninth (`[1, 1, 3, 9, 22]`).
- **Shortest path cost**: Every result `T` has shortest cost `n + m`, identical to Ninth.
- **Shortest sequence counts**: Exactly identical to Ninth (`count_shortest_sequences_10 == count_shortest_sequences_9`).
- **Mechanism**: Every change of Ninth alters `size` by `±1`. The swap change alters `size` by `0`. Because `empty9` has `size 0`, any path from `empty9` to a target `T` of `size(T)` requires at least `size(T)` additions. A path containing at least one swap would require at least `size(T) + 1` steps. Hence, no shortest path from `empty9` contains a swap.

Thus, **from the empty beginning, the falsifier holds strictly**: all shortest path costs and rounds from `empty9` equal Ninth's.

### B. State-to-State Setting: Hypothesis Supported

In the full transition graph among explored canonical states (32 states with `n ≤ 2`, `m ≤ 2`):
- **Shortest path reductions**: Among the 1024 state pairs, 220 pairs have strictly shorter paths with swap than in Ninth (`cost_10 < cost_9`).
- **Involution shortcut**: For any asymmetric state `S` (`S.r ≠ S.s`), `dist_10(S, swap(S)) = 1`. In Ninth, any sequence between `S` and `swap(S)` has even length at least 2 (`dist_9(S, swap(S)) ≥ 2`).
- **Maximum cost reduction observed**: A cost reduction of 3 steps occurs between states with 2 assertions in `r` and their swapped counterparts (`dist_9 = 4`, `dist_10 = 1`).
- **Closed-form reduction formula**:
  For all states `S, T`, the exact relation holds:
  $$\text{dist}_{10}(S, T) = \min(\text{dist}_9(S, T), 1 + \text{dist}_9(\text{swap}(S), T))$$
  This formula was checked across all pairs in `reduction_formula_verification.json`.
- **At most one swap**: Because Ninth changes commute with swap, any shortest path in Problem 10 uses at most one swap.

Thus, **in the general transition graph, the hypothesis is supported**: making the involution a step strictly changes shortest paths and sequence counts between states.

## 4. Summary Table

| Metric | Ninth Derivation | Problem 10 (with swap) | Outcome |
|---|---|---|---|
| BFS rounds from empty (`n ≤ 2, m ≤ 2`) | 4 rounds, 32 states | 4 rounds, 32 states | Falsifier holds (identical) |
| Shortest cost from `empty9` to `T` | `size(T)` | `size(T)` | Falsifier holds (identical) |
| Shortest sequences from `empty9` | Additions only | Additions only (no swaps) | Falsifier holds (identical) |
| Total attempts during BFS (`bound=2, r=4`) | 79 attempts | 87 attempts (+8 swaps) | Tenth performs more attempts |
| Cost between `0r0` and `0s0` | 2 changes | 1 change (swap) | Hypothesis supported (reduced) |
| Cost between `0r0+0r0` and `0s0+0s0` | 4 changes | 1 change (swap) | Hypothesis supported (reduced) |
| Pairs with cost reduction (`n ≤ 2, m ≤ 2`) | 0 | 220 / 1024 pairs | Hypothesis supported |

## 5. Artifact Audit Summary

1. **What this artifact supports**:
   - Supports that root-relative rounds and shortest paths from `empty9` collapse to Ninth.
   - Supports that state-to-state reachability contains genuine shortcut edges, reducing distance by up to `2k - 1` for `k` asymmetric assertions.
   - Supports the closed-form reduction formula $\text{dist}_{10}(S, T) = \min(\text{dist}_9(S, T), 1 + \text{dist}_9(\text{swap}(S), T))$.
2. **What it does not support**:
   - Does not support that swap creates new reachable states (the set of reachable states is identical to Ninth).
   - Does not support that any state is reached sooner from `empty9`.
3. **Narrowest defensible claim**:
   Exchanging the relations as a step introduces length-1 shortcut edges between asymmetric dual states, strictly reducing shortest path distances between asymmetric state pairs while preserving all root-relative shortest path lengths and exploration rounds from `empty9`.
4. **Next test needed**:
   Evaluate whether graph diameter of the reachable quotient at higher term bounds exhibits an asymptotic bound reduction under relation exchange.
