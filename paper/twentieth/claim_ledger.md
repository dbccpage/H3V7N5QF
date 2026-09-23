# Claim ledger

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**.
Lean names are in namespace `Seed.Twentieth` unless noted. Axiom report:
`evidence/twentieth/lean_axioms.txt`.

| ID | Statement | Status | Evidence | Axioms | What would falsify it | re-check |
|---|---|---|---|---|---|---|
| W1 | The changed sentence, and the rest of the base seed | given | `prompt/twentieth/seed_prompt.md` | — | a sentence of the seed that says otherwise | — |
| W2 | O1: a round is one performed change; the listing inside a round is either the base's or by the addition pair | chosen | `code/twentieth/order.py` | — | a round that performs two changes | — |
| W3 | O2: expand fewest additions first, and stop after the round-2 count of expansions | chosen + computed | `capped_by_round_2` in `evidence/twentieth/summary.json` | — | the capped sets equaling the round-2 sets | — |
| W4 | The two listings and the base agree on rounds and on the term-bound frontier | computed | `layer_mismatch`, `frontier_mismatch`, `differs_from_base` | — | a key in one of those lists | base D12 survives under O1 |
| W5 | Inside 3 terms and 12 rounds the closures are the base's: 109 and 20, with 700 and 112 frontier exits | computed | `evidence/twentieth/summary.json` | — | a regeneration with other counts | the base evidence at this bound |
| W6 | Fewer additions can be the later round | derived + computed | `reach_cleared`, `added_cleared`, `added_oneTerm`, `additions_diverge`; the witness table | std | the one-term state at an earlier round than the cleared state, or a greater added count | base `givenA_to_oneTerm` survives; the changed sentence is not used in its proof |
| W7 | The recorded additions are the round | refuted | W6 | std | a run in which every fewer-addition result is reached no later | — |
| W8 | O2 stopped early moves the frontier. At the plan's cap (12 or 11 expansions, against the 4 O1 spends): 0 leave and 17 enter, or 4 leave and 18 enter. At O1's own 4 expansions: 5 leave and 4 enter, or 5 leave and 3 enter | computed | `capped_by_round_2` (`matched_leave`, `matched_enter`, `o1_expansions_to_round_2`, `o1_at_that_cap_is_round_2`) | — | those counts changing | — |
| W9 | Adding a term is never obstructed, so there is no last result | derived | base `addTerm_legal` | std | an added term that asserts `xrx` | survives: the changed sentence is about order |
| W10 | O2 run until nothing is pending reaches O1's closure, either beginning, either sameness | computed | `o2_closure_differs` empty on all four runs | — | a key in that list | — |
| W11 | No sequence that leaves the term bound and returns is shorter than the recorded round | derived | W4 (`differs_from_base` empty) and base D12, D8: `fewest_changes_lower_A`, `fewest_changes_lower_B` | std | a shorter path that leaves and returns | survives: the base proves it for every sequence, and the changed sentence is about order |
