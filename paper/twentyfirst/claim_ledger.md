# Claim ledger

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**.
Lean names are in namespace `Seed.Twentyfirst` unless noted. Axiom report:
`evidence/twentyfirst/lean_axioms.txt`.

| ID | Statement | Status | Evidence | Axioms | What would falsify it | re-check |
|---|---|---|---|---|---|---|
| Z1 | The changed sentence, and the rest of the base seed | given | `prompt/twentyfirst/seed_prompt.md` | — | a sentence of the seed that says otherwise | — |
| Z2 | R1: refusal changes nothing (given by the seed); the base's other answers are compared and not performed | chosen | `code/twentyfirst/refusal.py`, `code/twentyfirst/evidence.py` | — | a refusal that changes the state | — |
| Z3 | Identifying `a` with `b` in what is given is not a performed step | derived | `identify_given_illegal`, `no_step_to_illegal`, `identify_given_refused` | std | a `Step` to that outcome | base `identify_legal_iff` on a related pair |
| Z4 | The start still has performed steps: add a term, remove `arb` | derived | `refusal_continues_by_a_term`, `refusal_continues_by_removal` | std | either step failing | survives: those changes were unobstructed in the base |
| Z5 | Inside 3 terms and 12 rounds an exploration that performs every change and refuses those writing some `xrx` reaches the base's results at the base's rounds, refusing as many changes as the base obstructs; no answer buys a result | computed | `evidence/twentyfirst/summary.json` (`outside_the_base`, `refusals`, `obstructed_attempts_in_the_base`, `answer_buys_a_result`) | — | a non-empty disagreement list, or other counts | base D10 and D12, re-checked by an independent census; the answer menu is not used to reach them |
| Z6 | The reachable set is smaller | refuted | Z5 | — | a base result inside the bound missing here | — |
| Z7 | Every alternative stops at its first obstruction | refuted | Z4 | std | the start having no performed step | — |
| Z8 | Adding a term is never obstructed, so there is no last result | derived | base `addTerm_legal` | std | an added term that asserts `xrx` | survives: the changed sentence is the answer menu |
| Z9 | No sequence that leaves the term bound and returns is shorter than the recorded round | derived | Z5 and base D12, D8: `fewest_changes_lower_A`, `fewest_changes_lower_B` | std | a shorter path that leaves and returns | survives: the base proves it for every sequence of unobstructed changes, and the changed sentence removes answers, not changes |
