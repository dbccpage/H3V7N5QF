# Claim Ledger: Problem 04 (Written Refusal)

Status vocabulary: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**.

| ID | Statement | Status | Evidence | Axioms | What would falsify it | Re-check |
|---|---|---|---|---|---|---|
| C04-1 | Seed edit: "Two results that differ only in how their terms are written are different results." | given | `meta/next_ten/04-written-refusal/seed_prompt.md` | — | A seed sentence stating that different writings are the same result | — |
| C04-2 | An obstructed change asserts some `xrx`, is refused, and changes nothing. | derived | `Derivation.lean` (`refusal_invariant`), `model.py` (`refused`, `refusal_result`) | std | A refused change altering the state representation | Verified: outcome is identical to starting state |
| C04-3 | Identifying `a` with `b` in what is given is refused and not performed. | derived | `Derivation.lean` (`identify_given_refused`) | std | Existence of a `Step` from `givenA` to `givenA.identify 0 1` | Inherited from Twentyfirst `identify_given_refused` |
| C04-4 | Adding a self-loop `xrx` to any legal state is always refused. | derived | `Derivation.lean` (`adding_self_loop_refused`) | std | A valid `Step` adding `(x, x)` | Derived from base `adding_xrx_always_obstructed` |
| C04-5 | Written refusal exploration reaches exactly 69 FREE states and 137 ANCHORED states within bound 3. | computed | `evidence/summary.json`, `test_derivation.py` | — | Exploration finding fewer or more states within bound | Certified by independent census formula $2^{n(n-1)}$ |
| C04-6 | The written refusal closure matches the Eighteenth closure wave-by-wave and state-by-state at every round. | computed | `evidence/summary.json` (`all_eighteenth_closures_match`), `test_derivation.py` | — | Any state present in one closure and absent in the other, or reached at a different round | Re-checked across all 4 configurations |
| C04-7 | Canonical renaming projects the written refusal closure onto the Twentyfirst quotient closure. | computed | `evidence/summary.json` (`all_twentyfirst_quotients_match`), `test_derivation.py` | — | A projected state not in Twentyfirst, or a Twentyfirst state unreached | Verified: 69 maps to 20; 137 maps to 109 |
| C04-8 | Written identity strictly refines the quotient: multiple written states share the same quotient class. | derived | `Derivation.lean` (`free_witness_distinct`, `anchored_witness_distinct`), `model.py` | std | All quotient fibers having size 1 | Witnessed constructively in Lean and Python |
| C04-9 | Orbit-Stabilizer theorem holds for all reached states: $n! = \|\text{Orb}(s)\| \cdot \|\text{Aut}(s)\|$. | computed | `model.py` (`orbit_splits_factorial`), `test_derivation.py` | — | Any reached state where the product does not equal $n!$ | Verified exhaustively on all 137 states |
| C04-10 | Hypothesis: Written sameness and refusal interact beyond a quotient of the same closure. | refuted | `resolution.md`, `evidence/summary.json`, `test_derivation.py` | — | A novel state reached under written refusal that is not in Eighteenth's closure | Falsifier confirmed at every round |
