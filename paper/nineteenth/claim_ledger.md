# Claim ledger

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**.
Lean names are in namespace `Seed.Nineteenth`. Axiom report:
`evidence/nineteenth/lean_axioms.txt`. "std" means `propext`,
`Classical.choice`, and `Quot.sound` only.

| ID | Statement | Status | Evidence | Axioms | What would falsify it | re-check |
|---|---|---|---|---|---|---|
| N1 | The changed sentence, and the rest of the base seed | given | `prompt/nineteenth/seed_prompt.md` | — | a sentence of the seed that says otherwise | — |
| N2 | P1: one pair that mentions at least one of the two terms; the terms stay; an unchanged pair is not a change; a loop is refused | chosen | `code/nineteenth/changes.py` | — | a partial identification that erases a term | — |
| N3 | P2, only a pair naming both terms, is kept and reaches the same results while performing none | chosen + computed | `evidence/nineteenth/summary.json` (`cooccur_performed` 0, equal closures) | — | a result of one reading that the other misses | — |
| N4 | Rewriting one pair leaves the terms | derived | `performPartial_terms` | std | a partial identification whose term set differs | the base `identify` does not survive |
| N5 | A pair naming both terms becomes a loop | derived | `cooccur_is_loop` | std | a survivor that leaves the two endpoints distinct | — |
| N6 | A one-sided rewrite can be legal, and it is not the base identification | derived | `side_partial_eq`, `side_partial_legal`, `side_not_identify` | std | the three-term witness equaling `side.identify` | base identification rewrites every assertion |
| N7 | The base identification of what is given has fewer terms | derived | `identify_smaller` | std | equal term counts | base `identify` |
| N8 | No sequence of these changes reaches the one-term state | derived | `PStep.card_ge`, `PReach.card_ge`, `oneTerm_unreachable` | std | a sequence whose term count falls | base `givenA_to_oneTerm` does not survive |
| N9 | Inside 3 terms and 12 rounds the counts are those in the paper | computed | `evidence/nineteenth/summary.json` | — | a regeneration with other counts | base closure 109 / 20, of which 68 / 19 remain |
| N10 | On a legal state a partial identification is obstructed exactly when the pair names both terms, and removing that pair is already reached | computed | `obstruction_not_between`, `removal_answer_outside` | — | a disagreement in either list | base D10, re-checked inside the bound: the removal is an ordinary change |
| N11 | Global identification is recovered by iterating partial ones | refuted | N8, N9 | std | a run whose least term count is 1 | — |
| N12 | Adding a term is never obstructed, so there is no last result | derived | base `addTerm_legal`; the frontier counts in N9 | std | an added term that asserts `xrx` | survives: the changed sentence is not about adding a term |
| O1 | A closed form for 68 and 19 | open | the rounds in N9 | — | a proved formula | — |
| N13 | No sequence that adds a fourth term returns inside the bound, so the closure inside 3 terms is every result with at most 3 terms | derived | `PStep.card_ge`, `PReach.card_ge` (over a superset of the seed's changes) | std | a change of this seed that lowers the number of terms | differs from the base, where an identification lowers it |
