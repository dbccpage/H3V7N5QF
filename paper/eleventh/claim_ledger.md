# Claim ledger, eleventh derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/eleventh/paper.md`). Lean names in namespace `Seed.Eleventh` are in
`lean4/Eleventh/`; names in `Seed.Ninth` are the ninth's. Axiom report:
`evidence/eleventh/lean_axioms.txt`; "std" means the theorem depends on
`propext`, `Classical.choice`, `Quot.sound` only (some on a subset). No
`sorry`, `admit`, or declared axiom occurs anywhere in `lean4/` (scanned by
`code/eleventh/leanreport.py`).

The column **Re-check** says how a cited earlier result was re-checked from
the eleventh seed and whether it *survives a writing that can collide terms
it does not identify*: *no change* (the statement mentions no writing),
*identity* (`NDSt` / `Step9` as `Step11`), *computed again* (eleventh
exploration against the ninth's), or "—" for a claim new to this derivation.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The ninth seed, word for word | given | `diff` of `prompt/eleventh/seed_prompt.md` against `prompt/ninth/seed_prompt.md` | — | 9:G* no change | a sentence of the eleventh seed that differs elsewhere |
| G16 | A writing of terms may give two terms the same letter while they remain two; assertions are read from the writing; if two terms are written the same and their assertions differ, the writing does not determine the assertions | given | `prompt/eleventh/seed_prompt.md` | — | — | a sentence making writing a change or an identification |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C-W1 | A writing is a reading of a result's terms; a result is a two-relation state; determination is constant multiplicity on every letter-pair rectangle (chosen so the assertions are recoverable from the writing — the weaker term-by-term reading is recorded and eliminated in the paper §3); coarser means further collision | chosen | `code/eleventh/writing.py`; Lean `determines`, `coarser` | — | — | a seed sentence putting the writing in the result |
| C-W2 | Unchosen, kept: the writing tags the result, counted up to renaming letters and up to the state's automorphisms (`writing_orbits`; cross-checked by Burnside, `labeled_equals_orbit_count`); at two terms this equals the per-writing count | chosen (unchosen) | `code/eleventh/state.py` `Labeled`, `code/eleventh/writing.py` `writing_orbits`; Lean `Labeled` | — | — | two writings of one orbit counted as two results |
| C8′ | Bounds: 3 terms / 6 rounds; 3 / 5; 2 / 8; log 2 / 3; labeled 2 / 4 | chosen | `code/eleventh/evidence.py` `Plan` | — | 9:C8′ lowered | — |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D3 | An injective writing determines the assertions | derived + computed | Lean `inj_determines`, `apart_determines_twoBetween`; `given.json` | std | — | an injective writing whose rectangles are not constant |
| D4 | A collision forbids every coarser writing from determining | derived + computed | Lean `coarser_of_not_determines`; `given.json` `collision_forbids_coarser` | std | — | a coarser writing of a collision that determines |
| D5 | A collision of one relation need not be a collision of the other | derived + computed | Lean `r_collision_not_s`, `no_cross_constraint`; `given.json` `r_collision_not_s` | std | — | every `r`-collision is an `s`-collision |
| D6 | A writing is not a third multiplicity beside `r` and `s` | chosen (C-W1, by construction) | the state is `NDSt`, with no field for a writing; Lean `no_third_rel`, `writing_not_assertion` are definitional (`rfl` on the projections) and do not mention a writing | std | identity on `NDSt` | a seed sentence making writing a multiplicity |
| D8 | Identifying two terms drops a term; a writing is not a state change, so writing them the same leaves both | derived + computed | Lean `identify_drops_a_term` (a card fact); `collide_keeps_terms` records only `twoTerms9.T.card = 2` (the writing absent from state and statement); `writing_not_identify`; `given.json` | std | identity on `Step9.identify` | a colliding writing that drops a term |
| D9 | Under C-W1 fewest changes is the size | derived + computed | Lean `fewest_changes11`; `summary_*.json` `ninth_derivation.same_results` | std | 9:D4 identity | a C-W1 result whose round is not its size |
| D10 | C-W1 results, rounds, sequences and count are the ninth's; count not a product for `n ≥ 2` | derived (identity) + computed | the C-W1 exploration wraps the ninth's, so `same_results`, rounds and sequences agree by construction; the one independent check is `explored_equals_independent_count` (the ninth's orbit count); 9:D10 for the non-product | — | 9:D5, 9:D10 identity / no change | an explored count different from the independent count |
| D11 | Reachability is having a term; jointly free results; exchange carries writings | derived | Lean `reach11_iff`, `results_pair11`, `determines_swap`, `Step11.swap` | std | 9:D8, 9:D5, 9:D16 identity | a pair the criterion admits with no sequence |
| D12 | Under C-W2 the two-term empty state is two results (two writing orbits); the cost is still the size | computed (two results; cost) + illustrated in Lean | `labeled_of` gives two results; `labeled.json`. Lean `labeled_extra` only shows two `Labeled` records with different letter functions differ (not up to renaming); `labeled_cost_is_size` is `rfl` (definition unfold) | std | 9:D4 survives on labeled cost, not on the count | one orbit counted as two results; a labeled cost unequal to size |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | An `r`-collision that is not an `s`-collision is inhabited; identifying drops a term | computed | `given.json` `r_collision_not_s`, `identify_drops_a_term` | — | — | those witnesses failing |
| K2 | Writing statements about a (state, writing) pair do not follow | computed | `writing_verdicts`; `writing_statements_holding_of_every_writing` empty in the committed 2-term 8-round run (`summary_bound2_rounds8.json`) | — | 9:D14 for state statements, identity | a writing statement true of every writing of every result within 2 terms and 8 rounds |
| K3 | C-W2 at 2 terms and 4 rounds has more results than the ninth | computed | `labeled.json` | — | 9:K results computed again and exceeded | equal labeled and ninth counts at that bound |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| O1 | Results beyond the declared bounds | open as a listing | ninth frontier; 9:D11 | — | 9:O2 | — |
| O2 | Reading a determining colliding writing is not the identification of the collided terms | open in Lean | paper §9; Python `read_from` vs `perform` identify | — | — | a Lean identity of those two operations |

## Refuted as readings

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| R1 | Writing is identifying | refuted | G16 "remain two terms"; D8 | — | — | a seed sentence making writing a change of the four kinds |
| R2 | Writing is a third multiplicity | refuted | G16 a writing of terms; D6 | — | — | a seed sentence making writing an assertion |
