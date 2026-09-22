# Claim ledger, twelfth derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/twelfth/paper.md`). Lean names in namespace `Seed.Twelfth` are in
`lean4/Twelfth/`; names in `Seed.Ninth` are the ninth's. Axiom report:
`evidence/twelfth/lean_axioms.txt`; "std" means the theorem depends on
`propext`, `Classical.choice`, `Quot.sound` only (some on a subset). No
`sorry`, `admit`, or declared axiom occurs anywhere in `lean4/` (scanned by
`code/twelfth/leanreport.py`).

The column **Re-check** says how a cited earlier result was re-checked from
the twelfth seed and whether it *survives a kept per-relation identification
record*: *no change* (the statement mentions no record), *identity* (`NDSt`
/ `Step9` as `Step12`), *computed again* (twelfth exploration against the
ninth's), or "—" for a claim new to this derivation.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The ninth seed, word for word | given | `diff` of `prompt/twelfth/seed_prompt.md` against `prompt/ninth/seed_prompt.md` | — | 9:G* no change | a sentence of the twelfth seed that differs elsewhere |
| G17 | Identifying two terms records, for each relation, which assertions of those two terms become one assertion; the record is kept with the result | given | `prompt/twelfth/seed_prompt.md` | — | — | a sentence making the record a third multiplicity or a fifth kind of change |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C-M1 | The record is computed from the start and the two terms, per relation; a result is a two-relation state; "kept with the result" is extra data on the identification | chosen | `code/twelfth/record.py`; Lean `recordRel` | — | — | a seed sentence putting the record in the result as a field |
| C-M2 | Unchosen, kept: the record tags the result | chosen (unchosen) | `code/twelfth/state.py` `Recorded`; Lean `Recorded` | — | — | — |
| C8′ | Bounds: 3 terms / 6 rounds; 3 / 5; 2 / 8; log 2 / 3; recorded 2 / 5 | chosen | `code/twelfth/evidence.py` `Plan` | — | 9:C8′ lowered | — |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D3 | The record of one relation is determined by that relation | chosen (C-M1, by construction) | `record_rel` reads only that relation, so this is definitional, not emergent; Lean `record_determined_by_rel` (stated for `r`, `simp [recordRel]`); `given.json` `r_determined_by_r` | std | — | a `record_rel` that reads the other relation |
| D4 | An empty isolated record is restored by adding a term; a between-assertion record is not restored by any one later change | derived + computed | Lean `empty_record_restored_by_addTerm`, `nonempty_not_restored`; `given.json` | std | — | a one-change restore of `0 r 1` after identifying those two terms |
| D5 | The two records can differ | derived + computed | Lean `r_record_not_s`, `no_cross_constraint`; `given.json` `r_record_not_s` | std | — | every identification has equal `r` and `s` records |
| D6 | The record is not a third multiplicity beside `r` and `s` | chosen (C-M1, by construction) | the state is `NDSt`, with no field for a record; Lean `no_third_rel`, `record_not_assertion` are `rfl` on the projections and do not mention a record | std | identity on `NDSt` | a seed sentence making the record a multiplicity |
| D8 | Identifying two terms drops a term | derived + computed | Lean `identify_drops_a_term`; `given.json` | std | identity on `Step9.identify` | an identification that keeps both terms |
| D9 | Under C-M1 fewest changes is the size | derived + computed | Lean `fewest_changes12`; `summary_*.json` `ninth_derivation.same_results` | std | 9:D4 identity | a C-M1 result whose round is not its size |
| D10 | C-M1 results, rounds, sequences and count are the ninth's; count not a product for `n ≥ 2` | derived (identity) + computed | the C-M1 exploration wraps the ninth's, so `same_results`, rounds and sequences agree by construction; the one independent check is `explored_equals_independent_count` (the ninth's orbit count); 9:D10 for the non-product | — | 9:D5, 9:D10 identity / no change | an explored count different from the independent count |
| D11 | Reachability is having a term; jointly free results; exchange carries records | derived | Lean `reach12_iff`, `results_pair12`, `recordRel_swap`, `recordOf_swap` (both now in the axiom report), `Step12.swap` | std | 9:D8, 9:D5, 9:D16 identity | a pair the criterion admits with no sequence |
| D12 | Under C-M2 the one-term empty state is several results (six within the bound); a recorded result's tagged cost can exceed the size | computed | `recorded.json` (six on `1::|`; empty-record one costs 3, size 1). Lean `recorded_extra` shows only that two differ (a Bool tag); `recorded_cost_is_size` is `rfl` (underlying size, not the BFS round) | std | 9:D4 fails on tagged cost, survives on the underlying size | one record per ninth state; a recorded cost below the size |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | An `r` record that is not the `s` record is inhabited; identifying drops a term; empty isolated restores | computed | `given.json` `r_record_not_s`, `identify_drops_a_term`, `two_term_empty_restored` | — | — | those witnesses failing |
| K2 | Record statements about an identification do not follow, except determination (which is chosen, D3) | computed | `record_verdicts`; `record_statements_holding_of_every_identification` is `['determined']` in the committed `summary_bound2_rounds8.json` | — | 9:D14 for state statements, identity | a record statement other than determination true of every identification within 2 terms and 8 rounds |
| K3 | C-M2 at 2 terms and 5 rounds has more results than the ninth; tagged one-term cost is 3 | computed | `recorded.json` | — | 9:K results computed again and exceeded | equal recorded and ninth counts at that bound |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| O1 | Results beyond the declared bounds | open as a listing | ninth frontier; 9:D11 | — | 9:O2 | — |
| O2 | Lean record of other-term groups vs the 2×2 block | open in Lean | paper §9; Python `record_rel` outgoing/incoming | — | — | a Lean identity of those two records |
