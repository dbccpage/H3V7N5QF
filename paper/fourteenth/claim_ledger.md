# Claim ledger, fourteenth derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/fourteenth/paper.md`). Lean names in namespace `Seed.Fourteenth` are in
`lean4/Fourteenth/`; names in `Seed.Ninth` are the ninth's. Axiom report:
`evidence/fourteenth/lean_axioms.txt`; "std" means the theorem depends on
`propext`, `Classical.choice`, `Quot.sound` only (some on a subset). No
`sorry`, `admit`, or declared axiom occurs anywhere in `lean4/` (scanned by
`code/fourteenth/leanreport.py`).

The column **Re-check** says how a cited earlier result was re-checked from
the fourteenth seed and whether it *survives leftover as a writing that is
not an assertion*: *no change* (the statement mentions no leftover),
*identity* (`NDSt` / `Step9` as `Step14`), *computed again* (fourteenth
exploration against the ninth's), or "—" for a claim new to this derivation.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The ninth seed, word for word | given | `diff` of `prompt/fourteenth/seed_prompt.md` against `prompt/ninth/seed_prompt.md` | — | 9:G* no change | a sentence of the fourteenth seed that differs elsewhere |
| G15 | After every change, record what that change leaves; a leftover is written neither `xry` nor `xsy`; leftover is not an assertion and is not an answer | given | `prompt/fourteenth/seed_prompt.md` | — | — | a sentence making leftover an assertion, an answer, or written `xry`/`xsy` |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C-F1 | Leftover is recorded on the change; a result is a two-relation state; additions leave nothing; a removal leaves the pair written `xℓy`; an identification leaves `u∼v` | chosen | `code/fourteenth/leftover.py`; Lean `leftoverRemove`, `leftoverAdd`, `leftoverIdentify` | — | — | a seed sentence putting leftover in the result |
| C-F2 | Unchosen, kept: leftover writing tags the result | chosen (unchosen) | `code/fourteenth/state.py` `Tagged`; Lean `Tagged` | — | — | — |
| C8′ | Bounds: 3 terms / 6 rounds; 3 / 5; 2 / 8; log 2 / 3; tagged 2 / 5 | chosen | `code/fourteenth/evidence.py` `Plan` | — | 9:C8′ lowered | — |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D3 | Leftover is not an assertion of `r` or of `s` | derived + computed | Lean `leftover_not_assertion`, `leftover_addTerm`, `leftover_remove`, `leftover_identify`; `given.json` `r_leftover_is_assertion` false | none / std | — | a leftover writing equal to some `xry` or `xsy` |
| D4 | Leftover is not an answer | derived + computed | Lean `leftover_not_answer`; `given.json` `first_leftover_is_answer` false | std | 1:answers no change (dropped from the sixth) | leftover being refuse, remove-the-obstruction, or build |
| D5 | Leftover of a removal in `r` of a pair is leftover of a removal in `s` of that pair | derived + computed | Lean `leftover_remove_r_s`, `r_leftover_is_s`, `twoBoth_remove_r`, `twoBoth_remove_s`; `given.json` `r_and_s_same_leftover` | std | — | leftover writings of those two removals that differ |
| D6 | Clearing leftover is not one of the four kinds | derived | Lean `clearing_not_a_kind`, `leftover_remove_ne_nothing`; G6 nothing else is a change | none | — | a fifth kind, or leftover being a term or an assertion |
| D7 | Leftover is not a third multiplicity beside `r` and `s` | derived | Lean `no_third_rel`, `leftover_not_in_M` | std | identity on `NDSt` | a seed sentence making leftover a multiplicity |
| D8 | An identification leaves a merge writing, not an assertion | derived + computed | Lean `leftover_identify`; `given.json` `two_term_between_identify_leftover` | none | — | leftover of an identification written `xry` or `xsy` |
| D9 | Under C-F1 fewest changes is the size | derived + computed | Lean `fewest_changes14`; `summary_*.json` `ninth_derivation.same_results` | std | 9:D4 identity | a C-F1 result whose round is not its size |
| D10 | C-F1 results, rounds, sequences and count are the ninth's; count not a product for `n ≥ 2` | derived (paper) + computed | `compare_with_ninth`; `ninth_ok` in every run; 9:D10 for the non-product | — | 9:D5, 9:D10 computed again / no change | a C-F1 result the ninth lacks, or the reverse |
| D11 | Reachability is having a term; jointly free results; exchange carries leftover of additions and removals | derived | Lean `reach14_iff`, `results_pair14`, `leftover_swap_addTerm`, `leftover_swap_remove`, `Step14.swap` | std | 9:D8, 9:D5, 9:D16 identity | a pair the criterion admits with no sequence |
| D12 | Under C-F2 the one-term state is two results; the pair tag costs 3 against size 1 | derived + computed | Lean `tagged_one_nothing`, `tagged_cost_fails`, `tagged_extra`; `tagged.json` 130 against 101 | std | 9:D4 does not survive on tagged results | a unique leftover writing per ninth state; a tagged cost equal to size on the pair-tagged one-term state |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | Leftover of `r` and of `s` agree on a pair; leftover is not an assertion and not an answer | computed | `given.json` | — | — | `r_and_s_same_leftover` false |
| K2 | Leftover statements about a change do not follow | computed | `leftover_verdicts`; `leftover_statements_holding_of_every_change` does not contain `leaves_nothing` at 4 or more rounds | — | 9:D14 for state statements, identity | a leftover statement true of every performed change within 2 terms and 4 rounds except "is an assertion writing" which holds of none |
| K3 | C-F2 at 2 terms and 5 rounds has 130 results against the ninth's 101 | computed | `tagged.json` | — | 9:K results computed again and exceeded | equal tagged and ninth counts at that bound |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| O1 | Results beyond the declared bounds | open | ninth frontier; 9:D11 two-term closed form | — | 9:O bounds | a complete run of 100 rounds within minutes |
| O2 | A Lean function `Step9 s t → LeftWriting` | open in Lean | paper §9; Python `leftover_of`; Lean `leftoverRemove` takes the pair, not a `Step9` | — | — | a definition eliminating `Step9` into `LeftWriting` without `Prop`→`Type` |
