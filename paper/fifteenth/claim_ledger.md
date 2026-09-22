# Claim ledger, fifteenth derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/fifteenth/paper.md`). Lean names in namespace `Seed.Fifteenth` are in
`lean4/Fifteenth/`; names in `Seed.Ninth` are the ninth's. Axiom report:
`evidence/fifteenth/lean_axioms.txt`; "std" means the theorem depends on
`propext`, `Classical.choice`, `Quot.sound` only (some on a subset). No
`sorry`, `admit`, or declared axiom occurs anywhere in `lean4/` (scanned by
`code/fifteenth/leanreport.py`).

The column **Re-check** says how a cited earlier result was re-checked from
the fifteenth seed and whether it *survives a reached result not thereby
admitted*: *no change* (the statement mentions no admission),
*identity* (`NDSt` / `Step9` as `Step15`), *computed again* (fifteenth
exploration against the ninth's), or "—" for a claim new to this derivation.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The ninth seed, word for word | given | `diff` of `prompt/fifteenth/seed_prompt.md` against `prompt/ninth/seed_prompt.md` | — | 9:G* no change | a sentence of the fifteenth seed that differs elsewhere |
| G15 | A result of the changes is reached; whether it is admitted is not given by the reaching; record for every result whether it is admitted; reaching a result does not make it admitted | given | `prompt/fifteenth/seed_prompt.md` | — | — | a sentence making reaching admit, or making admission an assertion or a fifth kind |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C-A1 | Admission is recorded with the result; a result is a two-relation state; reaching leaves not-admitted; every reached result can be admitted by a record that is not a change | chosen | `code/fifteenth/admission.py`; Lean `reaching`, `admitted`, `every_reached_can_be_admitted` | — | — | a seed sentence putting admission in the result as its identity |
| C-A2 | Unchosen, kept: admission record tags the result | chosen (unchosen) | `code/fifteenth/state.py` `Tagged`; Lean `Tagged` | — | — | — |
| C8′ | Bounds: 3 terms / 6 rounds; 3 / 5; 2 / 8; log 2 / 3; tagged 2 / 5 | chosen | `code/fifteenth/evidence.py` `Plan` | — | 9:C8′ lowered | — |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D3 | Admission is not an assertion of `r` or of `s` | chosen (by construction: the record is `admitted`/`not-admitted`) + computed | Lean `admission_not_assertion` is a case split on the two constructors; `reaching_does_not_admit` is `reaching = .notAdmitted`; `given.json` `first_admission_is_assertion` false | none | — | a record written `xry` or `xsy` |
| D4 | Reaching a result does not make it admitted | chosen (C-A1: `admission_of_reaching` is constant not-admitted) + computed | Lean `reaching_does_not_admit`, `first_change_does_not_admit`, `step_reaches_not_admitted` are all `reaching = .notAdmitted` (definitional); `given.json` `the_first_change_does_not_admit` | none | — | a performed change recorded admitted under C-A1 |
| D5 | Admission of a result asserting only in `r` is admission of a result asserting only in `s` | chosen (by construction: the record names no relation) + computed | Lean `r_admission_is_s` is `reaching = reaching` (definitional); `twoBoth_remove_r`, `twoBoth_remove_s` show both removals legal; `given.json` `r_and_s_same_admission`; the check compares each result's record with its `r/s` swap's | std | — | a record that reads the relation |
| D6 | Admitting is not one of the four kinds (by construction); every reached result can be admitted (chosen, C-A1) | chosen | Lean `admission_not_a_kind` is `reaching = .notAdmitted` (definitional); `every_reached_can_be_admitted` is the C-A2 `StepTagged.record` constructor, exhibiting the admitted copy, not proving reached ⇒ admissible; G6 nothing else is a change | none / std | — | a seed sentence making admission a fifth kind |
| D7 | Admission is not a third multiplicity beside `r` and `s` | chosen (C-A1, by construction) | the state is `NDSt`, with no admission field; Lean `no_third_rel`, `admission_not_in_M` are `rfl` on the projections and do not mention admission | std | identity on `NDSt` | a seed sentence making admission a multiplicity |
| D8 | An admitted result does not constrain the other relation | chosen (by construction: admission is of the result, not a projection) | Lean `no_cross_constraint` is `rfl` with two `Step9.remove` facts on `twoBoth`; `admission_not_of_relation` is `reaching = .notAdmitted`; neither states a constraint | std | — | a record that reads a projection |
| D9 | Under C-A1 fewest changes is the size | derived + computed | Lean `fewest_changes15`; `summary_*.json` `ninth_derivation.same_results` | std | 9:D4 identity | a C-A1 result whose round is not its size |
| D10 | C-A1 results, rounds, sequences and count are the ninth's; count not a product for `n ≥ 2` | derived (identity) + computed | the C-A1 exploration wraps the ninth's, so `same_results`, rounds and sequences agree by construction; the one independent check is `explored_equals_independent_count` (the ninth's orbit count); 9:D10 for the non-product | — | 9:D5, 9:D10 identity / no change | an explored count different from the independent count |
| D11 | Reachability is having a term; jointly free results; exchange keeps the admission record | derived (reach/results) + definitional (the exchange) | Lean `reach15_iff`, `results_pair15`; that the exchange keeps the record is definitional (`admission_swap`, `admission_swap_admitted` are `reaching = reaching` / `admitted = admitted`), the record naming no relation; the change is carried by `Step15.swap` | std | 9:D8, 9:D5, 9:D16 identity | a pair the criterion admits with no sequence |
| D12 | Under C-A2 the one-term state is two results; the admitted tag costs 2 against size 1 | derived (two results; a route) + computed (2 is the fewest) | Lean `tagged_one_nothing`, `tagged_extra` (two results); `tagged_cost_fails` exhibits a route of 2 (an upper bound, not the minimum); `tagged.json` 137 against 101, admitted one-term cost 2 (the fewest) | std | 9:D4 does not survive on tagged results | a route to the admitted copy shorter than 2; a unique admission record per ninth state |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | Admission of `r` and of `s` agree; admission is not an assertion and not a kind; reaching does not admit | computed | `given.json` | — | — | `r_and_s_same_admission` false |
| K2 | Under C-A1, "is not admitted" and "can be admitted" hold of every result; "is admitted" holds of none | computed | `admission_verdicts`; `admission_statements_holding_of_every_result` | — | 9:D14 for state statements, identity | a C-A1 result that is admitted |
| K3 | C-A2 at 2 terms and 5 rounds has 137 results against the ninth's 101 | computed | `tagged.json` | — | 9:K results computed again and exceeded | equal tagged and ninth counts at that bound |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| O1 | Results beyond the declared bounds | open | ninth frontier; 9:D11 two-term closed form | — | 9:O bounds | a complete run of 100 rounds within minutes |
| O2 | A Lean function `Step9 s t → Admission` | open in Lean | paper §9; Python `admission_of_reaching`; Lean `reaching` is of the result, not a `Step9` | — | — | a definition eliminating `Step9` into `Admission` without `Prop`→`Type` |
