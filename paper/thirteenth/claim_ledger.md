# Claim ledger, thirteenth derivation

Status: **given**, **chosen**, **derived**, **computed**, **refuted**, **open**
(see `paper/thirteenth/paper.md`). Lean names in namespace `Seed.Thirteenth` are in
`lean4/Thirteenth/`; names in `Seed.Ninth` are the ninth's. Axiom report:
`evidence/thirteenth/lean_axioms.txt`; "std" means the theorem depends on
`propext`, `Classical.choice`, `Quot.sound` only (some on a subset). No
`sorry`, `admit`, or declared axiom occurs anywhere in `lean4/` (scanned by
`code/thirteenth/leanreport.py`).

The column **Re-check** says how a cited earlier result was re-checked from
the thirteenth seed and whether it *survives a coarser writing that forgets
which relation asserted*: *no change* (the statement mentions no coarser
writing), *identity* (`NDSt` / `Step9` as `Step13`), *computed again*
(thirteenth exploration against the ninth's), or "—" for a claim new to this
derivation.

## Given

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The ninth seed, word for word | given | `diff` of `prompt/thirteenth/seed_prompt.md` against `prompt/ninth/seed_prompt.md` | — | 9:G* no change | a sentence of the thirteenth seed that differs elsewhere |
| G18 | A coarser writing of an assertion forgets whether it was written with `r` or with `s`; every result is recorded also in that coarser writing; two results that differ only in which relation wrote their assertions may be the same coarser result | given | `prompt/thirteenth/seed_prompt.md` | — | — | a sentence making the coarser writing a third multiplicity or a fifth kind of change |

## Chosen

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| C-C1 | The coarser writing is the sum of the two multiplicities, recorded on the result; a result is a two-relation state | chosen | `code/thirteenth/coarse.py`; Lean `coarse` | — | — | a seed sentence putting the coarser writing in the result as its identity |
| C-C2 | Unchosen, kept: the result is the coarser writing | chosen (unchosen) | `code/thirteenth/explore.py` `explore_coarse`; Lean `coarse_extra` | — | — | — |
| C8′ | Bounds: 3 terms / 6 rounds; 3 / 5; 2 / 8; log 2 / 3; coarser 2 / 5 | chosen | `code/thirteenth/evidence.py` `Plan` | — | 9:C8′ lowered | — |

## Derived

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| D3 | The coarser writing determines the finer one iff nothing is asserted | derived + computed | Lean `determines_of_nothing`, `empty_determines`, `not_determines_twoBetween`; `given.json`; 4 of 518 results at 3 terms / 6 rounds | std | — | a state asserting something with a unique finer preimage; an empty-assertion state with two preimages |
| D4 | Adding in `r` and adding in `s` land on the same coarser writing; exchange keeps it | derived + computed | Lean `coarse_addAssertion_r_s`, `coarse_swap`; `given.json` `add_r_or_s_same_coarser` | std | — | an add-`r` / add-`s` pair with different coarser writings |
| D5 | Two finer results that differ only in which relation wrote the assertion may be the same coarser result; a collision on one pair does not constrain another | derived + computed | Lean `r_and_s_same_coarse`, `coarse_extra`, `no_cross_constraint`; `given.json` `r_and_s_same_coarser` | std | — | `0 r 1` and `0 s 1` having different coarser writings |
| D6 | The coarser writing is not a third multiplicity beside `r` and `s` | chosen (by construction) | the state is `NDSt`, with no field for the coarser writing; Lean `no_third_rel`, `coarse_not_assertion` are `rfl` on the projections and do not mention the coarser writing | std | identity on `NDSt` | a seed sentence making the coarser writing a multiplicity of a third relation |
| D8 | The size of the coarser writing equals the size of the finer state; having a term is preserved | derived + computed | Lean `size_coarse`, `coarse_cost_descends`, `coarse_has_term`; `given.json` `size_descends_between` | std | 9:D4 identity on size | a coarser writing whose size differs from its finer state's |
| D9 | Under C-C1 fewest changes is the size; the cost descends | derived + computed | Lean `fewest_changes13`; `summary_*.json` `ninth_derivation.same_results` | std | 9:D4 identity | a C-C1 result whose round is not its size |
| D10 | C-C1 results, rounds, sequences and count are the ninth's; count not a product for `n ≥ 2` | derived (identity) + computed | the C-C1 exploration wraps the ninth's, so `same_results`, rounds and sequences agree by construction; the one independent check is `explored_equals_independent_count` (the ninth's orbit count); 9:D10 for the non-product | — | 9:D5, 9:D10 identity / no change | an explored count different from the independent count |
| D11 | Reachability is having a term; jointly free results; exchange keeps the coarser writing | derived | Lean `reach13_iff`, `results_pair13`, `coarse_swap`, `Step13.swap`, `coarse_has_term` | std | 9:D8, 9:D5, 9:D16 identity | a pair the criterion admits with no sequence |
| D12 | Under C-C2 `0 r 1` and `0 s 1` are one result; 25 coarser results against 101 ninth results at 2 terms / 5 rounds; cost-as-size survives | derived + computed | Lean `coarse_extra`; `coarse.json` | std | 9:D4 survives as size; 9:D5, 9:D10 fail as a count | equal coarser and ninth counts at that bound; a coarser cost not equal to the size |

## Computed

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| K1 | `0 r 1` and `0 s 1` same coarser, different finer; empty determines; size descends; add-`r` / add-`s` same coarser | computed | `given.json` | — | — | those witnesses failing |
| K2 | Coarser statements about a result do not follow | computed | `coarse_verdicts`; `coarse_statements_holding_of_every_result` empty in the committed `summary_bound2_rounds8.json`. The exchange statement counts a result different from its exchange up to writing (`not same`), not merely differing `r`/`s` tuples (corrected at review) | — | 9:D14 for state statements, identity | a coarser statement true of every result within 2 terms and 8 rounds |
| K3 | C-C2 at 2 terms and 5 rounds has 25 results against the ninth's 101; seventh independent count agrees | computed | `coarse.json` | — | 9:K results computed again and quotiented | equal coarser and ninth counts at that bound |

## Open

| ID | Statement | Status | Evidence | Axioms | Re-check | What would falsify it |
|---|---|---|---|---|---|---|
| O1 | Results beyond the declared bounds | open as a listing | ninth frontier; 9:D11; seventh two-term form for C-C2 | — | 9:O2 | — |
| O2 | Number of finer preimages up to rewriting of terms | open in Lean | paper §9; Python `splits` in a fixed writing | — | — | a Lean enumeration of preimages up to rewriting |
