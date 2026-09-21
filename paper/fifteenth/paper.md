# What follows once reaching a result does not make it admitted

Fifteenth derivation. Input: `prompt/fifteenth/seed_prompt.md`. Task:
`prompt/fifteenth/prompt.md`. Claim IDs refer to `paper/fifteenth/claim_ledger.md`;
an ID written `9:D4` refers to the ninth derivation's ledger
(`paper/ninth/claim_ledger.md`, paper `paper/ninth/paper.md`). Lean names in
the namespace `Seed.Fifteenth` are in `lean4/Fifteenth/`; names in `Seed.Ninth` are
the ninth's (`lean4/Ninth/`). The axiom report for every theorem cited here
is `evidence/fifteenth/lean_axioms.txt`. Computed files are in `evidence/fifteenth/`,
written by `python code/generate_fifteenth.py`.

Every notion below carries one source status: **given**, **chosen**,
**derived**, **computed**, **refuted**, **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the fifteenth seed, and the re-check says whether the result *survives
once a reached result is not thereby admitted*. The re-check is one of:
*(no change)* the statement mentions no admission; *(identity)* a fifteenth
state is a ninth state (`NDSt`) and a fifteenth change is a ninth change
(`Step15` as `Step9`); *(computed again)* the fifteenth exploration under
C-A1 is compared with the ninth's at the same bound.

The tenth leftover grading, the eleventh colliding writing, the twelfth
identification record, the thirteenth coarser writing and the fourteenth
leftover-as-writing are not in this seed.

## 0. Findings in brief

1. The fifteenth seed is the ninth (nothing given, two relations, four
   kinds, nothing forbidden) with one passage added: a result of the
   changes is reached; whether it is admitted is not given by the
   reaching; record for every result whether it is admitted; reaching a
   result does not make it admitted.
2. **Admission is independent of the two relations.** It is not an
   assertion of `r` or of `s` (G15, D3, `admission_not_assertion`). The
   record names no relation. Admission of a result asserting only in `r`
   is the same record as admission of a result asserting only in `s`
   (D5, `r_admission_is_s`).
3. **Every reached result can be admitted.** Reaching leaves not-admitted
   (D4, `reaching_does_not_admit`). Recording admission is not one of the
   four kinds (D6, `admission_not_a_kind`, `every_reached_can_be_admitted`).
   Nothing else is a change (G6).
4. **An admitted result does not constrain the other relation.** Admission
   is of the result, not of a projection (D5, D8, `no_cross_constraint`).
   Both `Step9.remove` exist on `twoBoth`.
5. **The ninth's cost, reachability, jointly free results and non-product
   count survive under C-A1** (D9–D11): the states and the changes are the
   ninth's. Under C-A2 they do not as a count of results: the one-term
   state asserting nothing is two tagged results, and the admitted copy
   costs 2 against size 1 (D12, `tagged_cost_fails`).
6. Admission is not a third relation (`no_third_rel`).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The sentences of the ninth seed, word for word (`diff`) |
| G15 | A result of the changes is reached. Whether it is admitted is not given by the reaching. Record for every result whether it is admitted. Reaching a result does not make it admitted. |

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, assertion `xry` or `xsy`, multiplicity, empty beginning, four kinds | given (ninth) | identity on `NDSt` / `Step9` |
| admission recorded of every result; not given by reaching | given (G15) | a record, not an assertion |
| admission recorded with the result, not in the state | chosen (C-A1) | the result remains a two-relation state |
| admission as a field of the result | chosen unchosen, kept (C-A2) | different results; computed |
| admission as an assertion of `r` or of `s` | refuted | G15: recorded of a result, not written `xry`/`xsy` |
| admission as a fifth kind of change | refuted | G6: nothing else is a change |
| admission as a third multiplicity | refuted as a reading | G15: admission is not an assertion |
| cost, reachability, results, count under C-A1 | derived (D9–D11) | the ninth's, through the identity |
| admission of `r` is admission of `s` as records of a result | derived (D5) | the record names no relation |

## 3. Readings that had to be chosen

**C-A1 (chosen).** Admission is recorded with the result as extra data. A
result is still a two-relation state up to sameness (9:C6). Reaching leaves
the record as not-admitted. Every reached result can be admitted by a
record that is not a change of the four kinds. The record names no
relation.

**C-A2 (unchosen, kept).** A result is a ninth state together with an
admission record; the beginning is not admitted. A change of the four kinds
lands on the unadmitted copy. Recording admission (not a change of the
seed) produces the admitted copy. Both computed.

C3, C5⁗, C6, C8′, C9 of the ninth paper, unchanged in kind. Bounds used here
(C8′): 3 terms with 6 rounds; 3 terms with 5; 2 terms with 8; full logs at 2
terms and 3 rounds; tagged reading at 2 terms with 5 rounds. Completeness of
the C-A1 results is the ninth's independent count at those bounds (D10).

## 4. What admission is

**D3.** Admission is not an assertion of `r` or of `s`. Lean
`admission_not_assertion`, `reaching_does_not_admit`, `admitted_is_admitted`.
The writings are `not-admitted` and `admitted`
(`given.json` `admitted_written_uses_neither_r_nor_s`).

**D4.** Reaching a result does not make it admitted. Lean
`reaching_does_not_admit`, `first_change_does_not_admit`,
`step_reaches_not_admitted`. Computed: `given.json`
`the_first_change_does_not_admit`; every performed change within the bound
leaves not-admitted (`admissions_*.csv`).

**D5.** Admission of a result asserting only in `r` is the same record as
admission of a result asserting only in `s`. Lean `r_admission_is_s`,
`r_admission_is_s_result`; both `Step9.remove` exist on `twoBoth`
(`twoBoth_remove_r`, `twoBoth_remove_s`). Computed: `given.json`
`r_and_s_same_admission`.

**D6.** Admitting is not one of the four kinds. Lean `admission_not_a_kind`,
`every_reached_can_be_admitted` (`StepTagged.record`, not a `Step9`). The
four kinds act on terms and on assertions; admission is neither. Nothing
else is a change (G6).

**D7.** Admission is not a third multiplicity beside `r` and `s`. Lean
`no_third_rel`, `admission_not_in_M`. The state is `NDSt`.

**D8.** An admitted result does not constrain the other relation.
`no_cross_constraint`; `admission_not_of_relation`. Admission is of the
result, not of a projection.

The admission statements about a result (is not admitted; is admitted; is
an assertion record; can be admitted) under C-A1: "is not admitted" and
"can be admitted" hold of every reached result; "is admitted" and "is an
assertion record" hold of none (`admission_verdicts`).

## 5. What of the ninth survives

**D9.** Under C-A1 the fewest changes to a result is its size. Lean
`fewest_changes15` (the ninth's `fewest_changes9`). Admission is not counted
among terms or assertions.

**D10.** The C-A1 results, rounds and shortest-sequence counts are the
ninth's at the same bound (`compare_with_ninth`; `ninth_ok` in every run).
Completeness is the ninth's independent count. The count is not a product
for `n ≥ 2` (9:D10, no change: admission is not in the count).

**D11.** Reachability is having a term, or the start is empty. Lean
`reach15_iff`. Jointly free results: `results_pair15`. The exchange keeps
the admission record (`admission_swap`, `admission_swap_admitted`,
`Step15.swap`).

## 6. The unchosen tag

**D12.** Under C-A2 a ninth state may be several results. The one-term state
asserting nothing is reached not-admitted in one change
(`tagged_one_nothing`) and admitted in two (`tagged_cost_fails`); those are
different results (`tagged_extra`). The tagged exploration at 2 terms and 5
rounds has 137 results against the ninth's 101 (`tagged.json`). The ninth's
"fewest changes is the size" fails for the admitted tag (2 against 1).

## 7. The task's questions

- **Is admission independent of the two relations?** Yes (D3, D5, D7): it
  is not an assertion of `r` or of `s`, it names no relation, and it is not
  a third multiplicity.
- **Can every reached result be admitted?** Yes (D4, D6): reaching leaves
  not-admitted; recording admission is available for every ninth state and
  is not a change of the four kinds.
- **Does an admitted result in one relation constrain the other?** No
  (D5, D8): admission is of the result, not of a projection.
- **Which of the ninth's cost, reachability, results and count survive?**
  All of them under C-A1 (D9–D11). Under C-A2 the result-set is strictly
  larger and the cost of a tagged state can exceed its size (D12).

## 8. What does not follow

Each item has two legal witnesses, or a proof of independence.

- Reaching a result admits it — fails: every reached result under C-A1
  (D4); there is no holding witness among C-A1 results.
- Admission of a result asserting only in `r` differs from admission of a
  result asserting only in `s` — fails: D5; holds: the two records
  not-admitted and admitted on one ninth state (C-A2).
- Every admission record is an assertion — fails: every reached result
  (D3); there is no holding witness among admission records (G15).
- The ninth's count of results is the tagged count — fails: C-A2 at 2 terms
  and 5 rounds; holds: C-A1, identity on states.

## 9. Open

- O1. Results beyond the declared bounds: the frontier of the ninth
  exploration is the C-A1 frontier; the ninth's two-term closed form (9:D11)
  gives every round with at most two terms.
- O2. A Lean function `Step9 s t → Admission` would eliminate `Prop` into
  `Type` and is not defined; admission is a record of the result
  (`reaching`, `admitted`), not a recursor on `Step9`. Recorded here rather
  than closed as a recursor on `Step9`.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Traces and logs of graph edits.** Recording, of each two-coloured
  multigraph reached by edits, whether that state is admitted, is a mark on
  the state, not a third colour. D3–D8 classify that mark: it is not an arc
  of either colour, it is not a fifth kind of edit, and it is independent
  of which colour is present. That is not a graph homomorphism and not the
  first seed's refusal of an obstructed change.
- **Edit distance from the empty two-coloured multigraph.** D9–D11 are the
  ninth's: the results up to writing are the ninth's, the distance from
  empty is vertices plus arcs of either colour, an admission record not
  counted. D12 is that taking the admission record as part of the result
  makes the count fail and the distance exceed the size.
- **Pólya enumeration of two-coloured multigraphs.** D10 is the ninth's
  count, admission not in the cycle index.

What appears to be specific to this seed: that reaching a result does not
make it admitted; that every reached result can be admitted by a record
that is not a change; that admission of one relation is admission of the
other as records of the same result; and that the ninth's collapses and
independence survive exactly so long as admission is kept off the identity
of the result.
