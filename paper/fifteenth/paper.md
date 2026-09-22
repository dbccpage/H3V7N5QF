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
2. **Admission is independent of the two relations** — by construction of
   the chosen reading C-A1. The record is `admitted`/`not-admitted`, which is
   not an assertion of `r` or of `s` and names no relation (D3). Admission of
   a result asserting only in `r` is the same record as admission of a result
   asserting only in `s` (D5), the record being relation-blind; the
   consistency check compares a result with its own `r/s` exchange.
3. **Every reached result can be admitted** — this is the chosen reading
   C-A1, not a derived fact: reaching leaves not-admitted (D4), and recording
   admission is a separate act, not one of the four kinds (D6). Nothing else
   is a change (G6).
4. **An admitted result does not constrain the other relation** (D5, D8) —
   again by construction: admission is of the result, not of a projection.
   Both `Step9.remove` exist on `twoBoth`.
5. **The ninth's cost, reachability, jointly free results and non-product
   count survive under C-A1** (D9–D11): the states and the changes are the
   ninth's. Under C-A2 they do not as a count of results: the one-term
   state asserting nothing is two tagged results, and the admitted copy costs
   2 against size 1 (D12: a route of 2 in Lean, `tagged_cost_fails`, an upper
   bound; that 2 is the fewest is computed).
6. Admission is not a third relation — by construction (the state is `NDSt`).

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

**D3.** Admission is not an assertion of `r` or of `s`, by construction: the
record is `not-admitted`/`admitted`, containing neither `r` nor `s`. The Lean
`admission_not_assertion` is a case split on the two constructors and does not
by itself say the record is not an assertion; `reaching_does_not_admit` is
`reaching = .notAdmitted` (definitional). Computed: `given.json`
`admitted_written_uses_neither_r_nor_s`.

**D4.** Reaching a result does not make it admitted — the chosen reading
C-A1: `admission_of_reaching` is not-admitted for every result. The Lean
`reaching_does_not_admit`, `first_change_does_not_admit`,
`step_reaches_not_admitted` are all `reaching = .notAdmitted`, definitional.
Computed: `given.json` `the_first_change_does_not_admit`; every performed
change within the bound leaves not-admitted (`admissions_*.csv`).

**D5.** Admission of a result asserting only in `r` is the same record as
admission of a result asserting only in `s` — by construction, the record
naming no relation. The Lean `r_admission_is_s` is `reaching = reaching`
(definitional). The witnesses `twoBoth_remove_r`, `twoBoth_remove_s` show
both removals are legal. Computed: `given.json` `r_and_s_same_admission`, and
the consistency check in `code/fifteenth/invariants.py` compares the record
of each result with the record of its `r/s` exchange (`swap`), which a
relation-dependent record would break.

**D6.** Admitting is not one of the four kinds (`admission_not_a_kind`, i.e.
`reaching = .notAdmitted`, definitional). That **every reached result can be
admitted** is the chosen reading C-A1, not a derived fact: the Lean
`every_reached_can_be_admitted` is the `StepTagged.record` constructor of the
unchosen reading C-A2, exhibiting the admitted copy, not proving reachedness
implies admissibility. The four kinds act on terms and on assertions;
admission is neither. Nothing else is a change (G6).

**D7.** Admission is not a third multiplicity beside `r` and `s`, by
construction: the state is `NDSt`, with no admission field. Lean
`no_third_rel`, `admission_not_in_M` are `rfl` on the projections and do not
mention admission.

**D8.** An admitted result does not constrain the other relation — by
construction (admission is of the result, not of a projection). Lean
`no_cross_constraint` is `rfl` with two `Step9.remove` facts on `twoBoth`,
and `admission_not_of_relation` is `reaching = .notAdmitted`; neither
mentions a constraint.

The admission statements about a result (is not admitted; is admitted; is
an assertion record; can be admitted) under C-A1: "is not admitted" and
"can be admitted" hold of every reached result; "is admitted" and "is an
assertion record" hold of none (`admission_verdicts`). All four are settled
by the chosen reading, not emergent.

## 5. What of the ninth survives

**D9.** Under C-A1 the fewest changes to a result is its size. Lean
`fewest_changes15` (the ninth's `fewest_changes9`). Admission is not counted
among terms or assertions.

**D10.** The C-A1 results, rounds and shortest-sequence counts are the
ninth's at the same bound. This is an identity, not a second computation:
the C-A1 exploration is the ninth's (`fifteenth.explore.explore` wraps
`ninth.explore.explore`), so the result, round and sequence comparisons in
`compare_with_ninth` agree by construction and show only determinism. The one
independent check is the count: every run's explored results equal the
ninth's orbit count (`explored_equals_independent_count`). The count is not a
product for `n ≥ 2` (9:D10, no change: admission is not in the count).

**D11.** Reachability is having a term, or the start is empty. Lean
`reach15_iff`. Jointly free results: `results_pair15`. That the exchange keeps
the admission record is definitional (`admission_swap`,
`admission_swap_admitted` are `reaching = reaching` / `admitted = admitted`),
since the record names no relation; the change itself is carried by
`Step15.swap`.

## 6. The unchosen tag

**D12.** Under C-A2 a ninth state may be several results. The one-term state
asserting nothing is reached not-admitted in one change
(`tagged_one_nothing`) and admitted in two; those are different results
(`tagged_extra`). The Lean `tagged_cost_fails` exhibits a route of 2 to the
admitted copy, an upper bound; that 2 is the fewest is computed. The tagged
exploration at 2 terms and 5 rounds has 137 results against the ninth's 101
(`tagged.json`). The ninth's "fewest changes is the size" fails for the
admitted tag (2 against 1, computed).

## 7. The task's questions

- **Is admission independent of the two relations?** Yes, by construction of
  C-A1 (D3, D5, D7): the record is not an assertion of `r` or of `s`, names
  no relation, and is not a third multiplicity.
- **Can every reached result be admitted?** Yes — this is the chosen reading
  C-A1 (D4, D6), not a derived fact: reaching leaves not-admitted, and
  recording admission is a separate act available for every ninth state, not
  a change of the four kinds.
- **Does an admitted result in one relation constrain the other?** No
  (D5, D8): admission is of the result, not of a projection.
- **Which of the ninth's cost, reachability, results and count survive?**
  All of them under C-A1 (D9–D11). Under C-A2 the result-set is strictly
  larger and the cost of a tagged state can exceed its size (D12).

## 8. What does not follow

Each item has two legal witnesses, or a proof of independence.

- Reaching a result admits it — refuted by the chosen reading C-A1 (D4):
  reaching leaves not-admitted, so there is no witness where it holds. This
  is a chosen reading, not a statement with two witnesses.
- Admission of a result asserting only in `r` differs from admission of a
  result asserting only in `s` — refuted by D5 (the record names no
  relation), so the two agree by construction and there is no witness where
  they differ. (The two records not-admitted and admitted on one ninth state
  under C-A2 witness a *different* statement — that a state has two admission
  copies — not this one.)
- Every admission record is an assertion — refuted (D3): the record is
  `admitted`/`not-admitted`, never an assertion, so there is no witness
  where it holds.
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
