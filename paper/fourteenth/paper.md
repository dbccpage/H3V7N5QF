# What follows once leftover is a writing that is not an assertion

Fourteenth derivation. Input: `prompt/fourteenth/seed_prompt.md`. Task:
`prompt/fourteenth/prompt.md`. Claim IDs refer to `paper/fourteenth/claim_ledger.md`;
an ID written `9:D4` refers to the ninth derivation's ledger
(`paper/ninth/claim_ledger.md`, paper `paper/ninth/paper.md`). Lean names in
the namespace `Seed.Fourteenth` are in `lean4/Fourteenth/`; names in `Seed.Ninth` are
the ninth's (`lean4/Ninth/`). The axiom report for every theorem cited here
is `evidence/fourteenth/lean_axioms.txt`. Computed files are in `evidence/fourteenth/`,
written by `python code/generate_fourteenth.py`.

Every notion below carries one source status: **given**, **chosen**,
**derived**, **computed**, **refuted**, **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the fourteenth seed, and the re-check says whether the result *survives
once leftover is a writing that is not an assertion*. The re-check is one of:
*(no change)* the statement mentions no leftover; *(identity)* a fourteenth
state is a ninth state (`NDSt`) and a fourteenth change is a ninth change
(`Step14` as `Step9`); *(computed again)* the fourteenth exploration under
C-F1 is compared with the ninth's at the same bound.

The tenth seed, if run, grades leftovers as three outcomes of the four kinds
of change. That grading is not in this seed.

## 0. Findings in brief

1. The fourteenth seed is the ninth (nothing given, two relations, four
   kinds, nothing forbidden) with one passage added: after every change,
   record what that change leaves. A leftover is written neither `xry` nor
   `xsy`. A leftover is not an assertion and is not an answer.
2. **Leftover cannot be identified with an assertion of `r` or of `s`.** It
   is written neither `xry` nor `xsy` and is not an assertion (G15, D3,
   `leftover_not_assertion`). A leftover of a removal is the pair written
   `xℓy` with a third letter `ℓ`.
3. **Clearing leftover is not one of the four kinds.** Leftover is not a
   term and not an assertion; leftover is not an answer; nothing else is a
   change (D6, `clearing_not_a_kind`, `leftover_remove_ne_nothing`). Adding
   the corresponding `xry` after a removal restores the *state* (a ninth
   fact about terms and multiplicities) and leaves leftover-as-writing
   untouched: leftover of that later addition is nothing (`leftoverAdd`).
4. **Leftover of one relation is leftover of the other, as writings.** A
   removal of `(x, y)` in `r` and a removal of `(x, y)` in `s` have the same
   leftover writing `xℓy` — by construction, since the writing names no
   relation (D5). Both changes exist on a state that asserts the pair in each
   relation (`twoBoth_remove_r`, `twoBoth_remove_s`, now in the axiom report).
5. **The ninth's cost, reachability, jointly free results and non-product
   count survive under C-F1** (D9–D11): the states and the changes are the
   ninth's. Under C-F2 they do not as a count of results: the one-term state
   asserting nothing is three tagged results — tagged nothing at cost 1, and a
   pair tag `0ℓ0` and a merge tag `∼0`, both at cost 3 against size 1 (D12).
   A route of 3 to the pair tag is shown in Lean (`tagged_cost_fails`, an
   upper bound); that 3 is the fewest is computed.
6. Leftover is not a third relation (`no_third_rel`). The tenth's
   three-outcome grading is a different seed.

## 1. What the seed gives

| ID | Given |
|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The sentences of the ninth seed, word for word (`diff`) |
| G15 | After every change, record what that change leaves. A leftover is written neither `xry` nor `xsy`. A leftover is not an assertion and is not an answer. |

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, assertion `xry` or `xsy`, multiplicity, empty beginning, four kinds | given (ninth) | identity on `NDSt` / `Step9` |
| leftover writing neither `xry` nor `xsy`; not an assertion; not an answer | given (G15) | a third kind of writing |
| leftover recorded on the change, not in the result | chosen (C-F1) | the result remains a two-relation state |
| leftover as a field of the result | chosen unchosen, kept (C-F2) | different results; computed |
| leftover as an assertion of `r` or of `s` | refuted | G15: written neither `xry` nor `xsy`; not an assertion |
| leftover as an answer | refuted | G15: leftover is not an answer |
| leftover as a third multiplicity | refuted as a reading | G15: leftover is not an assertion |
| cost, reachability, results, count under C-F1 | derived (D9–D11) | the ninth's, through the identity |
| leftover of `r` is leftover of `s` as writings of the same pair | derived (D5) | the writing names no relation |

## 3. Readings that had to be chosen

**C-F1 (chosen).** Leftover is recorded on the change. A result is still a
two-relation state up to sameness (9:C6). An addition leaves nothing; a
removal of `(x, y)` in either relation leaves the pair written `xℓy`; an
identification of `u` and `v` leaves those two terms written `u∼v`. The
letter `ℓ` is neither `r` nor `s`.

**C-F2 (unchosen, kept).** A result is a ninth state together with the leftover
writing of the incoming change, counted up to writing: the state and the
writing's terms are renumbered *together* (`canonical_tagged`), so the tag
names the result's own terms. A removal's tag keeps its pair; an
identification's tag keeps only the surviving term (`∼u`), the other term
being gone from the result — naming it would name an absent term. An earlier
version canonicalized the state but not the tag, which merged and split
tagged results wrongly and named absent terms; that was corrected at review
(change log), moving the 2-term 5-round count from 130 to 131. Both computed.

C3, C5⁗, C6, C8′, C9 of the ninth paper, unchanged in kind. Bounds used here
(C8′): 3 terms with 6 rounds; 3 terms with 5; 2 terms with 8; full logs at 2
terms and 3 rounds; tagged reading at 2 terms with 5 rounds. Completeness of
the C-F1 results is the ninth's independent count at those bounds (D10).

## 4. What leftover is

**D3.** Leftover is not an assertion of `r` or of `s`. Lean
`leftover_not_assertion`, `leftover_addTerm`, `leftover_remove`,
`leftover_identify`. The leftover writing of a removal is `xℓy`
(`given.json` `pair_written_uses_neither_r_nor_s`).

**D4.** Leftover is not an answer, by construction: `is_answer()` returns
false for every leftover writing. The Lean `leftover_not_answer` is
`L = .nothing ∨ L ≠ .nothing`, a tautology, and does not establish it; the
content is that this seed has no answer field.

**D5.** Leftover of a removal in `r` of a pair is leftover of a removal in
`s` of that pair — by construction, since `leftover_pair` names no relation.
The Lean `leftover_remove_r_s` is `leftoverRemove x y = leftoverRemove x y`
(definitional). The witnesses `twoBoth_remove_r`, `twoBoth_remove_s` (now in
the axiom report) show both removals are legal changes on a state asserting
the pair in each relation. Computed: `given.json` `r_and_s_same_leftover`,
where the two removals are both legal (the state asserts `0 r 1` and `0 s 1`);
the cross-relation check in `code/fourteenth/invariants.py` compares the two
legal removals' writings on every such state (a consistency check — they
agree by construction).

**D6.** Clearing leftover is not one of the four kinds. Leftover of a
removal is not nothing (`leftover_remove_ne_nothing`); leftover of an
addition is nothing (`clearing_not_a_kind`). The four kinds act on terms
and on assertions; leftover is neither. Nothing else is a change (G6).

**D7.** Leftover is not a third multiplicity beside `r` and `s`. This is the
chosen reading C-F1, by construction: the state is `NDSt`, with no field for
leftover. Lean `no_third_rel`, `leftover_not_in_M` are `rfl` about the
projections and do not mention leftover; they are not cited as a proof of D7.

**D8.** An identification leaves a merge writing, not an assertion.
`leftover_identify`; `given.json` `two_term_between_identify_leftover`.

The leftover statements about a change (leaves nothing; leaves a pair;
leaves a merge; is an assertion writing) each fail of some change within 2
terms and 4 rounds (`leftover_verdicts`); "is an assertion writing" holds of
none.

## 5. What of the ninth survives

**D9.** Under C-F1 the fewest changes to a result is its size. Lean
`fewest_changes14` (the ninth's `fewest_changes9`). Leftover is not counted
among terms or assertions.

**D10.** The C-F1 results, rounds and shortest-sequence counts are the
ninth's at the same bound. This is an identity, not a second computation:
the C-F1 exploration is the ninth's (`fourteenth.explore.explore` wraps
`ninth.explore.explore`), so the result, round and sequence comparisons in
`compare_with_ninth` agree by construction and show only determinism. The one
independent check is the count: every run's explored results equal the
ninth's orbit count (`explored_equals_independent_count`). The count is not a
product for `n ≥ 2` (9:D10, no change: leftover is not in the count).

**D11.** Reachability is having a term, or the start is empty. Lean
`reach14_iff`. Jointly free results: `results_pair14`. That the exchange
carries the leftover of an addition and of a removal is definitional
(`leftover_swap_addTerm` is `leftoverAdd = leftoverAdd`; `leftover_swap_remove`
that the pair is unmoved), since neither writing names a relation; the change
itself is carried by `Step14.swap`.

## 6. The unchosen tag

**D12.** Under C-F2 a ninth state may be several results. The one-term state
asserting nothing is three results: tagged nothing in one change
(`tagged_one_nothing`), tagged with the pair `0ℓ0`, and tagged with the merge
`∼0`, the last two in three changes; those are different results
(`tagged_extra`). The Lean `tagged_cost_fails` exhibits a route of 3 to the
pair tag, an upper bound; that 3 is the fewest is computed. The tagged
exploration at 2 terms and 5 rounds has 131 results against the ninth's 101
(`tagged.json`). The ninth's "fewest changes is the size" fails for the pair
and merge tags (3 against 1, computed).

## 7. The task's questions

- **Can leftover be identified with an assertion of `r` or of `s`?** No
  (D3): leftover is written neither `xry` nor `xsy` and is not an
  assertion.
- **Is clearing leftover one of the four kinds?** No (D6): leftover is not
  a term and not an assertion; leftover is not an answer; nothing else is a
  change. Restoring a removed multiplicity is a change of the four kinds
  that restores the *state*, not leftover-as-writing.
- **Is leftover of one relation leftover of the other?** As writings, yes
  (D5): leftover of a removal names no relation. As a third relation, no
  (D7).
- **Which of the ninth's cost, reachability, results and count survive?**
  All of them under C-F1 (D9–D11). Under C-F2 the result-set is strictly
  larger and the cost of a tagged state can exceed its size (D12).

## 8. What does not follow

Each item has two legal witnesses, or a proof of independence.

- Leftover is always nothing — fails: a removal (`0ℓ0`); holds: the first
  change (adding a term).
- Leftover of a removal in `r` differs from leftover of a removal in `s` of
  the same pair — refuted by D5: the writing names no relation, so the two
  are equal by construction; there is no witness where they differ.
- Every leftover writing is an assertion — fails: every performed change
  (D3); there is no holding witness among leftovers (G15).
- The ninth's count of results is the tagged count — fails: C-F2 at 2 terms
  and 5 rounds; holds: C-F1, identity on states.

## 9. Open

- O1. Results beyond the declared bounds: the frontier of the ninth
  exploration is the C-F1 frontier; the ninth's two-term closed form (9:D11)
  gives every round with at most two terms.
- O2. A Lean function `Step9 s t → LeftWriting` would eliminate `Prop` into
  `Type` and is not defined; leftover is a function of the constructor's
  data (`leftoverRemove` takes the pair, not the relation). Recorded here
  rather than closed as a recursor on `Step9`.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Traces and logs of graph edits.** Recording, after each edit of a
  two-coloured multigraph, a writing that is not itself an arc, is a log of
  the edit, not a third colour. D3–D7 classify that log: it is not an arc
  of either colour, it is not an answer to an obstruction, and a deletion
  of a pair forgets which colour was deleted. That is not a graph
  homomorphism and not the tenth seed's three-way grading of edits.
- **Edit distance from the empty two-coloured multigraph.** D9–D11 are the
  ninth's: the results up to writing are the ninth's, the distance from
  empty is vertices plus arcs of either colour, a leftover writing not
  counted. D12 is that taking the leftover writing as part of the result
  makes the count fail and the distance exceed the size.
- **Pólya enumeration of two-coloured multigraphs.** D10 is the ninth's
  count, leftover not in the cycle index.

What appears to be specific to this seed: that leftover is a third kind of
writing, not an assertion and not an answer; that leftover of one relation
is leftover of the other as writings of the same pair; that clearing
leftover is not one of the four kinds; and that the ninth's collapses and
independence survive exactly so long as leftover is kept off the identity
of the result.
