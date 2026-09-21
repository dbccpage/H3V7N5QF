# What follows once every change records a leftover

Tenth derivation. Input: `prompt/tenth/seed_prompt.md`. Task:
`prompt/tenth/prompt.md`. Claim IDs refer to `paper/tenth/claim_ledger.md`;
an ID written `9:D4` refers to the ninth derivation's ledger
(`paper/ninth/claim_ledger.md`, paper `paper/ninth/paper.md`). Lean names in
the namespace `Seed.Tenth` are in `lean4/Tenth/`; names in `Seed.Ninth` are
the ninth's (`lean4/Ninth/`). The axiom report for every theorem cited here
is `evidence/tenth/lean_axioms.txt`. Computed files are in `evidence/tenth/`,
written by `python code/generate_tenth.py`.

Every notion below carries one source status: **given**, **chosen**,
**derived**, **computed**, **refuted**, **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the tenth seed, and the re-check says whether the result *survives once
every change carries a leftover outcome*. The re-check is one of: *(no
change)* the statement mentions no leftover; *(identity)* a tenth state is a
ninth state (`NDSt`) and a tenth change is a ninth change (`Step10` as
`Step9`); *(computed again)* the tenth exploration under C-L1 is compared
with the ninth's at the same bound.

## 0. Findings in brief

1. The tenth seed is the ninth (nothing given, two relations, four kinds,
   nothing forbidden) with one passage added: after every change, record what
   that change leaves. A leftover is not an assertion. Three outcomes:
   nothing left; a leftover that a later change of the four kinds can clear;
   a leftover that none of them can.
2. **Leftover is not a third relation.** Under the chosen reading C-L1 it is
   recorded on the change, not as a multiplicity beside `r` and `s` (D6,
   `no_third_rel`). The unchosen reading C-L2 that tags a result with leftover
   is kept: that tag is a third *record* of the result, not a third relation
   (D12, `tagged_extra`).
3. **The three outcomes split the ninth's changes.** Additions leave nothing
   (D3, `leftover_addTerm`, `leftover_addAssertion`). A removal leaves a
   leftover cleared by adding that same assertion (D4, `clears_remove`) and
   not by a change of the other relation (D5, `other_rel_not_clear`). An
   identification leaves a leftover that a later change can clear when some
   one change restores the start (two terms asserting nothing: D7,
   `leftover_identify_twoEmpty`) and a leftover that none of them can
   otherwise (two terms with an assertion between them: D8, computed). All
   three outcomes are inhabited (`given.json`).
4. **A leftover of one relation does not constrain the other.** A removal in
   `r` is not restored by adding an assertion of `s` (D5). An identification
   leftover is not of one relation (identification acts on both). Under C-L1
   later changes of either relation remain the ninth's list.
5. **The ninth's cost, reachability, jointly free results and non-product
   count survive under C-L1** (D9–D11): the states and the changes are the
   ninth's. Under C-L2 they do not: the one-term state asserting nothing is
   two tagged results, and the clearable tag costs 3 against size 1 (D12,
   `tagged_cost_fails`).
6. The first seed's obstruction is not restored: every change is performed;
   leftover is three-way and is not a bar.

## 1. What the seed gives

| ID | Given |
|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The sentences of the ninth seed, word for word (`diff`) |
| G15 | After every change, record what that change leaves. A leftover is not an assertion. Nothing left, a leftover that a later change of the four kinds can clear, and a leftover that none of them can, are three outcomes. Declare which, for every change. |

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, assertion `xry` or `xsy`, multiplicity, empty beginning, four kinds | given (ninth) | identity on `NDSt` / `Step9` |
| leftover; the three outcomes | given (G15) | not an assertion |
| leftover recorded on the change, not in the result | chosen (C-L1) | the result remains a two-relation state |
| leftover as a tag on the result | chosen unchosen, kept (C-L2) | different results; computed |
| leftover as a third multiplicity | refuted as a reading | G15: a leftover is not an assertion |
| "a later change can clear" | chosen (C-L1) | some one change of the four kinds restores the start, up to writing |
| cost, reachability, results, count under C-L1 | derived (D9–D11) | the ninth's, through the identity |
| the three outcomes inhabited | computed (K1) | `given.json` |

## 3. Readings that had to be chosen

**C-L1 (chosen).** Leftover is recorded on the change. A result is still a
two-relation state up to sameness (9:C6). An addition leaves nothing; a
removal leaves a leftover cleared by adding that assertion; an identification
leaves a leftover that is clearable iff some one later change restores the
start up to writing.

**C-L2 (unchosen, kept).** A result is a ninth state together with the leftover
of the incoming change; the beginning is tagged nothing left. Both computed.

C3, C5⁗, C6, C8′, C9 of the ninth paper, unchanged in kind. Bounds used here
(C8′): 3 terms with 6 rounds; 3 terms with 5; 2 terms with 8; full logs at 2
terms and 3 rounds; tagged reading at 2 terms with 4 rounds. Completeness of
the C-L1 results is the ninth's independent count at those bounds (D10).

## 4. What leftover is

**D3.** An addition leaves nothing. Lean `leftover_addTerm`,
`leftover_addAssertion`; the added thing is a term or an assertion.

**D4.** A removal leaves a leftover that adding that assertion clears. Lean
`leftover_remove`, `clears_remove`, `remove_add_of_pos`.

**D5.** A change of the other relation does not restore a removal: the
removed multiplicity stays lowered. Lean `other_rel_not_clear`. So a leftover
of one relation does not constrain the other relation's later changes.

**D6.** Leftover is not a third multiplicity beside `r` and `s`. Lean
`no_third_rel`, `leftover_not_assertion`. The state is `NDSt`.

**D7.** Identifying two terms in a state that asserts nothing is restored by
adding a term (the same result up to writing). Lean
`identify_twoEmpty_restored`, `leftover_identify_twoEmpty`.

**D8.** Identifying two terms that had an assertion between them is not
restored by any one later change of the four kinds (computed:
`given.json` `two_term_between_identify_leftover`; not in Lean, O1). That
inhabits the third outcome.

The three leftover statements about a change (leaves nothing; leaves a
clearable leftover; leaves an uncleared leftover) each hold of some change
and fail of some change within 2 terms and 4 rounds (`leftover_verdicts`).

## 5. What of the ninth survives

**D9.** Under C-L1 the fewest changes to a result is its size. Lean
`fewest_changes10` (the ninth's `fewest_changes9`). Leftover is not counted
among terms or assertions.

**D10.** The C-L1 results, rounds and shortest-sequence counts are the
ninth's at the same bound (`compare_with_ninth`; `ninth_ok` in every run).
Completeness is the ninth's independent count. The count is not a product
for `n ≥ 2` (9:D10, no change: leftover is not in the count).

**D11.** Reachability is having a term, or the start is empty. Lean
`reach10_iff`. Jointly free results: `results_pair10`. The exchange carries
leftover of an addition and of a removal (`leftover_swap_addTerm`,
`leftover_swap_remove`); the identification case is 9:D16 through
`Step9.swap` and is not re-closed as a single leftover identity (O2).

## 6. The unchosen tag

**D12.** Under C-L2 a ninth state may be several results. The one-term state
asserting nothing is reached tagged nothing left in one change
(`tagged_one_nothing`) and tagged clearable in three (`tagged_cost_fails`);
those are different results (`tagged_extra`). The tagged exploration at 2
terms and 4 rounds has more results than the ninth's (42 against 36 in the
SMALL evidence; `tagged.json`). The ninth's "fewest changes is the size"
fails for the clearable tag (3 against 1).

## 7. The task's questions

- **Is leftover a third kind of record beside the two relations?** Under
  C-L1, no: it is a classification of changes. Under C-L2, yes as a tag on
  the result, and no as a third relation (it is not a multiplicity on pairs).
- **Do the three outcomes split the ninth's changes?** Yes: additions /
  removals / identifications (the last split further by restorability).
- **Does a leftover of one relation constrain the other?** No for a removal
  (D5). An identification leftover is joint, not of one relation.
- **Which of the ninth's cost, reachability, results and count survive?**
  All four under C-L1. None of cost-as-size, the result-set, or the count
  as the ninth's, under C-L2.

## 8. What does not follow

Each item has two legal witnesses, or a proof of independence.

- Every change leaves nothing — fails: a removal; holds: the first term.
- Every change leaves a leftover none can clear — fails: an addition; holds:
  identifying two terms with an assertion between them.
- Leftover is a third relation — refuted as a reading of G15; the unchosen
  tag is not a relation.
- The ninth's cost is the size of a tagged result — fails: one-term
  clearable, 3 against 1; holds: one-term nothing left, 1 against 1.

## 9. Open

- O1. Lean statement of D8 (identification with an assertion between the
  terms is uncleared): proved in the paper from the four kinds and checked
  by computation. The dependent elimination on `Step9` against that pair of
  states did not close on the first attempt.
- O2. `leftoverOf s.swap t.swap = leftoverOf s t` in full generality: the
  addition and removal cases are in Lean; the identification case is
  `Step9.swap` plus restorability, recorded here rather than closed as one
  identity.
- O3. Results beyond the declared bounds: the frontier of the ninth
  exploration is the C-L1 frontier; the ninth's two-term closed form (9:D11)
  gives every round with at most two terms.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Graph edits with a residue that is not an arc.** D3–D8 classify each
  edit as leaving nothing (an insertion is the new vertex or arc), a residue
  that the inverse insertion clears (a deletion), or a residue that no one
  edit of the four kinds restores (a contraction that mixed arcs). That is
  not the first seed's binary obstruction (a forbidden loop), which the sixth
  dropped and this seed does not restore.
- **Edit distance from the empty two-coloured multigraph.** D9 is the ninth's
  D4: the distance is vertices plus arcs of either colour, leftover not
  counted. D12 is that tagging each arrival with the residue of the last edit
  makes that distance fail (the one-vertex graph, residue of a contraction of
  two empty vertices, costs three edits).
- **Pólya enumeration of two-coloured multigraphs.** D10 is the ninth's
  count, leftover not in the cycle index. The tagged reading's extra results
  are not that enumeration.

What appears to be specific to this seed: that recording a leftover after
every change, with leftover not an assertion, classifies the ninth's four
kinds without adding a third relation and without restoring a forbidden pair;
that the three outcomes are all inhabited, the third only when an
identification mixed an assertion; that a leftover of one relation does not
constrain the other; and that the ninth's collapses and independence survive
exactly so long as leftover is kept off the result.
