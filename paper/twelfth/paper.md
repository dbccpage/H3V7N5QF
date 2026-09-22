# What follows once identifying keeps a per-relation record

Twelfth derivation. Input: `prompt/twelfth/seed_prompt.md`. Task:
`prompt/twelfth/prompt.md`. Claim IDs refer to `paper/twelfth/claim_ledger.md`;
an ID written `9:D4` refers to the ninth derivation's ledger
(`paper/ninth/claim_ledger.md`, paper `paper/ninth/paper.md`). Lean names in
the namespace `Seed.Twelfth` are in `lean4/Twelfth/`; names in `Seed.Ninth`
are the ninth's (`lean4/Ninth/`). The axiom report for every theorem cited here
is `evidence/twelfth/lean_axioms.txt`. Computed files are in `evidence/twelfth/`,
written by `python code/generate_twelfth.py`.

Every notion below carries one source status: **given**, **chosen**,
**derived**, **computed**, **refuted**, **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the twelfth seed, and the re-check says whether the result *survives
once an identification keeps a per-relation record*. The re-check is one
of: *(no change)* the statement mentions no record; *(identity)* a twelfth
state is a ninth state (`NDSt`) and a twelfth change is a ninth change
(`Step12` as `Step9`); *(computed again)* the twelfth exploration under C-M1
is compared with the ninth's at the same bound.

## 0. Findings in brief

1. The twelfth seed is the ninth (nothing given, two relations, four kinds,
   nothing forbidden) with one passage added: identifying two terms records,
   for each relation, which assertions of those two terms become one
   assertion, and the record is kept with the result.
2. **The record is not a third relation.** Under the chosen reading C-M1 it
   is computed from the start and the two terms, not a multiplicity beside
   `r` and `s` (D6, `no_third_rel`, `record_not_assertion`).
3. **The record of one relation is determined by that relation alone**
   (D3, `record_determined_by_rel`). Zeroing the other relation leaves it
   unchanged.
4. **The two records can differ.** Two terms, `0 r 1` once, nothing with
   `s`: the `r` record lists `xy`, the `s` record is empty (D5,
   `r_record_not_s`, `no_cross_constraint`).
5. **A later change can restore what the record lists, or not, by kind of
   record.** An empty record of two isolated terms is restored by adding a
   term (D4, `empty_record_restored_by_addTerm`). A record that lists a
   between-assertion (`xy` or `yx`) or that merges two asserted pairs into
   one is not restored by any one later change of the four kinds (D4,
   `nonempty_not_restored`). Identifying a blank extra term into a term
   that already carries assertions can restore the start in one change
   (the extra term comes back by adding a term); that record is nonempty
   but lists no between-assertion.
6. **The ninth's cost, reachability, jointly free results and non-product
   count survive under C-M1** (D9–D11): the states and the changes are the
   ninth's. Under C-M2 they do not as a *count of results*: the one-term
   state asserting nothing is several recorded results — within the 2-term
   5-round bound, six: the never-identified one at cost 1, the empty-record
   one (identifying two isolated terms) at cost 3, and four more at cost 5
   (`recorded.json`). The Lean `recorded_extra` shows only that two of them
   differ. The fewest changes to the empty-record one is 3, not the size 1
   (computed).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The sentences of the ninth seed, word for word (`diff`) |
| G17 | Identifying two terms records, for each relation, which assertions of those two terms become one assertion. The record is kept with the result. |

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, assertion `xry` or `xsy`, multiplicity, empty beginning, four kinds | given (ninth) | identity on `NDSt` / `Step9` |
| identification record, per relation | given (G17) | not a change |
| record computed on the identification, not in the result | chosen (C-M1) | the result remains a two-relation state |
| record as a field of the result | chosen unchosen, kept (C-M2) | different results; computed |
| record as a third multiplicity | refuted as a reading | G17: a record of *which assertions became one* |
| "assertions of those two terms" | chosen (C-M1) | the 2×2 block, plus outgoing and incoming pairs with each other term |
| "kept with the result" | chosen (C-M1) | extra data on the identification's outcome |
| cost, reachability, results, count under C-M1 | derived (D9–D11) | the ninth's, through the identity |
| record of `r` ignores `s`; the two records can differ; restore | derived + computed | `given.json` |

## 3. Readings that had to be chosen

**C-M1 (chosen).** The record of identifying `x < y` is computed from the
start and those two terms, per relation. A result is still a two-relation
state up to sameness (9:C6). The record lists the asserted pairs among
`{x, y}` (all becoming the merged loop) and, for each other term `z`, the
outgoing pair `(xz, yz)` and the incoming pair `(zx, zy)` that become one.
Other terms are remembered only by the pattern of which of the two pairs
were asserted, so the record is invariant under rewriting them. "Kept with
the result" is read as: the attempt that produces the result of an
identification carries the record; the record is not a third multiplicity.

**C-M2 (unchosen, kept).** A result is a ninth state together with the
identification record of the most recent identification, or no record if
none has occurred. The record persists through later non-identify changes
and is replaced by a new identification. Both computed.

C3, C5⁗, C6, C8′, C9 of the ninth paper, unchanged in kind. Bounds used here
(C8′): 3 terms with 6 rounds; 3 terms with 5; 2 terms with 8; full logs at 2
terms and 3 rounds; recorded reading at 2 terms with 5 rounds. Completeness of
the C-M1 results is the ninth's independent count at those bounds (D10).

## 4. What the record is

**D3.** The record of one relation is determined by that relation's
multiplicities and the two terms. Lean `record_determined_by_rel`;
`given.json` `r_determined_by_r`. Zeroing the other relation leaves it
unchanged.

**D5.** The two records can differ. Two terms, `0 r 1` once, nothing with
`s`: `r` lists `xy`, `s` lists nothing. Lean `r_record_not_s`,
`no_cross_constraint`; `given.json` `r_record_not_s`.

**D4.** Whether a later change restores what the record lists. An empty
record of two isolated terms is restored by adding a term (the two terms
come back, nothing was listed). Lean `empty_record_restored_by_addTerm`;
`given.json` `two_term_empty_restored`. A record that lists a
between-assertion, or that merges two asserted pairs into one, is not
restored by any one later change of the four kinds: identifying `0 r 1`
puts that assertion on the loop of the surviving term, and no one change
splits it back. Lean `nonempty_not_restored`; `given.json`
`two_term_between_restored` is false.

**D6.** The record is not a third multiplicity beside `r` and `s`. This is
the chosen reading C-M1, by construction: the state is `NDSt`, with no field
for a record. Lean `no_third_rel`, `record_not_assertion` are `⟨rfl, rfl⟩`
about the projections and do not mention a record; they are not cited as a
proof of D6.

**D8.** Identifying two terms drops a term. Lean `identify_drops_a_term`;
`given.json` `identify_drops_a_term`. The record does not put the dropped
term back.

The record statements (empty record; nonempty record; the two records
differ; `r` merged two pairs; the start is restored; the `r` record is
determined by `r`) each hold of some identification of some result and fail
of some identification of some result within 2 terms and 8 rounds
(`record_verdicts`; `record_statements_holding_of_every_identification` is
`['determined']` in the committed `summary_bound2_rounds8.json`), except
determination, which holds of every identification (D3). Determination holds
of every identification because it is true by construction of C-M1: the
record of a relation is read from that relation alone, so it is a chosen
reading, not an emergent fact (Lean `record_determined_by_rel`, stated for
`r` and closed by `simp [recordRel]`, is definitional).

## 5. What of the ninth survives

**D9.** Under C-M1 the fewest changes to a result is its size. Lean
`fewest_changes12` (the ninth's `fewest_changes9`). A record is not counted
among terms or assertions.

**D10.** The C-M1 results, rounds and shortest-sequence counts are the
ninth's at the same bound. This is an identity, not a second computation:
the C-M1 exploration is the ninth's (`twelfth.explore.explore` wraps
`ninth.explore.explore`), so the result, round and sequence comparisons in
`compare_with_ninth` agree by construction and show only determinism. The one
independent check is the count: every run's explored results equal the
ninth's orbit count (`explored_equals_independent_count`). The count is not a
product for `n ≥ 2` (9:D10, no change: a record is not in the count).

**D11.** Reachability is having a term, or the start is empty. Lean
`reach12_iff`. Jointly free results: `results_pair12`. The exchange carries
records (`recordRel_swap`, `recordOf_swap`) and carries every change
(`Step12.swap`).

## 6. The unchosen recorded tag

**D12.** Under C-M2 a ninth state may be several results. The one-term
state asserting nothing is reached with no record (one change: add a term),
with the empty identification record of two isolated terms (three changes),
and with four further records at five changes — six in all within the bound
(`recorded.json`). The Lean `recorded_extra` shows only that two of them
(the plain one and the empty-record one, tagged by a Bool) differ; the count
of six is computed. The recorded exploration at 2 terms and 5 rounds has more
results than the ninth's (`recorded.json`). The ninth's "fewest changes is
the size" fails on every recorded result carrying a record (the empty-record
one-term result costs 3, size 1, computed); it survives on the untagged one.
Note `recorded_cost_is_size` (Lean) is `rfl` — the ninth's size of the
underlying state — and is not a statement about the BFS round.

## 7. The task's questions

- **Is the record of one relation determined by that relation alone?** Yes
  (D3).
- **Can the two records differ?** Yes (D5).
- **Can a later change restore what the record lists?** Yes when the record
  is empty and the two terms were isolated (add a term). No when the record
  lists a between-assertion or merges two asserted pairs (D4).
- **Which of the ninth's cost, reachability, results and count survive?**
  All four under C-M1. Under C-M2 the result-set and the count are larger;
  cost-as-size fails on tagged identifications; has-a-term reachability of
  the underlying state survives.

## 8. What does not follow

Each item has two legal witnesses, or a proof of independence.

- Every identification records nothing — fails: two terms, `0 r 1`; holds:
  two isolated terms.
- Every identification records something — fails: two isolated terms;
  holds: two terms, `0 r 1`.
- The two records always agree — fails: D5; holds: two terms, `0 r 1` and
  `0 s 1`.
- A later change always restores the start — fails: D4 between-assertion;
  holds: two isolated terms.
- The ninth's count of results is the recorded count — fails: one-term
  state, with and without a record; holds: the empty state, no
  identification yet.

## 9. Open

- O1. Results beyond the declared bounds: the frontier of the ninth
  exploration is the C-M1 frontier; the ninth's two-term closed form (9:D11)
  gives every round with at most two terms.
- O2. Whether the outgoing/incoming groups with other terms are needed in
  Lean, or the 2×2 block already answers the task: the 2×2 block is what
  Lean records (`recordRel`); the Python record also groups other-term
  pairs. Recorded here rather than closed as a Lean identity of those two
  operations.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Contraction of a two-coloured multigraph, with a log of which arcs were
  identified.** D3–D5 classify the log of a contraction as a pair of
  preimages, one per colour, determined by that colour's arcs on the two
  vertices (D3) and able to differ (D5). That is not a graph homomorphism
  (which would send arcs to arcs without summing them) and not the tenth's
  leftover (which asked only whether some one later edit restores the
  start, not which arcs became one).
- **Edit distance from the empty two-coloured multigraph.** D9–D11 are the
  ninth's: the results up to writing are the ninth's, the distance from
  empty is vertices plus arcs of either colour, a record not counted. D12
  is that tagging each result with the log of the last contraction makes
  that count fail (the one-vertex empty graph, with and without a
  contraction log, two results, costs 1 and 3).
- **Pólya enumeration of two-coloured multigraphs.** D10 is the ninth's
  count, the record not in the cycle index. The recorded reading's extra
  results are not that enumeration.

What appears to be specific to this seed: that keeping a per-relation
record of which assertions an identification merges classifies the ninth's
identifications without adding a third relation; that the record of one
relation does not constrain the other; that a later change restores what
the record lists exactly when the identification mixed nothing that a
single addition cannot put back; and that the ninth's collapses and
independence survive exactly so long as the record is kept off the result.
