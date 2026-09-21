# What follows once a writing can collide terms it does not identify

Eleventh derivation. Input: `prompt/eleventh/seed_prompt.md`. Task:
`prompt/eleventh/prompt.md`. Claim IDs refer to `paper/eleventh/claim_ledger.md`;
an ID written `9:D4` refers to the ninth derivation's ledger
(`paper/ninth/claim_ledger.md`, paper `paper/ninth/paper.md`). Lean names in
the namespace `Seed.Eleventh` are in `lean4/Eleventh/`; names in `Seed.Ninth`
are the ninth's (`lean4/Ninth/`). The axiom report for every theorem cited here
is `evidence/eleventh/lean_axioms.txt`. Computed files are in `evidence/eleventh/`,
written by `python code/generate_eleventh.py`.

Every notion below carries one source status: **given**, **chosen**,
**derived**, **computed**, **refuted**, **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the eleventh seed, and the re-check says whether the result *survives
once a writing can collide terms it does not identify*. The re-check is one
of: *(no change)* the statement mentions no writing; *(identity)* an eleventh
state is a ninth state (`NDSt`) and an eleventh change is a ninth change
(`Step11` as `Step9`); *(computed again)* the eleventh exploration under C-W1
is compared with the ninth's at the same bound.

## 0. Findings in brief

1. The eleventh seed is the ninth (nothing given, two relations, four kinds,
   nothing forbidden) with one passage added: a writing of terms may give two
   terms the same letter while they remain two terms; assertions are read from
   the writing; if two terms are written the same and their assertions differ,
   the writing does not determine the assertions.
2. **A writing is not identifying, and is not a third relation.** Under the
   chosen reading C-W1 it is a function from a result's terms to letters, not
   a multiplicity beside `r` and `s` (D6, `no_third_rel`). Identifying two
   terms drops a term; writing them the same leaves both (D8,
   `writing_not_identify`).
3. **An injective writing always determines the assertions** (D3,
   `inj_determines`, `apart_determines_twoBetween`). A writing determines
   exactly when, in each relation, the multiplicity is constant on every
   letter-pair rectangle.
4. **A collision forbids every coarser writing from determining** (D4,
   `coarser_of_not_determines`). That is what "same writing, different
   assertions" forbids of every coarser writing.
5. **A collision of one relation does not constrain the other.** Two terms
   written the same, `xry` asserted and nothing with `s`, fails to determine
   `r` and determines `s` (D5, `r_collision_not_s`, `no_cross_constraint`).
6. **The ninth's cost, reachability, jointly free results and non-product
   count survive under C-W1** (D9–D11): the states and the changes are the
   ninth's. Under C-W2 they do not as a *count of results*: the two-term
   state asserting nothing is two labeled results, one per writing (D12,
   `labeled_extra`). The fewest changes to a labeled result is still the
   size (`labeled_cost_is_size`).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The sentences of the ninth seed, word for word (`diff`) |
| G16 | A writing of terms may give two terms the same letter while they remain two terms. Assertions are read from the writing. If two terms are written the same and their assertions differ, the writing does not determine the assertions. |

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, assertion `xry` or `xsy`, multiplicity, empty beginning, four kinds | given (ninth) | identity on `NDSt` / `Step9` |
| writing; two terms the same letter; remaining two terms | given (G16) | not a change |
| writing recorded as a reading, not in the result | chosen (C-W1) | the result remains a two-relation state |
| writing as a label on the result | chosen unchosen, kept (C-W2) | different results; computed |
| writing as a third multiplicity | refuted as a reading | G16: a writing of *terms* |
| writing as identifying | refuted as a reading | G16: they remain two terms |
| "determines the assertions" | chosen (C-W1) | constant multiplicity on every letter-pair rectangle, each relation |
| "coarser writing" | chosen (C-W1) | writes together every pair the first writes together, and possibly more |
| cost, reachability, results, count under C-W1 | derived (D9–D11) | the ninth's, through the identity |
| injective writings determine; collision forbids coarser; `r` not `s` | derived + computed | `given.json` |

## 3. Readings that had to be chosen

**C-W1 (chosen).** A writing is a function from a result's terms to letters.
A result is still a two-relation state up to sameness (9:C6). The writing
determines the assertions exactly when each relation is constant on every
letter-pair rectangle. A writing `w'` is coarser than `w` when it writes
together every pair `w` writes together, and possibly more.

**C-W2 (unchosen, kept).** A result is a ninth state together with a writing
of its terms (up to renaming letters). Both computed.

C3, C5⁗, C6, C8′, C9 of the ninth paper, unchanged in kind. Bounds used here
(C8′): 3 terms with 6 rounds; 3 terms with 5; 2 terms with 8; full logs at 2
terms and 3 rounds; labeled reading at 2 terms with 4 rounds. Completeness of
the C-W1 results is the ninth's independent count at those bounds (D10).

## 4. What a writing is

**D3.** An injective writing determines the assertions: no two terms share a
letter, so every rectangle is a singleton. Lean `inj_determines`,
`apart_determines_twoBetween`; `given.json` `two_term_between_injective_determines`.

**D4.** If a writing does not determine, neither does any coarser writing.
Lean `coarser_of_not_determines`; `given.json` `collision_forbids_coarser`
(three terms, `0 r 1` once, writing that collides the first two, coarser
writing that collides all three).

**D5.** A collision of one relation need not be a collision of the other.
Two terms, `0 r 1` once, nothing with `s`, both written the same letter:
`r` is not determined, `s` is. Lean `r_collision_not_s`,
`no_cross_constraint`; `given.json` `r_collision_not_s`.

**D6.** A writing is not a third multiplicity beside `r` and `s`. Lean
`no_third_rel`, `writing_not_assertion`. The state is `NDSt`.

**D8.** Identifying two terms drops a term; writing them the same leaves
both. Lean `identify_drops_a_term`, `collide_keeps_terms`,
`writing_not_identify`; `given.json` `identify_drops_a_term`,
`collide_keeps_two_terms`.

The writing statements (injective; determines; collides; collides in `r`
only) each hold of some writing of some result and fail of some writing of
some result within 2 terms and 4 rounds (`writing_verdicts`).

## 5. What of the ninth survives

**D9.** Under C-W1 the fewest changes to a result is its size. Lean
`fewest_changes11` (the ninth's `fewest_changes9`). A writing is not counted
among terms or assertions.

**D10.** The C-W1 results, rounds and shortest-sequence counts are the
ninth's at the same bound (`compare_with_ninth`; `ninth_ok` in every run).
Completeness is the ninth's independent count. The count is not a product
for `n ≥ 2` (9:D10, no change: a writing is not in the count).

**D11.** Reachability is having a term, or the start is empty. Lean
`reach11_iff`. Jointly free results: `results_pair11`. The exchange carries
determination (`determines_swap`) and carries every change (`Step11.swap`).

## 6. The unchosen label

**D12.** Under C-W2 a ninth state may be several results. The two-term state
asserting nothing is reached with writing `(0, 1)` and with writing `(0, 0)`
(`labeled_extra`); those are different results, both at cost 2, the size.
The labeled exploration at 2 terms and 4 rounds has more results than the
ninth's (`labeled.json`). The ninth's "fewest changes is the size" survives
on labeled results (`labeled_cost_is_size`); the ninth's *count* does not.

## 7. The task's questions

- **When does the writing determine the assertions?** Exactly when each
  relation is constant on every letter-pair rectangle (C-W1). In particular
  every injective writing determines (D3).
- **What does a collision forbid of every coarser writing?** Determining
  the assertions (D4).
- **Does a collision of one relation constrain the other?** No (D5).
- **Which of the ninth's cost, reachability, results and count survive?**
  All four under C-W1. Under C-W2 the result-set and the count are larger;
  cost-as-size and has-a-term reachability of the underlying state survive.

## 8. What does not follow

Each item has two legal witnesses, or a proof of independence.

- Every writing determines the assertions — fails: two terms, `0 r 1`, both
  written the same; holds: any injective writing.
- Every writing collides — fails: the empty state's only writing; holds: the
  colliding writing of two terms with `0 r 1`.
- A collision of `r` is a collision of `s` — fails: D5; holds: two terms,
  `0 r 1` and `0 s 1`, both written the same.
- Writing two terms the same is identifying them — refuted by G16 and D8.
- The ninth's count of results is the labeled count — fails: two writings of
  the two-term empty state; holds: the empty state, one writing.

## 9. Open

- O1. Results beyond the declared bounds: the frontier of the ninth
  exploration is the C-W1 frontier; the ninth's two-term closed form (9:D11)
  gives every round with at most two terms.
- O2. Whether a writing that determines, read as letter-pair multiplicities,
  is the same two-relation state as the identification of every pair it
  collides: it is not (identifying *adds* multiplicities; reading takes the
  constant value). Recorded here rather than closed as a Lean identity of
  two different operations.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Quotient of a labelled two-coloured multigraph.** D3–D5 classify a
  writing of the vertices as determining the arcs exactly when every pair of
  labels sees one multiplicity in each colour. That is not a graph
  homomorphism (which would send arcs to arcs) and not a contraction (which
  would identify vertices and *add* the arcs, D8). A collision forbids every
  coarser labelling from determining (D4), the usual monotonicity of a
  partition refinement, here read on two colours independently (D5).
- **Enumeration of two-coloured multigraphs up to relabelling.** D9–D11 are
  the ninth's: the results up to writing are the ninth's, the distance from
  empty is vertices plus arcs of either colour, a writing not counted. D12
  is that tagging each result with a partition of its vertices makes that
  count fail (the two-vertex empty graph, two partitions, two results).
