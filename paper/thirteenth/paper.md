# What follows once a coarser writing forgets which relation asserted

Thirteenth derivation. Input: `prompt/thirteenth/seed_prompt.md`. Task:
`prompt/thirteenth/prompt.md`. Claim IDs refer to `paper/thirteenth/claim_ledger.md`;
an ID written `9:D4` refers to the ninth derivation's ledger
(`paper/ninth/claim_ledger.md`, paper `paper/ninth/paper.md`). Lean names in
the namespace `Seed.Thirteenth` are in `lean4/Thirteenth/`; names in `Seed.Ninth`
are the ninth's (`lean4/Ninth/`). The axiom report for every theorem cited here
is `evidence/thirteenth/lean_axioms.txt`. Computed files are in `evidence/thirteenth/`,
written by `python code/generate_thirteenth.py`.

Every notion below carries one source status: **given**, **chosen**,
**derived**, **computed**, **refuted**, **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the thirteenth seed, and the re-check says whether the result *survives
once a coarser writing of an assertion forgets whether it was written with
`r` or with `s`*. The re-check is one of: *(no change)* the statement
mentions no coarser writing; *(identity)* a thirteenth state is a ninth
state (`NDSt`) and a thirteenth change is a ninth change (`Step13` as
`Step9`); *(computed again)* the thirteenth exploration under C-C1 is
compared with the ninth's at the same bound.

## 0. Findings in brief

1. The thirteenth seed is the ninth (nothing given, two relations, four
   kinds, nothing forbidden) with one passage added: a coarser writing of an
   assertion forgets whether it was written with `r` or with `s`; every
   result is recorded also in that coarser writing; two results that differ
   only in which relation wrote their assertions may be the same coarser
   result.
2. **The coarser writing is not a third relation.** Under the chosen reading
   C-C1 it is the one-relation state whose multiplicity at each pair is the
   sum of the `r` and `s` multiplicities (a seventh state), computed from
   the result, not a multiplicity beside `r` and `s` (D6, `no_third_rel`,
   `coarse_not_assertion`).
3. **The coarser writing determines the finer one exactly when nothing is
   asserted** (D3, `determines_of_nothing`, `not_determines_twoBetween`).
   The splits of a sum `N` are the pairs `(A, B)` with `A + B = N`; that
   pair is unique iff `N` is zero. Within 3 terms and 6 rounds, 4 results
   determine (the empty-assertion states on 0–3 terms) and 514 do not.
4. **Two finer results that differ only in which relation wrote the
   assertion may be the same coarser result.** `0 r 1` and `0 s 1` are
   different finer results and the same coarser result (D5, `coarse_extra`,
   `r_and_s_same_coarse`). Adding in `r` and adding in `s` land on the same
   coarser writing (D4, `coarse_addAssertion_r_s`).
5. **A coarser collision on one pair does not constrain another.** The two
   splits of `0-1` agree on the loop `(0, 0)` (D5, `no_cross_constraint`).
6. **The ninth's cost, reachability, jointly free results and non-product
   count survive under C-C1** (D9–D11): the states and the changes are the
   ninth's. The size of the coarser writing equals the size of the finer
   state (`size_coarse`), and the coarser writing has a term exactly when
   the finer state has one (`coarse_has_term`), so cost and reachability
   *descend*. Under C-C2 they do not as a *count of results*: at 2 terms
   and 5 rounds the ninth has 101 results and the coarser writing has 25
   (the seventh's count); `0 r 1` and `0 s 1` collapse (D12, `coarse_extra`).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The sentences of the ninth seed, word for word (`diff`) |
| G18 | A coarser writing of an assertion forgets whether it was written with `r` or with `s`. For every result, record also its coarser writing. Two results that differ only in which relation wrote their assertions may be the same coarser result. |

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, assertion `xry` or `xsy`, multiplicity, empty beginning, four kinds | given (ninth) | identity on `NDSt` / `Step9` |
| coarser writing of an assertion | given (G18) | not a change |
| coarser writing as the sum of the two multiplicities, recorded on the result | chosen (C-C1) | the result remains a two-relation state |
| coarser writing as the result | chosen unchosen, kept (C-C2) | fewer results; computed |
| coarser writing as a third multiplicity | refuted as a reading | G18: a writing that *forgets* which relation |
| "same coarser result" | chosen (C-C1) | same one-relation state up to rewriting of terms |
| "determines the finer one" | chosen (C-C1) | unique two-relation preimage |
| cost, reachability, results, count under C-C1 | derived (D9–D11) | the ninth's, through the identity |
| coarser writing of `0 r 1` equals that of `0 s 1`; size descends | derived + computed | `given.json` |

## 3. Readings that had to be chosen

**C-C1 (chosen).** The coarser writing of a two-relation state is the
one-relation state whose multiplicity at each ordered pair is the sum of
the `r` and `s` multiplicities. A result is still a two-relation state up
to sameness (9:C6). "Record also its coarser writing" is extra data on the
result, not a third multiplicity. Two finer results are the same coarser
result when those one-relation states are the same up to rewriting of
terms.

**C-C2 (unchosen, kept).** A result *is* the coarser writing. Two finer
states with the same sum are one result. Both computed.

C3, C5⁗, C6, C8′, C9 of the ninth paper, unchanged in kind. Bounds used here
(C8′): 3 terms with 6 rounds; 3 terms with 5; 2 terms with 8; full logs at 2
terms and 3 rounds; coarser reading at 2 terms with 5 rounds. Completeness of
the C-C1 results is the ninth's independent count at those bounds (D10).
Completeness of the C-C2 results is the seventh's independent count (D12).

## 4. What the coarser writing is

**D3.** The coarser writing determines the finer one exactly when nothing
is asserted. Lean `determines_of_nothing`, `empty_determines`,
`not_determines_twoBetween`; `given.json` `empty_determines`,
`two_term_between_determines`. The number of finer splits of a writing of
the terms is the product of `N(p) + 1` over ordered pairs; that product is
1 iff nothing is asserted. Within 3 terms and 6 rounds, 4 results
determine and 514 do not (`summary_bound3_rounds6.json`).

**D5.** Two finer results that differ only in which relation wrote the
assertion may be the same coarser result. Two terms, `0 r 1` once, nothing
with `s`, and the exchange of the relations: different finer, same coarser.
Lean `r_and_s_same_coarse`, `coarse_extra`, `no_cross_constraint`;
`given.json` `r_and_s_same_coarser`. The collision is on the pair `(0, 1)`;
the loop `(0, 0)` is split the same way in both (nothing asserted there).

**D4.** Adding in `r` and adding in `s` land on the same coarser writing
and differ as finer results. Lean `coarse_addAssertion_r_s`; `given.json`
`add_r_or_s_same_coarser`. Exchanging the relations keeps the coarser
writing (`coarse_swap`).

**D6.** The coarser writing is not a third multiplicity beside `r` and
`s`. Lean `no_third_rel`, `coarse_not_assertion`. The state is `NDSt`; the
coarser writing is a seventh state (`NSt`).

**D8.** The size of the coarser writing equals the size of the finer
state (terms counted once, both totals). Lean `size_coarse`,
`coarse_cost_descends`; `given.json` `size_descends_between`. The coarser
writing has a term exactly when the finer state has one (`coarse_has_term`).

The coarser statements (determines the finer one; unique split; exchange
is a different finer result with the same coarser writing; both relations
used) each hold of some result and fail of some result within 2 terms and
8 rounds (`coarse_verdicts`; `coarse_statements_holding_of_every_result`
empty in the committed `summary_bound2_rounds8.json`). None holds of every
result. "A different finer result with the same coarser writing" is read as
difference up to writing (`not same`), not as differing written tuples: a
state and its exchange can have differing `r` and `s` tuples yet be the same
result up to renaming the terms, and those are excluded (corrected at
review; change log).

## 5. What of the ninth survives

**D9.** Under C-C1 the fewest changes to a result is its size. Lean
`fewest_changes13` (the ninth's `fewest_changes9`). A coarser writing is
not counted among terms or assertions. The size of the coarser writing is
that same number, so the cost *descends*.

**D10.** The C-C1 results, rounds and shortest-sequence counts are the
ninth's at the same bound. This is an identity, not a second computation:
the C-C1 exploration is the ninth's (`thirteenth.explore.explore` wraps
`ninth.explore.explore`), so the result, round and sequence comparisons in
`compare_with_ninth` agree by construction and show only determinism (518
results at 3 terms and 6 rounds, 140 at 3 and 5, 1556 at 2 and 8, 12 at 2
and 3). The one independent check is the count: every run's explored results
equal the ninth's orbit count (`explored_equals_independent_count`). The
count is not a product for `n ≥ 2` (9:D10, no change: a coarser writing is
not in the C-C1 count).

**D11.** Reachability is having a term, or the start is empty. Lean
`reach13_iff`. Jointly free results: `results_pair13`. The exchange keeps
the coarser writing (`coarse_swap`) and carries every change
(`Step13.swap`). The has-a-term criterion *descends* (`coarse_has_term`).

## 6. The unchosen coarser result

**D12.** Under C-C2 two ninth states may be one result. `0 r 1` and
`0 s 1` are the same coarser result. Lean `coarse_extra`. The coarser
exploration at 2 terms and 5 rounds has 25 results against the ninth's
101 (`coarse.json`); the 25 are the seventh's independent count of
one-relation states within that bound. The ninth's "fewest changes is the
size" *survives* on coarser results (every finer preimage has that size;
`coarse_cost_equals_size`). Jointly free as a count of pairs of parts does
not: `(A, 0)` and `(0, A)` collapse. The non-product of the ninth becomes
the seventh's one-relation count.

## 7. The task's questions

- **When does the coarser writing determine the finer one?** Exactly when
  nothing is asserted (D3).
- **When are two finer results that disagree in which relation wrote the
  assertion the same coarser result?** When they have the same terms (up to
  rewriting) and the same sum of multiplicities; in particular whenever one
  is the exchange of the other, and whenever one is obtained from the other
  by moving assertions between `r` and `s` while keeping the sum (D4, D5).
- **Do the ninth's cost and reachability descend to the coarser writing?**
  Yes: size is preserved (`size_coarse`) and having a term is preserved
  (`coarse_has_term`). Under C-C1 they are the ninth's. Under C-C2 they
  remain the size and the has-a-term criterion of the coarser writing.
- **Which of the ninth's results and count survive?** All of them under
  C-C1. Under C-C2 the result-set and the count are strictly smaller once
  anything is asserted; jointly-free-as-a-product and the non-product count
  of two-relation states do not survive as counts of coarser results.

## 8. What does not follow

Each item has two legal witnesses, or a proof of independence.

- The coarser writing always determines the finer one — fails: `0 r 1`
  (two splits); holds: nothing asserted.
- Two finer results that differ in which relation wrote the assertion are
  always different coarser results — fails: D5; holds: `0 r 1` once versus
  `0 r 1` twice (different sums).
- The two relations always both assert something — fails: `0 r 1`, nothing
  with `s`; holds: `0 r 1` and `0 s 1`.
- The ninth's count of results is the coarser count — fails: 101 against 25
  at 2 terms and 5 rounds; holds: the empty state, round 0.

## 9. Open

- O1. Results beyond the declared bounds: the frontier of the ninth
  exploration is the C-C1 frontier; the ninth's two-term closed form (9:D11)
  gives every round with at most two terms. The seventh's two-term closed
  form gives every C-C2 round with at most two terms.
- O2. The number of finer preimages of a coarser writing, up to rewriting
  of terms (not just in a fixed writing): the Python `splits` counts in a
  fixed writing; Lean proves uniqueness only for the empty-assertion case
  and exhibits one collision. Recorded here rather than closed as a Lean
  enumeration of preimages.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Forgetting the colour of a two-coloured multigraph.** D3–D5 classify
  the map that adds the two colours' multiplicities pair by pair. That is
  not a graph homomorphism (which would send arcs of one colour to arcs of
  one colour) and not the ninth's exchange (which swaps the colours without
  adding them). The fibre is a product of simplices, one per ordered pair,
  unique only at zero (D3).
- **Edit distance from the empty two-coloured multigraph.** D9–D11 are the
  ninth's: the results up to writing are the ninth's, the distance from
  empty is vertices plus arcs of either colour, a coarser writing not
  counted. D8 is that this distance equals the distance of the
  one-coloured image (the size descends). D12 is that taking the
  one-coloured image as the result makes the count fail (101 two-coloured
  writings against 25 one-coloured, at 2 vertices and 5 edits).
- **Pólya enumeration of two-coloured versus one-coloured multigraphs.**
  D10 is the ninth's count, the coarser writing not in the cycle index.
  The coarser reading's 25 results are the seventh's enumeration, not that
  two-coloured count.

What appears to be specific to this seed: that recording a coarser writing
which forgets which relation asserted classifies the ninth's results
without adding a third relation; that the coarser writing determines the
finer one only when nothing is asserted; that a collision of one pair does
not constrain another; and that the ninth's collapses and independence
survive exactly so long as the coarser writing is kept off the identity of
the result.
