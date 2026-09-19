# What follows from `arb` once with a second relation `s`: counted assertions, four kinds of change, nothing forbidden

Eighth derivation. Input: `prompt/eighth/seed_prompt.md`. Task:
`prompt/eighth/prompt.md`. Claim IDs refer to `paper/eighth/claim_ledger.md`;
an ID written `1:D8` refers to the first derivation's ledger
(`paper/claim_ledger.md`, paper `paper/paper.md`), `4:D8` to the fourth's
(`paper/fourth/`), `6:D8` to the sixth's (`paper/sixth/`), `7:D4` to the
seventh's (`paper/seventh/`). Lean names in the namespace `Seed.Eighth` are
in `lean4/Eighth/`; names in `Seed.Seventh`, `Seed.Sixth`, `Seed.Fifth`,
`Seed.Fourth`, `Seed` are the earlier derivations' (`lean4/Seventh/`,
`lean4/Sixth/`, `lean4/Fifth/`, `lean4/Fourth/`, `lean4/H3V7N5QF/`). Where a
short name exists in two libraries the eighth's is meant unless the
namespace is written. The axiom report for every theorem cited here, of any
of the eight libraries, is `evidence/eighth/lean_axioms.txt`. Computed files
are in `evidence/eighth/`, written by `python code/generate_eighth.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; the unchosen
readings are listed), **derived** (proved), **computed** (output of `code/`),
**refuted** (proved impossible), **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the eighth seed, and the re-check says whether the result *survives the
second relation* — per relation, jointly, or not. The re-check is one of five
kinds. *(no change)*: the statement mentions no relation at all (the terms,
the names, the rewritings), so it stands as it is. *(on a part)*: a
two-relation state has two *parts*, its `r` part and its `s` part, each a
state of the sixth seed with the same terms and names (`DSt.proj`); every
change of the eighth seed is a change of the sixth on a part and leaves the
other part as it is, or is a change of the sixth on both parts
(`Step8.proj`, `Step8.proj_self`); so what the sixth proved about one
multiplicity function holds here for each part, and "per relation" means
exactly that. *(through the embedding)*: a state of the sixth seed read as a
two-relation state asserting nothing with `s` (`MSt.ofR`) turns every change
and sequence of the sixth into one of the eighth (`Step6.ofR`,
`Reach6.ofR`); what the sixth proved for a particular sequence holds for it
here. *(re-proved)*: the earlier proof handled one multiplicity function and
a statement about both is proved afresh. *(computed again)*: a computed
statement of the sixth derivation is re-run beside the eighth exploration
and compared on the results asserting nothing with `s`. Results of the
earlier derivations that fail, or change shape, under the eighth seed are
listed in §8.

## 0. Findings in brief

1. The eighth seed is the sixth (counted assertions, four kinds of change,
   nothing forbidden) with a second relation: an assertion is `xry` or
   `xsy`; `arb` alone is given; whether `bra` or anything written with `s` is
   asserted is not given (given, §1). The state gains a second multiplicity
   function on the same terms; the changes range over both relations; an
   identification merges both; a rewriting rewrites both.
2. **The results are every well-formed two-relation state with a term, and
   they are jointly free**: for every well-formed `r` part and every
   well-formed `s` part on the same terms and names, the pair is a result
   (D5, `results_pair`). No result in one relation constrains the other.
   The sixth's results are exactly the results asserting nothing with `s`,
   at the same rounds, reached by the same shortest sequences (computed
   again on every run).
3. **The cost is additive per relation.** The fewest changes to a result is
   the sixth's fewest changes to its `r` part plus the total multiplicity of
   its `s` part: `size − size(given) + 2·lost`, with the size counting both
   relations and the destroyed givens read on `r` (D4, `costA8_eq`,
   `fewest_changes8_A`). The `s` part costs exactly its total, as the
   seventh seed's states cost their size: nothing is given in `s`, so
   nothing in `s` is ever destroyed.
4. **The reachability criterion survives as a statement about the `r`
   part's names**: a result reaches another exactly when the names, if one
   term at the start, are one term at the end (names kept), always (any
   rewriting) — and the `s` parts impose nothing (D8, `reach8_iff`,
   `reach8_iff_r`). Two results with the same `r` part reach each other
   whatever their `s` parts.
5. **Separability — telling the two named terms apart — is a property of
   the terms, shared by both relations**: the names are one term in `r`
   exactly when they are in `s`, an identification merges both relations at
   once, and the one-way merge of the names is the eighth's one irreversible
   change as it was the sixth's (D2, D7). Nothing separates one relation
   from the other but the assertions themselves.
6. **How the two relations interact**: through the terms and the names
   only. An assertion of one relation leaves the other part as it is; a
   term and an identification act on both; a rewriting rewrites both
   (`interaction`). This is why the *set* of results is a product of the
   single-relation results (jointly free), the *cost* is a sum, the
   *criterion* reads `r` alone — and why the *count* of results up to
   sameness is *not* the product of the single-relation counts (the swap of
   two terms acts on both relations at once: with two terms and one
   assertion in each relation there are 8 results, not 2 × 2 = 4; D10, K1).
   `s` is an independent copy of `r`'s structure in every respect but this
   one, and in one more: it carries no given, so its cost and its statements
   are the seventh seed's, not the sixth's.
7. A result with `n` terms and `d_r + d_s` asserted pairs (diagonal pairs
   included) has `C(n, 2) + d_r + d_s + 1 + 2n²` changes, none obstructed,
   `n` plus the related pairs in `r` of them making some `xrx` asserted on a
   result asserting none, and likewise for `s` (D3). With the given terms
   only the results of round `r` are the sixth's two-term kinds convolved
   with the `s` states, quartic in `r` (D11), so far fewer rounds than 100
   complete and the bounds are declared (C8′). Within the bounds the
   exploration is complete, certified by an independent count with two
   multiplicities on every cycle of the rewriting (D10). Everything claimed
   as derived is in Lean, the every-writing statements included (target 5
   of the plan closed on the single attempt); proved in the paper and
   checked by computation only: the change-count of a result and which
   changes make some loop asserted (D3), which changes raise the cost by
   exactly one (D4(iv)), the within-bound completeness (D10), the two-term
   closed forms (D11), the fate of the unchosen beginnings with
   something in `s` (C2″) and of the unchosen reading of identification
   (D15).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2⁗ | An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G3′ | `arb` is asserted with multiplicity one. |
| G5′ | Whether `bra`, or anything written with `s`, is asserted is not given. |
| G6 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G11 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, prove what is complete within it. |
| G14 | Any outcome is valid. |

G2⁗ and G5′ replace the sixth seed's G2‴ and G5; nothing else changes
(`diff`; `research/eighth/reading_the_seed.md`). Every other sentence is the
sixth seed's word for word.

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry` or `xsy`, the two relations, multiplicity | given (G1, G2⁗) | |
| adding raises a multiplicity by one; removing lowers it by one | given (G2⁗) | in either relation |
| asserted = multiplicity at least one; the two-relation state | chosen (C1′; 4:C1′ on each part) | the fourth's model twice, on the same terms: `DState`, Lean `DSt` |
| the `r` part, the `s` part | derived (§4, `DSt.proj`) | each a state of the sixth seed |
| a state of the sixth seed as a two-relation state | derived (`MSt.ofR`) | nothing in `s` |
| `xrx`, `xsx` are assertions | given (G2⁗) | nothing forbids them |
| `a`, `b` are two terms to begin with | derived (D1) | not kept (D2) |
| what is given: `a`, `b`; `arb` once; `bra` once or not at all; nothing with `s` | given (G3′), chosen (C2″) | unchosen: beginnings asserting something with `s`; harmless (D5) |
| supply of letters not capped | chosen (C3) | harmless |
| `r`, `s` do not write terms | chosen (C9) | writing only |
| change, four kinds over two relations; what identifying does | given (G6, G7) | in every assertion of both relations |
| the multiplicities of the pairs an identification merges add up, in each relation separately | chosen (C5⁗) | unchosen: the larger of the two; same results and reachability; the cost as 6:D19 (D15) |
| removing what is not asserted, identifying a term with itself: not changes; adding what is asserted is a change | chosen (C5⁗) | |
| the order of the changes of a result | chosen (C6) | identifications, removals in `r`, in `s`, a term, additions in `r`, in `s` |
| destroyed given, cost | derived (D4) | the sixth's on the `r` part; the `s` total added |
| result | chosen (C6) | a two-relation state up to sameness |
| the results, as a set | derived (D5) | every well-formed two-relation state with a term; jointly free |
| sameness | given (G12) | two readings, both kept: chosen (C4); a rewriting rewrites both relations |
| terms and assertions added to what is given | given (G11) | both relations counted, with multiplicity; may be negative |
| round; what counts as one change | chosen (C6) | the round of a result is its cost (D4) |
| bound, frontier | given (G13) | bound on terms and on rounds: chosen (C8′) |
| shortest sequences reaching a result; sequences of every length | computed (K7); derived (D9, D10) | exact within the bound where D10 says; infinitely many sequences in all |
| reachability between results | derived (D8) | the names of the `r` part decide; the `s` part imposes nothing |
| parity of the cost | derived (D4) | every change moves it by an odd amount |
| counts of results by terms, total multiplicity, destroyed givens | computed (K1) | by series, two multiplicities on every cycle |
| the interaction of the two relations | derived (D12; `interaction`) | through the terms and the names only |
| separability (the task's word) | chosen reading (§7) | telling the named terms apart: a property of the terms, shared by both relations (D2) |
| what survives the second relation | derived (§7; `Eighth/Compare.lean`) | see §8 for what changes shape |

## 3. Readings that had to be chosen

C1′ is 4:C1′ on each part; C3, C4, C6, C9 are the earlier derivations',
restated; C8′ is the fourth's to sixth's; C2″ and C5⁗ are the sixth's C2′
and C5‴ with the second relation.

**C2″. To begin with: the terms `a` and `b`; `arb` once; `bra` once or not
at all; nothing with `s`.** The seed flags `bra` and "anything written with
`s`" alike as not given. For `bra` the earlier derivations kept two
beginnings; for `s` there are infinitely many candidates (any multiplicities
of `asa`, `asb`, `bsa`, `bsb`), every one of them a result of the beginning
with nothing in `s` (D5) and reaching the same results (D8: the criterion
does not look at `s`). So the beginning with nothing in `s` is chosen and the
others are kept as alternatives that add no result. They differ in cost:
from a beginning asserting `G_s` with `s` (each once), the fewest changes to
a result is `size − size(given) + 2·lost` with the given `s` assertions
counted among the givens — the destroyed givens of the `r` part plus the
number of given `s` assertions with multiplicity zero (names apart), or,
with the names one term, the merge plus the given `r` and `s` assertions the
merge did not carry into `crc` and `csc`. Proof: the potential argument of
D4 with the `s` part treated as the `r` part is treated, since nothing in
the argument uses that the given lies in `r`; the upper bound removes the
missing givens of both relations before the identification. Not computed
(O4); the chosen beginning's formula is the case `G_s = ∅`.

**C3. No cap on the number of terms.** The sequences used in the proofs of
D4 and D5 never have more terms than `max(2, terms of the target)`; the
sequence of D8 uses at most `max(terms) + 2`; as 6:C3.

**C4. Sameness, two readings, both kept.** FREE and ANCHORED as 1:C4; either
way a rewriting acts on both relations at once. Two states whose parts are
the same up to *separate* rewritings need not be the same result (`a b; arb
bsb` and `a b; arb asa` under any rewriting: the `s` parts are the same up
to the swap, the `r` parts only as they stand; D10).

**C5⁗. What is a change.** As 6:C5‴ in either relation: adding an assertion
that is asserted already is a change, and so is adding `xrx` or `xsx`;
removing what is not asserted and identifying a term with itself are not
changes. **Identification with two relations.** "Replaces both by one term
in every assertion": each time an assertion of either relation is asserted
its terms are replaced, so the pairs of each relation that become one pair
have their times added up, separately (`code/eighth/state.py` `identify`,
the fifth's on each part; Lean `DSt.identify`). Unchosen: the larger of the
two, per relation; the two readings give the same results and the same
reachability, and the same cost without `bra` (D15).

**C6. Results and rounds.** As 6:C6 with two relations: a result is a
two-relation state up to sameness; round `k` performs every change on every
result first reached in round `k − 1`; every change counts one. Fewest
additions first: identifications, removals in `r`, removals in `s` (no
addition), then a term, then the additions in `r`, then in `s` — the seed's
order of kinds and of relations among equals. Unchosen: other orders; the
order cannot move a result to another round (D4).

**C8′. Bound on terms and on rounds.** As 4:C8′ to 6:C8′: within any bound
on terms the results are infinite, so every exploration is bounded in terms
and in rounds. A result now has `2n²` pairs to assert, so the results per
round grow faster than the sixth's; the independent count sized every run
in advance (`change_log.md`, item 9): 4 terms (FREE) or 3 terms (ANCHORED)
with 5 rounds; 3 terms with 6 rounds; 2 terms with 8 rounds; under ANCHORED
a counts-only census at 4 terms with 5 rounds. Full attempt logs at 2 terms
and 3 rounds; reachability among the results of 2 terms and 4 rounds, along
the changes among the results of 2 terms and 7 rounds (enough for every
sequence the proof of D8 uses between two of them: clearing `s`, the
sixth's path on `r`, adding `s`). The seed's 100 rounds with the given terms
only would hold about 7 · 10^11 results (D11) and are not run.

**C9.** `r` and `s` write assertions, not terms.

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. `a` and `b` are two terms to begin with, and not for good.** What is
given is the sixth's beginning with nothing in `s` (`givenA8 = givenA4.ofR`,
`givenB8`); its names are two terms (`givenA8_a`, `givenA8_b`; 6:D1 through
the embedding). Identifying them is one change to `a (a and b are one term);
ara` with nothing in `s` (`identify_zero`: an empty relation stays empty
under an identification), and with `asb` asserted first to `a; ara asa` —
the merge carries the `s` assertions along exactly as it carries the `r`
ones (`proj_identify` for both parts).

**D2. The one irreversible change is the merge of the names, in both
relations at once.** Once `a` and `b` are one term they are one term after
every sequence of changes: `Step8.names_stay_merged`,
`Reach8.names_stay_merged` (6:D7 on the `r` part, since the names are
fields of the state, shared by the two parts). A two-relation state has one
pair of names, so the names are one term in the `r` part exactly when they
are in the `s` part: the property is not per relation but of the terms. From
a state with the names one term what is given is never reached
(`merged_never_apart8`). **Separability** (the task's word), read as telling
the two named terms apart, is thus a property of the terms shared by both
relations and lost by both at once (§7).

**D3. How many changes a result has, and which make some loop asserted.**
A result with `n` terms and `d_r + d_s` asserted pairs, diagonal pairs
included, has `C(n, 2) + d_r + d_s + 1 + 2n²` changes, every one performed
(the sixth's count with the assertions of the second relation added;
computed: `attempts_equal_formula` true in every run; the formula is not a
Lean statement, O3). On a result asserting
no `xrx`, `n` plus the number of related pairs *in `r`* of its changes make
some `xrx` asserted, and on a result asserting no `xsx`, `n` plus the related
pairs *in `s`* make some `xsx` asserted: 6:D3's characterisation on each part
(`Step8.proj` splits a change onto a part, or leaves the part as it is; it
does not count the list; computed with the sixth's own function on each part,
`xrx_making_equal_sixth_formula`, `xsx_making_equal_sixth_formula` true in
every run).

**D4. Fewest changes (cost): additive per relation.** Let what is given
have `m0` assertions (`1` without `bra`, `2` with), so size `2 + m0` with
size = terms + the sum of all multiplicities of both relations. For a
well-formed two-relation state `G` with names let `lost(G)` be the sixth's
destroyed givens read on the `r` part (`lostA8 G = lostA6 (G.proj false)`;
the given lives in `r` alone). Then the fewest changes from what is given to
`G` is

    size(G) − (2 + m0) + 2 · lost(G)  =  (the sixth's fewest changes to the r part) + Σ s

(`costA8_eq`, `costB8_eq`: definitional). *(i) Lower bound.* `size +
2·lost` (`costA8`, `costB8`) rises by at most one per change
(`Step8.costA_le`, `_B`): every change either keeps the `r` part and moves
the `s` total by one (an `s` assertion or removal), or is a change of the
sixth on the `r` part and keeps the `s` total (a term: `Seed.Fourth.
total_addTerm` on the `s` part; an `r` change: the `s` part is untouched; an
identification: `Seed.Fifth.total_identify` on the `s` part) — `Step8.split`
— and in the second case the sixth's `Step6.costA_le` on the `r` part (6:D8,
on a part) bounds the rise. So a result reached in `n` changes has `cost ≤
n + cost(given)`: `Reach8.costA_le`, `fewest_changes8_lower_A`, `_B`. *(ii)
Upper bound.* The sixth's sequence to the `r` part (6:D8(ii),
`fewest_changes6_A`, `_B`), lifted to the states asserting nothing with `s`
(`Reach6.ofR`: every change of the sixth is a change of the eighth there,
the identification keeping the empty `s` relation empty, `ofR_identify`),
then the `s` additions one at a time (`reach8_raise`, the sixth's
`reach6_raise` with a relation tag; `reach8_from_ofR`):
`fewest_changes8_A`, `fewest_changes8_B`. *(iii) Every writing.* Changes
commute with one-to-one rewriting of both relations (D7) and the cost is the
same in every writing (`costA8_rename`, `costB8_rename`), so the fewest
changes to a result is the cost of any of its writings
(`fewest_changes8_every_writing_A`, `_B`; target 5 of the plan closed).
*Under FREE* the names are placed to make the `r` part's destroyed givens
least (the sixth's `lost_free` on the `r` part); the `s` part has no say
(computed: the closed form equals the best placement on every two-relation
state with at most 2 terms and no multiplicity above 2, 6 660 states,
`free_cost_closed_form_mismatches` empty, and the round of every explored
result equals the formula in all twelve runs and both census runs,
`round_equals_cost_formula_for_every_result`). *(iv) Which changes raise
the cost by exactly one.* Every `s` addition; no `s` removal; a term; an
`r` addition, removal or identification exactly when the sixth's rule
(6:D8(iv)) says so on the `r` part (computed: `code/eighth/cost.py`
`raises_by_one` agrees with the outcome on every change within the bound
of every run with names, `cost_rule_disagreements` empty). *(v) Parity.*
Every change moves the size by exactly one (`Step8.size_step`) and the
destroyed givens enter twice, so every change moves the cost by an odd
amount; no change keeps the round (`Reach8.size_parity`;
`changes_keeping_the_round: 0` in every run). **What survives.** On the
results asserting nothing with `s` the sixth's fewest changes survive as they
stand (`fewest_changes8_of_r_A`, `_B`); a state whose `r` part is what is
given costs exactly its `s` total (`s_costs_its_total`) — the seventh's
cost, the size, on the `s` relation (7:D4 re-checked: nothing is given in
`s`, and the `s` additions are the seventh's additions).

**D5. Everything well formed is a result; the results are jointly free.**
Every well-formed two-relation state with at least one term is a result of
either beginning, its names on any terms: `result8_iff_A`, `result8_iff_B`
(from D8). For every well-formed `r` part `m` and `s` part `m'` on the same
terms and names, the pair is a result (`results_pair`): no result in one
relation constrains the other. **The sixth's results are the results
asserting nothing with `s`**: every result of the sixth is a result of the
eighth with nothing in `s` at the same round (`results_ofR_A`, `_B`, through
the embedding); among the states asserting nothing with `s` the two seeds
have the same results (`results_r_iff`); the eighth has results the sixth
has not (`results_grow`: `asb` added to what is given); and both parts of
every result are results of the sixth (`proj_results`). Computed: in every
run and census the results asserting nothing with `s`, read as their `r`
parts, with their rounds, are exactly the sixth derivation's exploration's at
the same bound and rounds, with the same numbers of shortest sequences
(`same_results_and_rounds_as_sixth_derivation`,
`same_shortest_sequence_counts_as_sixth_derivation`; 6:K1, 6:K2, 6:K7
computed again) — a shortest sequence to such a result never touches `s`,
since an `s` addition would need an `s` removal, which is not cost-raising.

**D6. What every result has.** Every result is well formed, has at least one
term, and is finite (`Reach8.wf`, `Reach8.nonempty`; 6:D6 on each part).
Nothing else is kept (N6).

**D7. Changes commute with one-to-one rewriting of both relations;
sequences keep their length.** `rename8` rewrites both relations; its parts
are the fourth's `rename4` of the parts (`proj_rename8`, definitionally), so
4:D11's and 5:D11's commutation lemmas on a part give `rename8_addTerm`,
`rename8_addAssertion`, `rename8_remove`, `rename8_identify` (through
`ext_proj`: a two-relation state is determined by its parts), and
`Step8.rename`, `Reach8.rename`, `size_rename8`, `costA8_rename`,
`costB8_rename` follow (6:D11 on each part).

**D8. Reachability: the names of the `r` part decide; the `s` part imposes
nothing.** A well-formed two-relation state `t` is reachable from a
well-formed `s` exactly when the names, if one term in `s`, are one term in
`t`: `reach8_iff`. Necessity is D2. Sufficiency (`reach8_of_names`): remove
every `s` assertion (`reach8_clear_s`, the fifth's `reach5_clear` on the `s`
part, which leaves the embedding of the `r` part, `eq_ofR_of_nothing_in_s`);
follow the sixth's path on the `r` part (6:D12, `reach6_of_names`, through
the embedding: nothing in `s` all along); add the target's `s` assertions
(`reach8_from_ofR`). So reachability of two-relation states is reachability
of their `r` parts under the sixth seed (`reach8_iff_r`), and two results
with the same `r` part reach each other whatever their `s` parts
(`same_r_part_mutual`). Under FREE every result reaches every result.
Computed: the criterion agrees with a search along the changes among the
results within 2 terms and 7 rounds on every ordered pair of results within
2 terms and 4 rounds, in all four combinations (`criterion_agrees_with_
search`; 463 761 pairs, names kept, no `bra`), and every pair of results with
the same `r` part is reachable both ways
(`ordered_pairs_with_the_same_r_part = of_which_reachable_both_ways`).

**D9. Reachability is mutual within two classes; every result reaches
itself; any two results are comparable.** `reach8_symm`, `reach8_back_A`,
`reach8_total`; every well-formed state with a term reaches itself in two
changes (`cycle2_8`: add `xrx`, remove it — `remove_addAssertion`), so the
lengths of the sequences reaching a result are unbounded (`Reach8.cycles`,
`Reach8.unbounded`) and infinitely many sequences reach every result.
One-way reachability stays refuted (`no_return_fails8`, `antisymm_fails8`,
`length_not_unique8`; 6:D13 through the embedding). Computed: 190 950
unordered pairs of different results reachable both ways among the 681
results within 2 terms and 4 rounds (names kept, no `bra`), 40 590 ordered
pairs unreachable — all from the 66 results with the names one term to the
615 with them apart; every result has a two-change cycle in every run.

**D10. Within the bound the exploration is complete; the frontier is exact;
the shortest-sequence counts are exact where said.** *Completeness.* Let the
bound be `N` terms and `R` rounds. Every well-formed state with at most `N`
terms and cost at most `R` lies at the end of the sequence of D4(ii), whose
states have at most `max(2, terms)` terms and whose cost rises by exactly one
at each change; so every state on it is within the bound and, by induction
along it, found by the exploration in round = cost. Every explored state is
a well-formed state within the bound by construction. The results with `n`
terms, total multiplicity `t` (both relations) and destroyed givens `lost`
are counted independently by the orbit method: a rewriting leaves a
two-relation state unchanged exactly when each relation's multiplicity is
the same along each cycle of pairs, so every cycle of the rewriting (the
sixth's off-diagonal and diagonal cycles, 6:D14, no change) carries two
multiplicities — the `r` factor is the sixth's, by kind of the named terms
and capped where the largest `xrx` multiplicity matters, and the `s` factor
is free, `Π 1/(1 − x^L)` (`code/eighth/orbits.py`: `count_free`,
`count_named`, `counts_by_lost`). **The count is not a product.** For `n ≥ 2`
the number of results with `n` terms exceeds the product of the
single-relation counts (`product_count`): the same rewriting must fix both
relations at once. With two terms and total 2 there are 20 results and the
product gives 16; with one assertion in each relation, 8 and 4 (K1;
`count_exceeds_product_for_two_or_more_terms`). With one term the two agree
(`product_equals_count_for_one_term`). The explored counts by (terms,
total, lost) equal the independent counts restricted to cost at most `R` in
every run and census (`explored_equals_independent_count`), and the counts
agree with a listing of every writing for small `n` and `t`
(`tests/test_eighth_orbits.py`). *Frontier.* An attempt leaves the bound on
terms exactly when it is "add a term" on a result with `N` terms: one entry
per such result whose changes were attempted
(`frontier_entries_are_1_per_state_with_N_terms` true in every run); the
results of round `R` are the second part. *Shortest sequences.* A shortest
sequence consists of cost-raising changes (D4(iv)); the `s` additions never
add a term, so the sixth's exactness clauses (6:D14) hold on the `r` part:
exact when the result has fewer terms than the bound or the names are apart
(names kept), or no optimal placement of the names on the `r` part puts
them on one term (any rewriting; `sequences_exact`). *Rounds.* The number of
results of round `r` without any bound is given by the series and the cost
formula (`layer_counts`); rounds `0 … N − 2` of a run within `N` terms agree
with it (`rounds_agreeing_with_unbounded_formula`), since a result of round
`r` has at most `r + 2` terms, as under the sixth seed.

**D11. Two terms: the results of every round in closed form.** With the
given terms only (names kept) the results of round `r` are the sixth's
two-term kinds of round `k` that have two terms — names apart with `arb`
present or missing, the names one term with a second term (6:D17) — each
with an `s` part of total `r − k` on the two terms, `C(r − k + 3, 3)` ways,
summed over `k`; plus the one-term states asserting `ara` `K` times and
`asa` `L` times with `cost(K) + L = r`: `r + [r ≥ 2]` of them without `bra`
(`cost(0) = 2`, `cost(K) = K` for `K ≥ 1`), `r + [r ≥ 2] + [r ≥ 3]` with it.
Totals `1, 10, 47, 161, 462, 1 156, 2 599, 5 366, 10 338, …` without `bra` and
`1, 11, 55, 196, 569, 1 430, 3 216, 6 627, 12 727, …` with it: quartic (the
sixth's cubic forms convolved with a cubic), so the seed's 100 rounds would
hold about 7 · 10^11 results (699 218 633 465 without `bra`). Proof: the cost of each kind (D4) and the count of
`s` states on two named terms of a given total (compositions into four
parts). Computed: `two_term_rounds_equal_closed_form` true on all 8 rounds
of both ANCHORED two-term runs, and on 10 in `tests/test_eighth_explore.py`.
The shortest sequences to a two-term result with the names apart are the
arrangements of its cost-raising changes: the sixth's four `r` items and
the four `s` multiplicities, a multinomial coefficient
(`two_term_sequences_equal_multinomial` true on both runs; 6:D17's
multinomial with four more items).

**D12. The interaction of the two relations.** An assertion of one relation
leaves the other part exactly as it is (`proj_addAssertion_other`,
`proj_remove_other`); a term is added to both, and an identification merges
both, pair by pair (`proj_addTerm`, `proj_identify`); a rewriting rewrites
both (`proj_rename8`): `interaction`, `Step8.proj_self`. So the two relations
share their terms, their names and their writing, and nothing else: the
results are jointly free (D5), the cost is a sum (D4), the criterion reads
the `r` part's names — the `s` part's names are the same names — (D8), and
the count up to sameness is not a product (D10). A sequence of the eighth
projects to a sequence of the sixth on either part, no longer
(`Reach8.proj`).

**D13. What the second relation adds to what is given: nothing.** `s` begins
used by nothing (C2″), so the sixth's cost formula survives on the `r` part
unchanged and the `s` part costs its total — the seventh's cost. Adding
`asb` to what is given is a result one change away (`s_is_a_result`), and
no sequence of the sixth reaches its embedding (`results_grow`).

**D14. Statements holding in every result.** By D5 a statement holds in
every result exactly when it holds in every well-formed two-relation state
with a term; of the fifty statements tested (§6: the sixth's twenty-two on
each part, the six joint ones), exactly "at least one term" — the same
statement read on either part — holds everywhere (D6). Every other fails in
some result, "nothing in `s`" in round 1 (N1).

**D15. The unchosen reading of identification.** Under the reading in which
a merged multiplicity is the *larger* of the parts, per relation, the results
are the same (every well-formed state: D4(ii) identifies terms only in
states with nothing asserted), the reachability criterion is the same (D8's
sequence identifies terms only in states with nothing asserted at all), and
the cost is the same without `bra` (6:D19's argument on the `r` part; the
`s` part destroys nothing under either reading). With `bra` given the costs
differ on the `r` part exactly as 6:D19 says; the `s` part is unaffected. Not
in Lean; the proof is this paragraph.

## 5. What does not follow

Each item has two witnesses among the results, or a proof.

**N1. Anything about the asserting**, in either relation or jointly, other
than "at least one term": of the fifty statements tested every one but that
one holds in some result and fails in another in every run
(`statements_that_do_not_follow`, `follows_*.csv`). In particular, nothing
in `s` (fails in round 1: `arb asb`), nothing in `r` (holds in round 1:
remove `arb`), some pair asserted in both relations (holds in round 1: `arb
asb`), the two relations agreeing everywhere (holds in round 1), every `s`
assertion having its `r` twin and the converse.

**N2. `bra`; not `bra`; `asb`; not `asb`.** Both beginnings are results, and
so is `arb asb` (1:N1, 1:N2 through the embedding; D13).

**N3. That the `s` part determines anything about the `r` part, or the
converse.** For every well-formed `r` part every well-formed `s` part on the
same terms makes a result (D5): the pairs `arb | nothing`, `arb | asb`,
`nothing | asb`, `nothing | nothing` on the given terms are all results of
rounds 0, 1, 2, 1.

**N4. That a result is reached by one sequence only, or by finitely many;
that results of one round are reached by equally many shortest sequences.**
Every result is reached by infinitely many sequences (D9). What is given is
reached by one shortest sequence, `a b; arb asb` by one, `a b; arb asa asb`
by two, `a b; arb bra asb` by two (column `shortest_sequences_of_changes`).

**N5. That results of one round with equally many terms have equally many
changes.** `C(n, 2) + d_r + d_s + 1 + 2n²` depends on `d_r + d_s`: 10 for `a
b; nothing asserted` and 12 for `a b; arb asb`, both of round 1.

**N6. That a multiplicity never falls; that the number of terms, either
relation's total, the size, or the fewest classes of a split in either
relation never falls; that no `xrx` or no `xsx` stays asserted.** All refuted
by witnesses (`changes_lowering`, `tests/test_eighth_follows_invariants.py`).

**N7. That a state is contained in its outcome; that a sequence carries
every assertion somewhere.** Refuted, as 6:N14 through the embedding.

**N8. That reachability is one-way, or that two results can be
incomparable.** Refuted and derived respectively (D9).

**N9. That the number of results with `n` terms is the product of the
single-relation counts.** Refuted for `n ≥ 2` (D10, K1); holds for `n = 1`.

**N10. That the `s` relation costs anything but its total, or that its
assertions are ever destroyed.** Refuted (D4, `s_costs_its_total`): nothing
is given in `s`.

**Refuted** (each a proved impossibility): `a` and `b` one term to begin
with (R1, D1); an attempt that is refused or obstructed (R2, D3); telling `a`
and `b` apart again after identifying them, in either relation (R3, D2); a
sequence of changes to a result shorter than its cost (R4, D4); a well-formed
state with at least one term that is not a result, or a pair of well-formed
parts that is not (R5, D5); a change that keeps the cost, or the round, where
it was (R6, D4(v)); two results with the names apart that do not reach each
other, or two results with the same `r` part that do not (R7, D8, D9); an
`s` assertion of the given, or an `s` assertion destroyed along a shortest
sequence (R8, D4); a rewriting of one relation that is not a rewriting of the
other (R9, D7).

## 6. The exploration

**Protocol.** From each beginning, under each reading of sameness (four
combinations): round by round, every change on every result first reached in
the round before (C6), each result's changes fewest additions first —
identifications, removals in `r`, removals in `s`, a term, then every ordered
pair as an addition in `r`, then in `s` (`C(n, 2) + d_r + d_s + 1 + 2n²`
changes, every one performed). Each attempt records whether its outcome
asserts some `xrx`, and some `xsx`, while the state asserts none. Three
explorations per combination (C8′): the main run (4 terms under FREE, 3
under ANCHORED, 5 rounds), a deeper run (3 terms, 6 rounds), and the two-term
run (8 rounds). Beside every run the sixth derivation's exploration is made at
the same bound and rounds and compared on the results asserting nothing with
`s` (D5). Files per run (`evidence/eighth/`, tag
`bound{N}_rounds{R}_{reading}_{beginning}`): `results_*.csv` (one row per
result: terms, assertions counted, in `r`, in `s`, asserted, largest
multiplicity, additions to what is given, round, cost by formula, the
sixth's cost of the `r` part, destroyed givens, fewest classes in each
relation where no loop is asserted, changes, changes making some `xrx` /
`xsx` asserted, whether its changes were attempted, shortest sequences and
whether the count is exact, whether it reaches what is given, whether the
names are one term, whether nothing is asserted with `s`, whether nothing is
asserted twice, whether no `xrx` / `xsx` is asserted, the sixth's
shortest-sequence count where the result asserts nothing with `s`),
`added_*.csv`, `frontier_*.csv`, `rounds_*.csv`, `follows_*.csv`; per
combination `reach_bound2_rounds4_*.csv` and the full attempt log
`attempts_bound2_rounds3_*.jsonl`; `counts.csv`, `given.json`,
`summary.json` (every check, per run), `lean_axioms.txt`, `MANIFEST.sha256`.

**Results within the bound** (K1, K2). Every check of every run passes
(`summary.json`; `python code/generate_eighth.py` prints one line per run).

| run | results | by terms | asserting nothing with `s` (the sixth's) | names one term | shortest sequences (total) |
|---|---|---|---|---|---|
| FREE, no `bra`, 4 terms, 5 rounds | 8 109 | 19 / 1 157 / 4 714 / 2 219 | 707 | — | 374 776 |
| FREE, `bra`, 4 terms, 5 rounds | 7 639 | 22 / 1 099 / 4 524 / 1 994 | 889 | — | 501 469 |
| ANCHORED, no `bra`, 3 terms, 5 rounds | 10 404 | 19 / 1 818 / 8 567 | 1 128 | 332 | 322 607 |
| ANCHORED, `bra`, 3 terms, 5 rounds | 12 123 | 22 / 2 240 / 9 861 | 1 380 | 344 | 394 886 |
| FREE, no `bra`, 3 terms, 6 rounds | 22 435 | 26 / 2 603 / 19 806 | 1 033 | — | 4 432 048 |
| FREE, `bra`, 3 terms, 6 rounds | 23 171 | 30 / 2 591 / 20 550 | 1 353 | — | 6 400 607 |
| ANCHORED, no `bra`, 3 terms, 6 rounds | 44 843 | 26 / 4 410 / 40 407 | 3 001 | 1 414 | 5 414 549 |
| ANCHORED, `bra`, 3 terms, 6 rounds | 52 849 | 30 / 5 448 / 47 371 | 3 703 | 1 464 | 6 716 869 |
| FREE, no `bra`, 2 terms, 8 rounds | 10 581 | 43 / 10 538 | 364 | — | 26 391 461 |
| FREE, `bra`, 2 terms, 8 rounds | 11 049 | 49 / 11 000 | 410 | — | 41 716 153 |
| ANCHORED, no `bra`, 2 terms, 8 rounds | 20 140 | 43 / 20 097 | 890 | 3 838 | 32 957 137 |
| ANCHORED, `bra`, 2 terms, 8 rounds | 24 832 | 49 / 24 783 | 1 074 | 4 174 | 43 981 539 |

In every run the results asserting nothing with `s`, with their rounds and
their shortest-sequence counts, are exactly the sixth derivation's
exploration's at the same bound and rounds (6:K1, 6:K2, 6:K7 computed again).
Every count by terms, total multiplicity and destroyed givens equals the
independent count (`explored_equals_independent_count`, D10), and every
result's round is its cost (D4).

**Rounds** (K2). ANCHORED, no `bra`, 3 terms
(`rounds_bound3_rounds5_anchored_without_bra.csv`): new results per round
1, 11, 66, 350, 1 766, 8 210; of which asserting nothing with `s` 1, 7, 26,
86, 266, 742 (the sixth's); with the names one term 0, 1, 4, 14, 59, 254;
without any bound on terms 1, 11, 67, 372, 2 096, 11 949 (`layer_counts`;
rounds 0–1 agree with the run, as every round up to `N − 2` must). FREE, no
`bra`, 4 terms: 1, 11, 57, 276, 1 324, 6 440 against 1, 11, 57, 277, 1 345,
6 701 without bound. With two terms, names kept: 1, 10, 47, 161, 462, 1 156,
2 599, 5 366, 10 338 (D11). Every round of every run has a new result.

**Attempts** (K3). 46 926 changes attempted in the ANCHORED 3-term run,
4 994 of them making some `xrx` asserted and 4 492 some `xsx` asserted on a
result asserting none in that relation (the sixth's function on each part,
D3); 11 in round 1 (identify `a` and `b`; remove `arb`; a term; the four
`r` additions; the four `s` additions), of which 3 make some `xrx` and 2
some `xsx` asserted. The totals equal `C(n, 2) + d_r + d_s + 1 + 2n²` summed
over the results whose changes were attempted, in every run. Of the 45 413
changes within the bound of that run, 36 482 raise the round by one and
8 931 lower it; none keeps it (D4(v)). 60 680 changes attempted in the census
without `bra`, 70 049 with it.

**Frontier** (K5). Every result with `N` terms whose changes were attempted
has one entry (the term): 1 513 in the ANCHORED 3-term run, 240 in the FREE
4-term run. The second part, the results of round 5 whose changes await:
8 210 results with 199 055 changes (ANCHORED, 3 terms), 6 440 with 192 233
(FREE, 4 terms); 10 338 results after round 8 with two terms (148 990
changes).

**Statements** (K7; `follows_*.csv`). Fifty statements tested with the names
kept (forty without): the sixth's twenty-two on each part — with the wording
rewritten for `s` — and six joint ones; "at least one term" (on either part)
holds everywhere and is proved (D6); every other fails somewhere (N1).

**Reachability within 2 terms and 4 rounds** (K8;
`reach_bound2_rounds4_*.csv`, `summary.json` `reachability`), along the
changes among the results of 2 terms and 7 rounds:

| reading, beginning | results (names one term) | ordered pairs | reachable | unordered pairs both ways | pairs with the same `r` part, all both ways |
|---|---|---|---|---|---|
| ANCHORED, no `bra` | 681 (66) | 463 761 | 423 171 | 190 950 | 14 366 |
| ANCHORED, `bra` | 832 (69) | 692 224 | 639 577 | 293 049 | 16 558 |
| FREE, no `bra` | 472 (—) | 222 784 | 222 784 | 111 156 | 11 318 |
| FREE, `bra` | 433 (—) | 187 489 | 187 489 | 93 528 | 7 280 |

The criterion agrees with the search on every pair; the unreachable pairs are
exactly those from a result with the names one term to one with them apart
(66 × 615 = 40 590; 69 × 763 = 52 647); every pair of results with the same
`r` part is reachable both ways.

**Census** (ANCHORED, 4 terms, 5 rounds, counts only): 14 113 results (19 /
1 818 / 8 567 / 3 709 by terms) without `bra`, 16 139 with it; 60 680 and
70 049 changes attempted; the sixth's 1 728 and 2 065 results are the
results asserting nothing with `s` in both, at the same rounds with the same
shortest-sequence counts; every check passes.

**Independent counts** (K1; `counts.csv`): all well-formed two-relation
states with `n ≤ 4` terms by total multiplicity `0 … 8`, under any rewriting
and with the names kept by kind, beside the sixth's single-relation counts
and their product: 45, 6 470, 261 318, 3 231 489 results for `n = 1 … 4` under
any rewriting, against products 45, 3 830, 61 912, 308 245 (equal for `n = 1`,
larger from `n = 2` on: 20 against 16 with two terms and total 2); with the
names kept, by how the named terms stand, 45, 25 740, 2 344 342, 51 375 246.

**What is given** (`given.json`): the two beginnings, their 11 or 12 changes
(7 or 8 in `r`, 4 in `s`), all performed, 3 (or 4) making some `xrx`
asserted and 2 making some `xsx` asserted; identifying `a` and `b` gives
`a (a and b are one term); ara` (cost 1); adding `asb` or `asa` costs 1; each
beginning reaches the other, the one-term states and the beginning with
`asb` instead, and is reached back from all but the one-term states.

**Reproducibility** (K9, K10). `python code/generate_eighth.py` rewrites
every computed file of `evidence/eighth/` (about seventeen minutes here, 37 MB);
`--check` regenerates into a temporary folder and compares byte for byte
(matched); `MANIFEST.sha256` lists every file's hash. `python
code/lean_report_eighth.py` builds all eight Lean libraries and rewrites
`evidence/eighth/lean_axioms.txt` (140 theorems, every one within
`propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit` or declared
axiom in `lean4/`). After this work the seven earlier derivations' `--check`
and Lean reports were re-run (`paper/eighth/change_log.md`, item 13). Tests:
623 passed, eight derivations; line coverage 100.00 %, branch
coverage 99.73 % of all of `code/`, every evidence module fully covered
(`python code/xry/gate.py coverage.json`); `mypy --strict` clean; the prose
watchlist clean, with every pinned hit of this paper in §10.

## 7. What survives the second relation

The task asks whether the results, the reachability criterion, the cost, and
separability hold per relation, jointly, or not, and how the two relations
interact. In one line each, with the Lean statements of `Eighth/Compare.lean`:

- **The results: jointly free.** Every result of the sixth seed is a result
  of the eighth asserting nothing with `s` at the same round (`results_ofR_A`,
  `_B`); the results asserting nothing with `s` are exactly the sixth's
  (`results_r_iff`); the eighth has results the sixth has not
  (`results_grow`); both parts of every result are sixth results
  (`proj_results`), and any two such parts on the same terms make a result
  (`results_pair`). Per relation: the sixth's set, twice. Jointly: the product
  of the two sets — but not the product of the two counts (D10).
- **The reachability criterion: on the `r` part, hence jointly.** The names
  decide, and the names belong to the terms, not to a relation; so
  reachability of two-relation states is reachability of their `r` parts
  under the sixth seed (`criterion_survives`, `reach8_iff_r`), the `s` parts
  imposing nothing (`same_r_part_mutual`). Per relation the criterion holds
  for the `r` part as the sixth's; for the `s` part it holds vacuously
  ("always", since its names are the `r` part's).
- **The cost: per relation, and additive.** The fewest changes to a result
  is the sixth's fewest changes to its `r` part plus its `s` total
  (`cost_survives`, `costA8_eq`, `fewest_changes8_A`); on the results
  asserting nothing with `s` it is the sixth's as it stands
  (`fewest_changes8_of_r_A`), and a state whose `r` part is what is given
  costs exactly its `s` total (`s_costs_its_total`) — the seventh's cost on
  the `s` relation. Parity survives; the sixth's cost-raising rule survives
  on the `r` part, and every `s` addition raises the cost.
- **Separability: of the terms, shared.** Telling `a` and `b` apart is
  possible exactly when the names are two terms, in both relations at once;
  the merge is one change on both parts (`proj_identify`) and irreversible
  for both (`Reach8.names_stay_merged`). Read as the fewest classes of a
  split, separability is per relation (a function of each part) and can
  fall in either (N6).
- **The interaction: through the terms and the names only.** An assertion of
  one relation leaves the other part as it is; a term and an identification
  act on both; a rewriting rewrites both (`interaction`, `Step8.proj_self`,
  D12). `s` is an independent copy of `r`'s structure in every respect —
  results, criterion, cost shape, rewriting — except that it shares the terms
  (so the count up to sameness is not a product) and carries no given (so its
  cost is the seventh's, not the sixth's).

## 8. Alternatives: kept, or eliminated by proof

| Alternative | Kept / eliminated |
|---|---|
| `bra` asserted to begin with / not | both kept: computed under both; N2 |
| something asserted with `s` to begin with | kept as alternatives that add no result (C2″, D5); their cost formula is proved in the paper, not computed (O4) |
| other beginnings (`bra` `k ≥ 2` times, more terms, some loop) | eliminated as starting points by D5 (results of the chosen beginning, with the same results); not computed separately |
| FREE / ANCHORED sameness | both kept: every file exists under both |
| identification: multiplicities add up / the larger of the two, per relation | the first chosen and computed; the second kept as an alternative with the same results and reachability and, with `bra` given, a different cost on the `r` part (D15, 6:D19) |
| the other orders of attempts (relations, kinds) | not computed; same results and rounds (D4) |
| a bound on terms alone | eliminated: the results within it are infinite (D5) |
| every well-formed two-relation state within the bound, up to sameness | kept; none dropped (D10) |

Earlier results that change shape under the eighth seed, each with the
reason: 6:D3 (changes per result) — the count gains `d_s + n²`, the loop
characterisation holds per relation, D3; 6:D8 (the cost) — survives on the
`r` part and gains the `s` total, D4; 6:D9 (the results) — extends to every
well-formed two-relation state, the sixth's being those with nothing in `s`,
D5; 6:D12 (the criterion) — survives as a statement about the `r` part's
names, D8; 6:D14 (the independent count) — every cycle gains an `s` factor,
D10; 6:D17 (the two-term forms) — convolved with the `s` states, D11; 6:D19
(the two readings of identification) — survives on the `r` part, D15; 6:N3's
one everywhere-true statement — survives on either part, D14; 7:D4 (the cost
as the size, additions only) — survives for the `s` part: it costs its
total by additions, D4; 4:D8's size difference on states containing what is
given — survives with both totals counted (a corollary of D4 with `lost =
0`); every K-claim of the sixth — computed again on the results asserting
nothing with `s` (§6). The sixth's `has_two_way`, `lost`, `lost_free`,
`merged_optimal`, `raises_by_one`, `cost`, `reachable`, the statements tested
and the orbit helpers are imported and applied to a part (`change_log.md`,
item 3): they survive per relation. Everything else cited stands with the
re-check given at its citation.

## 9. Open

- O1. A closed form for the number of shortest sequences reaching a result
  with three or more terms, or with the names one term: computed per result
  within the bound (K7); with two terms and the names apart it is the
  multinomial of D11.
- O2. Results beyond the declared bounds, listed: the frontier is exported
  (both parts); the census counts at 4 terms; the seed's 100 rounds with two
  terms are given in closed form (D11), not listed.
- O3. Lean statements of D3, of D4(iv), of the exactness of the
  shortest-sequence counts (D10), of D11, of D15 and of the non-product
  count (D10): proved in the paper and checked by computation.
- O4. The cost from a beginning asserting something with `s`: the formula
  of C2″, proved in the paper, not computed.
- O5. The earlier papers' O1 (multiplicity) stays closed by the fourth seed;
  their O2 (the number of new results beyond the bound) is given by the
  series and the cost formula for any round (D10, `layer_counts`) and not
  listed.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Two-coloured (arc-labelled) directed multigraphs with loops under vertex
  identification and arc insertion and deletion**, the marks `a`, `b` on two
  vertices and one `r`-arc given. D5 is that the edit graph on such marked
  two-coloured multidigraphs is connected except for the one-way merge of
  the two marks, and that the colour classes are independent as sets: any
  `r`-graph and any `s`-graph on the same vertex set combine. D8 and D9 are
  that its strong components are the sixth's two (marks apart, marks merged)
  under ANCHORED and one under FREE, whatever the `s`-arcs.
- **Graph edit distance with two arc colours** (Sanfeliu and Fu, 1983, with
  contraction allowed and colours kept apart). D4 is a closed form: the edit
  distance from the marked two-vertex graph `arb` to any marked two-coloured
  multidigraph with loops is the sixth's distance for the `r`-colour plus
  the number of `s`-arcs — the potential-function argument with the second
  colour contributing its arc count and no marks to destroy.
- **Pólya enumeration of two-coloured multigraphs.** The independent count
  (D10) is the cycle-index computation of the sixth derivation with two
  figure series per cycle, `1 / (1 − x^L)` twice; the departure of the
  count from the product of the single-colour counts is the familiar fact
  that the cycle index of a group acting on a product of two sets is not the
  product of the cycle indices. With two vertices (D11) the count is a
  convolution of the sixth's compositions with `C(t + 3, 3)`.
- **Structures with two binary relations on a common carrier.** That the
  second relation carries no given and costs its arc count by insertions
  alone (D4, D13) is the seventh derivation's "everything from nothing" for
  one relation, embedded beside the sixth's marked relation.

What appears to be specific to this seed: that the second relation changes
nothing about the first — the sixth's results, criterion, cost and counts are
recovered exactly on the `r` part through two definitional maps
(`Eighth/Compare.lean`) — and that the *only* place the two relations touch
is the shared terms and names, which is enough to make the set of results a
product, the cost a sum, and the count up to sameness neither (8 against 4
with two terms and one assertion in each relation).
