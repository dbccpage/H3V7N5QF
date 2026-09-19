# What follows from `arb` once, counted assertions, four kinds of change, and nothing forbidden

Sixth derivation. Input: `prompt/sixth/seed_prompt.md`. Task:
`prompt/sixth/prompt.md`. Claim IDs refer to `paper/sixth/claim_ledger.md`;
an ID written `1:D8` refers to the first derivation's ledger
(`paper/claim_ledger.md`, paper `paper/paper.md`), `2:D8` to the second's
(`paper/second/`), `3:D8` to the third's, `4:D8` to the fourth's, `5:D8` to
the fifth's (`paper/fifth/`). Lean names in the namespace `Seed.Sixth` are in
`lean4/Sixth/`; names in `Seed.Fifth`, `Seed.Fourth`, `Seed.Third`,
`Seed.Second`, `Seed` are the earlier derivations' (`lean4/Fifth/`,
`lean4/Fourth/`, `lean4/Third/`, `lean4/Second/`, `lean4/H3V7N5QF/`). Where a
short name exists in two libraries the sixth's is meant unless the namespace
is written. The axiom report for every theorem cited here, of any of the six
libraries, is `evidence/sixth/lean_axioms.txt`. Computed files are in
`evidence/sixth/`, written by `python code/generate_sixth.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; the unchosen
readings are listed), **derived** (proved), **computed** (output of `code/`),
**refuted** (proved impossible), **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the sixth seed, and the re-check says whether the result *survives once
`xrx` is allowed*. The re-check is one of five kinds. *(no change)*: the
statement mentions neither legality nor a change, so it stands as it is.
*(through the embedding)*: every performed change of the fifth seed is a
change of the sixth (`Step5.toStep6`, `Reach5.toReach6`), every *attempt* of
the fifth is a change of the sixth (`Try5.toStep6`), and a change of the sixth
between states asserting no `xrx` is a change of the fifth (`Step6.toStep5`);
so what the fifth proved for a particular sequence of its changes holds for
that sequence here, and what it proved *from* legality must be looked at on
the changes legality barred — where it is either re-proved or refuted by a
witness. *(on legal states)*: the earlier statement holds for the states
asserting no `xrx` and is used only there. *(re-proved)*: the earlier proof
used legality, and a statement covering all well-formed states is proved
afresh. *(computed again)*: a computed statement of the fifth derivation is
re-run beside the sixth exploration and compared on the results asserting no
`xrx`. Results of the earlier derivations that fail under the sixth seed are
listed in §8.

## 0. Findings in brief

1. The sixth seed is the fifth (counted assertions, four kinds of change)
   without "for no term `x` may `xrx` be asserted" and without the paragraph
   on obstruction, answers and refusal (given, §1). The state is the fifth's;
   a state asserting some `xrx` is a state like any other. **Nothing is
   obstructed**: the attempts of the fifth seed are exactly the changes of
   the sixth (D3, `try5_iff_step6`); nothing is answered, refused or built.
2. `a` and `b` are two terms to begin with, and they can be made one term in
   a single change: identifying them in what is given gives `a (a and b are
   one term); ara` — the given assertion survives the merge as `ara` (D1,
   D2). **Legality is not kept**: `a b; arb ara` is a result one change away
   (D6), and once the names are one term `arb` — now `ara` — *can* be
   asserted, so the fifth's "`arb` gone for good" fails (D7).
3. **The results extend to every well-formed state with at least one term**,
   its names anywhere (D9). The fifth's results are exactly the results
   asserting no `xrx`, at the same rounds (computed again on every run).
4. **The reachability criterion survives**: a result reaches another exactly
   when the names, if one term at the start, are one term at the end (names
   kept); always (any rewriting) (D12) — re-proved without legality. So do
   mutual reachability within the two classes, comparability, and the
   two-change cycle (D13).
5. **The cost survives on every result with the names apart and on every
   result asserting no `xrx`, and changes elsewhere.** The fewest changes to
   a result is `size − size(given) + 2·lost`, where `lost` counts the missing
   givens when the names are apart (as before) and `m0 + 1 − min(M(c,c), m0)`
   when they are one term `c` — the merge, plus the givens the merge did not
   carry into `crc` (D8). The fifth's `m0 + 1` fails: identifying `a` and `b`
   in what is given is one change where the fifth's potential rises by three.
   The size difference survives on results containing what is given; parity
   survives; every change moves the cost by an odd amount.
6. **The obstruction and answer notions do not survive as notions.** What
   survives is the *characterisation*: on a state asserting no `xrx`, a
   change makes some `xrx` asserted exactly when it adds some `xrx` or
   identifies two related terms (D3), now a fact about the outcome. The
   fifth's answer "remove the obstruction" (lower the assertions between the
   two terms, then identify) is still a sequence of changes, but it and the
   direct identification reach two *different* results (D5); the fifth's
   "removing first or last gives the same state" fails without legality.
7. A result with `n` terms and `d` asserted pairs (diagonal included) has
   `C(n, 2) + d + 1 + n²` changes, none obstructed; on a result asserting no
   `xrx`, `n` plus the number of related pairs of them make some `xrx`
   asserted — the fifth's obstructed count, recovered exactly (D3, K3).
8. Within the bound (terms and rounds) the exploration is complete, certified
   by an independent count with the diagonal pairs among the cycles of the
   rewriting (D14); the frontier is one entry per result at the bound; with
   the given terms only the results of round `r` grow as `r³` (D17), so the
   seed's 100 rounds do not complete and 20 are run, the closed form being
   proved for every round. Everything claimed as derived is in Lean, the
   every-writing statements included (target 5 of the plan closed on the
   single attempt); proved in the paper and checked by computation only: the
   within-bound completeness (D14), which changes raise the cost by exactly
   one (D8(iv)), the exactness of the shortest-sequence counts (D14), the
   two-term closed forms (D17), and the fate of the unchosen reading of
   identification (D19).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2‴ | An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G3′ | `arb` is asserted with multiplicity one. |
| G5 | Whether `bra` is asserted is not given. |
| G6 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G11 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, prove what is complete within it. |
| G14 | Any outcome is valid. |

The fifth seed's G4 ("for no term `x` may `xrx` be asserted") and G8–G10
(obstruction, answers, refusal) are gone; nothing is added (`diff`;
`research/sixth/reading_the_seed.md`). Every sentence above is the fifth
seed's word for word.

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry`, multiplicity | given (G1, G2‴) | |
| adding raises a multiplicity by one; removing lowers it by one | given (G2‴) | |
| asserted = multiplicity at least one; the counted state | chosen (4:C1′, no change) | the fourth's model, unchanged |
| an assertion has a first and a second term; `xrx` is an assertion | derived (1:§2), given (G2‴: `x`, `y` any terms) | |
| "legal" (no `xrx` asserted) | chosen name for a property (the fifth's condition) | no longer a condition on results; tested as a statement (N3) |
| `a`, `b` are two terms to begin with | derived (D1) | not kept (D2, D7) |
| what is given: the terms `a`, `b`; `arb` once; `bra` once or not at all | given (G3′), chosen (C2′) | unchosen: other beginnings; harmless (D9) |
| supply of letters not capped | chosen (C3) | harmless |
| `r` does not write a term | chosen (C9) | writing only |
| change, four kinds; what identifying does | given (G6, G7) | |
| the multiplicities of the pairs an identification merges add up (`urv`, `vru`, `uru`, `vrv` all become `uru`) | chosen (C5‴) | unchosen: the larger of the two; same results and reachability, different cost with `bra` given (D19) |
| removing what is not asserted, identifying a term with itself: not changes; adding what is asserted is a change | chosen (C5‴) | |
| the order of the changes of a result | chosen (C6) | identifications and removals, a term, the assertions |
| obstruction, answer, refusal, build | — (not in the seed) | the fifth's notions, empty here (D3, D5, §7); the characterisation of the fifth's obstructed attempts survives as a fact about outcomes |
| destroyed given, cost | derived (D8) | the fifth's formula with the names-one-term case changed |
| result | chosen (C6) | a counted state up to sameness |
| the results, as a set | derived (D9) | every well-formed state with at least one term; the fifth's are those asserting no `xrx` |
| sameness | given (G12) | two readings, both kept: chosen (C4) |
| terms and assertions added to what is given | given (G11) | counted with multiplicity; may be negative |
| round; what counts as one change | chosen (C6) | the round of a result is its cost (D8) |
| bound, frontier | given (G13) | bound on terms and on rounds: chosen (C8′) |
| shortest sequences reaching a result; sequences of every length | computed (K7); derived (D13, D14) | exact within the bound where D14 says; infinitely many sequences in all |
| reachability between results | derived (D12) | the names decide; mutual within classes (D13) |
| parity of the cost | derived (D8) | every change moves it by an odd amount |
| counts of results by terms, total multiplicity, destroyed givens | computed (K1) | by series, the diagonal pairs among the cycles |
| what survives `xrx` being allowed | derived (§7; `Sixth/Compare.lean`) | see §8 for what does not |

## 3. Readings that had to be chosen

C3, C4, C6, C9 are the earlier derivations', unchanged; C2′, C8′ are the
fourth's and fifth's; C5‴ is the fifth's C5″ with the identification of
related terms now performed. The fifth's C7 (obstruction and answers) has
nothing to read: the seed no longer mentions them.

**C2′. To begin with: the terms `a` and `b`; `arb` once; `bra` once or not
at all.** As 5:C2′. Harmless: every well-formed state is a result of either
beginning (D9), so any other beginning is a result of the chosen one and has
the same results.

**C3. No cap on the number of terms.** The sequences used in the proofs of
D8 and D9 never have more terms than `max(2, terms of the target)`; the
sequence of D12 between two results uses two fresh terms to move the names,
so at most `max(terms) + 2`; as 5:C3.

**C4. Sameness, two readings, both kept.** FREE and ANCHORED as 1:C4 on
counted states (4:C4, 5:C4); a state asserting some `xrx` has the same
rewritings.

**C5‴. What is a change.** Adding an assertion that is asserted already is a
change (it raises the multiplicity, 4:C5′), and so is adding `xrx`, for any
term `x`: the seed says `xry` "where `x` and `y` are terms" and forbids
nothing. Removing an assertion that is not asserted, and identifying a term
with itself, change nothing and are not changes (5:C5″). **Identification
with multiplicities.** "Replaces both by one term in every assertion": each
time an assertion is asserted its terms are replaced, so the pairs that
become one pair have their times added up — now including `urv`, `vru`,
`uru` and `vrv`, which all become `uru` (`code/fifth/state.py` `identify`,
imported; Lean `MSt.identify`, the fifth's). Unchosen: another combination,
for instance the larger of the two. The two readings give the same results
and the same reachability, and the same cost without `bra`; with `bra` given
they differ in cost (D19), so the unchosen reading is kept as an alternative
whose cost is not computed here (O6).

**C6. Results and rounds.** As 5:C6 with nothing refused: a result is a
counted state up to sameness; round `k` attempts — performs — every change on
every result first reached in round `k − 1`; every change counts one.
Fewest additions first: identifications and removals add nothing, then a
term, then the assertions. Unchosen: other orders; the order cannot move a
result to another round (D8: the round of a result is its cost).

**C8′. Bound on terms and on rounds.** As 4:C8′, 5:C8′: within any bound on
terms the results are infinite, so every exploration is bounded in terms and
in rounds: 5 terms (FREE) or 4 terms (ANCHORED) with 8 rounds; 3 terms with
9 rounds; 2 terms with 20 rounds. Under ANCHORED a counts-only census at 5
terms with 8 rounds. Full attempt logs at 2 terms and 3 rounds; reachability
among the results of 3 terms and 4 rounds, along the changes among the
results of 3 terms and 7 rounds (enough for every sequence the proof of D12
uses, §4). A result now has `n²` pairs to assert instead of `n² − n`, so the
results per round grow faster than under the fifth seed (about four times as
many at 4 terms and 8 rounds); the bounds were first set higher (3 terms
with 10 rounds, 2 terms with 30) and lowered for the size of the evidence,
not for time (`change_log.md`, item 10). The seed's 100 rounds with the given
terms only would hold about four million results (D17) and are not run.

**C9.** `r` writes assertions, not terms.

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. `a` and `b` are two terms to begin with, and not for good.** In a
state asserting no `xrx` with `arb` asserted, `a ≠ b`
(`Seed.Fourth.names_apart_of_legal`, 4:D1, 1:D1; on legal states — the
statement's hypothesis is legality). What is given is such a state. But one
change makes them one term: identifying `a` and `b` gives `a (a and b are
one term); ara` (`step_identify_given`, `identify_given_ara`: the outcome
asserts `ara` at least `M(a,b) + M(b,a)` times, `identify_M_ge_pair`). With
`xrx` allowed, `a = b` with `arb` asserted is a result (`arb_gone_fails`).

**D2. The beginnings.** On the given terms alone, exactly two states
asserting nothing twice and no `xrx` contain what is given
(`two_states_on_given_terms`, 1:D2, on legal states); with `xrx` allowed the
states on the given terms are infinite and all are results (D9). Each
beginning is one change from the other in both directions
(`no_return_fails6`; 5:D2 through the embedding). The one-term state
asserting nothing is two changes away without `bra` and three with it
(5:D2's `givenA4_to_oneTerm4`, `givenB4_to_oneTerm4` through the embedding);
the one-term state asserting `ara` once (`loopState 1`) is *one* change away
without `bra` (`step_identify_givenA4`, `identify_givenA4_eq`), and with `bra`
given one change reaches `ara` twice (`identify_givenB4_eq`).

**D3. Nothing is obstructed; which changes make some `xrx` asserted; how
many changes a result has.** Every attempt of the fifth seed (`Try5`, the
four kinds without the conditions that made them unobstructed) is a change
of the sixth and conversely: `Try5.toStep6`, `Step6.toTry5`,
`try5_iff_step6`. On a state asserting no `xrx`, a change leaves a state
asserting some `xrx` exactly when it adds some `xrx` or identifies two
related terms: `Step6.not_legal_iff` (the fifth's `Try5.obstructed_iff`,
5:D3, through the embedding — the same statement, now about the outcome
only); a change of the sixth between two states asserting no `xrx` is a
change of the fifth (`Step6.toStep5`). So a result with `n` terms and `d`
asserted pairs, diagonal pairs included, has `C(n, 2) + d + 1 + n²` changes,
every one performed, of which on a result asserting no `xrx` the `n`
additions of some `xrx` and the identifications of related pairs make some
`xrx` asserted (computed: `attempts_equal_formula`,
`xrx_making_equal_formula` true in every run; on the fifth's results the
count is the fifth's obstructed count, K3).

**D4. Adding `xrx` is performed in every state.** `xrx_is_a_result`: `ara`
added to what is given is a result one change away. 5:D4 ("adding `xrx` is
obstructed in every state") does not survive; what survives of it is that
the outcome asserts some `xrx` (`Seed.Fourth.adding_xrx_always_obstructed4`,
no change: a statement about the outcome).

**D5. The fifth's answers are sequences to other results.** The fifth's
answer "remove the obstruction" to identifying `a` and `b` in what is given
with `bra` — remove `arb`, remove `bra`, identify: the one-term state
asserting nothing — and the direct identification — the one-term state
asserting `ara` twice — are two sequences of changes to two different
results (`remove_answer_differs`; 5:D5's `remove_answer5` through the
embedding, now one sequence among others). The fifth's "removing first, or
identifying first and then lowering the resulting `uru` to zero, gives the
same state" (`remove_obstruction_first_or_last5`, 5:D5) does not survive
without its legality hypothesis: with `uru` asserted before the
identification the second path also destroys it (`first_or_last_fails`,
witness `a b; ara arb`). The fifth's persistence of an obstruction
(`obstruction_persists5`) survives as a statement about multiplicities
(through the embedding) and obstructs nothing.

**D6. What every result has.** Every result is well formed, has at least
one term, and is finite (`Reach6.wf`, `Reach6.nonempty`; 5:D6 re-proved
without legality). Legality is not kept (`legal_not_kept`); nothing else is
kept either (N13–N15).

**D7. The one irreversible change (ANCHORED).** Once `a` and `b` are one
term they are one term after every sequence of changes:
`Step6.names_stay_merged`, `Reach6.names_stay_merged` (1:D7, 5:D7 re-proved:
the proof mentions no legality). From the one-term states what is given is
never reached (`merged_never_apart6`, `loopState_never_apart`). **`arb` is
not gone for good**: after the merge `arb` is `ara`, and it is asserted in
the outcome of identifying what is given (`arb_gone_fails`); 5:D7's
`Reach5.arb_gone_for_good` does not survive. Under FREE every result reaches
every result (D12).

**D8. Fewest changes (cost).** Let what is given have `m0` assertions (`1`
without `bra`, `2` with), so size `2 + m0` with size = terms + the sum of the
multiplicities. For a well-formed state `G` with names let `lost(G)` be the
number of given assertions with multiplicity zero between the terms named
`a` and `b` if these are two terms, and `m0 + 1 − min(M(c,c), m0)` if they
are one term `c` (Lean `lostA6`, `lostB6`). Then the fewest changes from what
is given to `G` is

    size(G) − (2 + m0) + 2 · lost(G)

— the first and fifth derivations' formula with the names-one-term case
changed. *(i) Lower bound.* `size + 2·lost` (Lean `costA6`, `costB6`) rises
by at most one per change (`Step6.costA_le`, `Step6.costB_le`): adding a
term or an assertion — `xrx` included — raises the size by one and destroys
nothing (`addAssertion_contains`, the fourth's containment without `x ≠ y`;
`lostA6_le_of_contains`); a removal lowers the size by one and destroys at
most one given, since it lowers one multiplicity by one (`lostA6_remove`,
`lostB6_remove`; with the names one term, `min(M(c,c), m0)` falls by at most
one); an identification lowers the size by exactly one (`Seed.Fifth.
size_identify`, 5:D8 through the embedding: the total is kept) and destroys
at most one given (`lostA6_identify`, `lostB6_identify`): with the names
apart before and after, every multiplicity is carried to one at least as
large (`identify_M_ge`, 5:D8, no change); with them one term before, `crc`
can only rise; and when the identification merges `a` and `b` — the case the
fifth seed barred unless nothing was asserted between them — the outcome
asserts `crc` at least `M(a,b) + M(b,a)` times (`identify_M_ge_pair`, new),
so `min(M'(c,c), m0)` is at least the number of givens that were present and
`lost` rises by at most one. So a result reached in `n` changes has `cost ≤
n + cost(given)`: `Reach6.costA_le`, `fewest_changes6_lower_A`, `_B`. *(ii)
Upper bound.* Names apart: remove the given assertions `G` lacks, then the
additions (`reach6_of_contains`, the fourth's `reach4_of_contains` re-proved
without its legality hypothesis — `reach6_addTerms`, `reach6_raise`,
`reach6_by_additions`, with `xrx` raised like any pair):
`fewest_changes6_upper_A_apart`, `_B_apart` (the fifth's removal paths
`step_remove_arb`, `removed_arb_contains`, the four `givenB4_remove_…`
containments, through the embedding). Names one term: let `k = min(M_G(c,c),
m0)`; remove `m0 − k` of the givens, identify `a` and `b` — the one-term
state asserting `0r0` `k` times (`loopState k`; `identify_givenA4_eq`,
`identify_givenB4_eq`, `givenB4_to_loopState_one`; for `k = 0` the fifth's
`givenA4_to_oneTerm4`, `givenB4_to_oneTerm4`) — then the additions
(`loopState_contains`): `fewest_changes6_upper_A_merged`, `_B_merged`;
together `fewest_changes6_A`, `fewest_changes6_B`. *(iii) Every writing.*
Changes commute with one-to-one rewriting (D11) and the cost is the same in
every writing (`costA6_rename`, `costB6_rename`), so the fewest changes to a
result is the cost of any of its writings: `fewest_changes6_every_writing_A`,
`_B` (target 5 of the plan closed). *Under FREE* the names may be placed
anywhere and `lost` is the least of two closed forms: the names apart
(`lost_apart_free`, the first's: with `m0 = 1`, `0` if some `xry` with `x ≠
y` is asserted and `1` otherwise; with `m0 = 2`, `0` if some pair is asserted
both ways, `1` if some `xry` with `x ≠ y`, `2` otherwise) and the names on
the term with the largest `xrx` multiplicity (`lost_merged_free`, `m0 + 1 −
min(max_c M(c,c), m0)`); computed: the closed form equals the best placement
on every state with at most 3 terms and no multiplicity above 2 (6 918
states, `free_cost_closed_form_mismatches` empty), and the round of every
explored result equals the formula in all twelve runs and both census runs
(`round_equals_cost_formula_for_every_result`). *(iv) Which changes raise the
cost by exactly one.* Along a shortest sequence every change raises the cost
by exactly one; by (i) these are: adding a term; adding an assertion unless it
restores a given (names apart) or is `crc` with `crc` asserted fewer than
`m0` times (names one term); removing a given asserted once (names apart) or
`crc` asserted at most `m0` times (names one term); identifying `a` with `b`
when `min(S, m0) = p`, where `S = M(a,b) + M(b,a) + M(a,a) + M(b,b)` is what
`crc` will be asserted and `p` the number of givens present. Every other
change lowers the cost by one, three or five. Proof from (i): the size moves
by exactly one, up for an addition and down otherwise (`Step6.size_step`);
`lost` moves as computed in (i); the identification of `a` with `b` raises
it by `1 + p − min(S, m0)`, so the cost moves by `1 + 2·(p − min(S, m0))`:
exactly one when `min(S, m0) = p`, and otherwise down by one or three.
Computed (`code/sixth/cost.py` `raises_by_one`): the rule agrees with the
outcome on every change within the bound of every run with names
(`cost_rule_disagreements` empty; 451 157 changes in the ANCHORED 4-term
run). *(v) Parity.* Every change moves the size by one and the destroyed
givens enter the cost twice, so every change moves the cost by an odd
amount; the size and the length of a sequence have a fixed parity
(`Reach6.size_parity`, 5:D8(v) re-proved): no change keeps the round
(computed: `changes_keeping_the_round: 0` in every run). **What survives.**
On a state asserting no `xrx` the destroyed givens are the fifth's
(`lostA6_eq_lostA5_of_legal`), so the fifth's fewest changes survive there
(`fewest_changes6_of_legal_A`, `_B`); with the names apart they survive, `xrx`
or not (`lostA6_eq_lostA5_of_ne`, `fewest_changes6_apart_A`); on a state
containing what is given the fewest changes is the size difference, the
fourth's (`fewest_changes6_of_contains_A`, `_B`). **What fails.** With the
names one term and `crc` asserted the fifth's potential is no lower bound:
identifying `a` and `b` in what is given is one change to a state whose
fifth-seed cost is 6, three more than what is given, and whose sixth-seed
cost is 4, one more (`fifth_potential_fails`); the one-term state asserting
`ara` `k ≥ 1` times is `k` changes away (`cost_loopState`), not the fifth's
`k + 2`. Computed: in the ANCHORED 4-term run the fifth's destroyed givens
differ from these on 2 143 results, exactly the results with the names one
term and `crc` asserted (`fifth_destroyed_givens_differ_exactly_on_those`
true in every ANCHORED run) and on none asserting no `xrx`.

**D9. Everything well formed is a result.** Every well-formed state with at
least one term is a result of either beginning, with its names on any terms:
`result6_iff_A`, `result6_iff_B` (from D12: `reach6_of_names`); the one-term
states asserting `ara` any number of times included (`loopState_is_a_result`).
5:D9 re-proved without legality. **The results extend**: every result of the
fifth seed is a result of the sixth at the same round (`results_extend_A`,
`_B`, through the embedding), the sixth has results the fifth has not
(`results_grow`), and among the states asserting no `xrx` the two seeds have
the same results (`legal_results_are_the_fifths`). Computed: in every run and
census the results asserting no `xrx`, with their rounds, are exactly the
fifth derivation's exploration's at the same bound and rounds
(`same_results_and_rounds_as_fifth_derivation`; 5:K1, 5:K2 computed again),
and the fifth's independent counts are the `xrx`-free part of this
derivation's (`fifth_counts_are_the_xrx_free_part`, `counts.csv`; 5:K1
computed again).

**D10. No answers.** The seed has nothing to answer; every recorded attempt
is a performed change (`given.json`: `of_which_obstructed: 0` on every
beginning; `attempts_not_performed: 0`). The fifth's builds for `xrx` are two
additions whose outcomes are results like every state (5:D10's
`build_answer5` through the embedding); they answer nothing. The fifth's
"every answer is a sequence of performed changes" (5:D10) survives vacuously
and its results-independence has nothing to be independent of.

**D11. Changes commute with one-to-one rewriting; sequences keep their
length.** `Step6.rename` (`rename4_addTerm`, `rename4_addAssertion` — the
fourth's, stated for any `x`, `y` — and the fifth's `rename4_remove`,
`rename4_identify`, no change), `Reach6.rename`, `lostA6_rename`,
`lostB6_rename`, `costA6_rename`, `costB6_rename` (5:D11 re-proved for the
four kinds without conditions).

**D12. Reachability: the names decide.** A well-formed state `t` is
reachable from a well-formed state `s` exactly when the names, if one term
in `s`, are one term in `t`: `reach6_iff` (5:D12's `reach5_iff` re-proved
with "legal" dropped from `t`). Necessity is D7. Sufficiency
(`reach6_of_names`): remove every assertion (`reach5_clear`, 5:D12, through
the embedding: it mentions no legality), identify every term other than the
named ones into `a` (`reach5_collapse`, through the embedding; every
identification is now performed, but the fifth's path already had nothing
asserted at that point), move the names onto the target's named terms
(`move_a_pair`, `move_b_pair`, `two_names_to`, `merge_names`, `move_one`, all
5:D12 through the embedding), then the target contains the state reached and
additions reach it — `xrx` like any pair (`reach6_of_contains`). Under FREE
there are no names and every result reaches every result. Containment is
still sufficient (`contains4_reach6`) and still not necessary
(`criterion_not_containment`; 5:D12 through the embedding). Computed: the
criterion agrees with a search along the changes among the results within 3
terms and 7 rounds on every ordered pair of results within 3 terms and 4
rounds, in all four combinations (`criterion_agrees_with_search`; 148 996
pairs, names kept, no `bra`, of which 132 355 involve a result asserting some
`xrx`), and the fifth's criterion agrees with the sixth's on every pair of
the fifth's results (`fifth_criterion_agrees_on_fifth_results`; 16 641 pairs,
5:K8 computed again).

**D13. Reachability is mutual within two classes; every result reaches
itself; any two results are comparable.** `reach6_symm`, `reach6_back_A`,
`reach6_back_B`, `reach6_total`; every well-formed state with a term reaches
itself in two changes (`cycle2_6`, 5:D13's `cycle2` through the embedding),
so the lengths of the sequences reaching a result are unbounded
(`Reach6.cycles`, `Reach6.unbounded`), and infinitely many sequences reach
every result. One-way reachability stays refuted (`no_return_fails6`,
`antisymm_fails6`, `length_not_unique6`, 5:D13 through the embedding).
Computed: 63 300 unordered pairs of different results reachable both ways
among the 386 results within 3 terms and 4 rounds (names kept, no `bra`),
11 005 ordered pairs unreachable — all from the 31 results with the names
one term to the 355 with them apart — and every result has a two-change
cycle in every run (`results_with_a_two_change_cycle = results`).

**D14. Within the bound the exploration is complete; the frontier is exact;
the shortest-sequence counts are exact where said.** *Completeness.* Let the
bound be `N` terms and `R` rounds. Every well-formed state with at most `N`
terms and cost at most `R` lies at the end of the sequence of D8(ii), whose
states have at most `max(2, terms)` terms and whose cost rises by exactly one
at each change; so every state on it is within the bound and, by induction
along it, found by the exploration in round = cost. Every explored state is
a well-formed state within the bound by construction. The results with `n`
terms, total multiplicity `t` and destroyed givens `lost` are counted
independently by the orbit method (K1): the rewriting acts on *all* `n²`
ordered pairs — the earlier derivations' cycles of off-diagonal pairs plus,
for each cycle of the rewriting of length `p`, one cycle of length `p` of
diagonal pairs (`diag_cycles`) — each cycle contributing the fourth's series
`1 / (1 − x^L)` (4:D14, 5:D14, no change), or a capped series `1 + x^L + … +
x^{cL}` where the largest `xrx` multiplicity matters; with names, the first's
kinds for the names apart and, for the names one term, three kinds by how
often `crc` is asserted at the named term (`count_named`, `lost_of_kind`);
without names, the least of the two placements by the series for "nothing
off-diagonal", "no pair both ways" and "every `xrx` below `m`"
(`counts_by_lost`; `code/sixth/orbits.py`). The explored counts by (terms,
total, lost) equal the independent counts restricted to cost at most `R` in
every run and census (`explored_equals_independent_count`), and with the cap
at zero the count is the fifth's (`tests/test_sixth_orbits.py`,
`counts.csv`). *Frontier.* An attempt leaves the bound on terms exactly when
it is "add a term" on a result with `N` terms (there are no builds): one
entry per such result whose changes were attempted
(`frontier_entries_are_1_per_state_with_N_terms` true in every run); the
results of round `R` are the second part. *Shortest sequences.* A shortest
sequence consists of cost-raising changes (D8(iv)); to a result with the
names apart none of them removes a term, so the sequence never has more
terms than the result — exact within any bound holding the result; to a
result with the names one term, at most one more (built apart, merged last);
under FREE, a FREE-shortest sequence is ANCHORED-shortest for an optimal
placement, so the count is exact when the result has fewer terms than the
bound or no optimal placement puts the names on one term — a new clause: on
`c d; crc` (no `bra`) both placements destroy one given, and "add a term,
identify `a` and `b`" is a shortest sequence through three terms
(`merged_optimal`, `sequences_exact`; 62 299 of 63 362 exact in the ANCHORED
4-term run, 22 607 of 22 618 in the FREE 5-term run). *Rounds.* The number of
results of round `r` without any bound is given by the series and the cost
formula (`layer_counts`); rounds `0 … N − 2` of a run within `N` terms agree
with it (`rounds_agreeing_with_unbounded_formula`), since a result of round
`r` has at most `r + 2` terms (its cost is at least its number of terms minus
two: with the names apart `t ≥ m0 − lost`; with them one term `cost ≥ n + t
+ m0 − 2·min(M(c,c), m0) ≥ n`). 5:D14 survives with the diagonal cycles added
and the FREE exactness clause.

**D15. `bra` and passing on.** In a state asserting no `xrx`, `bra` together
with passing on is impossible (`passing_on_refutes_bra`, 1:R7, on legal
states: `arb`, `bra` and passing on give `ara`). With `xrx` allowed it is
possible: with `bra` given, "passes on" holds in the one-term state `a; ara(2)`
reached in one change and in `a b; arb bra ara brb` (computed:
`follows_*_with_bra.csv`, `passes_on` first holds in round 1). So 1:R7
survives on legal states only.

**D16. A result reached by two different shortest sequences.** The one-term
state asserting nothing: remove `arb` then identify, or identify then remove
`ara` — two shortest sequences where the fifth had one (computed, column
`shortest_sequences_of_changes`; with `bra` given five where the fifth had
two); `a (a and b one term); ara(2)` by five (identify then add `ara`; add
`ara`, `arb`, `bra` or `brb` then identify); and every result is reached by
sequences of different lengths (D13).

**D17. Two terms: the results of every round in closed form.** With the
given terms only (names kept, `bra` not given) the results of round `r` are:
the names apart with `arb` `1 + i` times, `bra` `j`, `ara` `p`, `brb` `q`,
`i + j + p + q = r` (`C(r+3, 3)`); `arb` missing, `j + p + q = r − 1`
(`C(r+1, 2)`); the one-term state with `ara` `K` times, of cost 2 for `K = 0`
and `K` otherwise (one result in every round `r ≥ 1`, two in round 2); the
names one term with a second term and `crc` `K` times: `K = 0`, `C(r−1, 2)`;
`K ≥ 1`, `C(r+1, 3)`. Total `1, 6, 16, 32, 59, 98, 151, 220, …` — cubic, so
100 rounds would hold about four million results. With `bra` given:
`C(r+3, 3) + 2·C(r+1, 2) + (r − 1)[r ≥ 2] + one_b(r) + C(r−2, 2) + C(r−1, 2) +
C(r+1, 3)` with `one_b = 0, 1, 2, 2, 1, 1, …`: `1, 7, 20, 41, 73, 120, 183,
264, …`. Proof: the cost of each kind of state with at most two terms
(`code/sixth/evidence.py` `two_term_round_count`); computed:
`two_term_rounds_equal_closed_form` true on all 20 rounds of both ANCHORED
two-term runs (and on 30 in the timed trial, `change_log.md` item 10). The
shortest sequences to a two-term result with the names apart are the
arrangements of its cost-raising changes — for each given, `M − 1` additions
if it is asserted and one removal if not; `bra` when not given, `ara`, `brb`
their multiplicities — a multinomial coefficient
(`two_term_sequences_equal_multinomial` true on both runs); 5:D17's
`C(i + j, i)` is the case `p = q = 0` with no removal. Without names: `1, 6,
11, 19, 28, 44, 60, …` (no `bra`).

**D18. Every state has a two-change cycle; no change keeps the round.** See
D13 and D8(v). The two ANCHORED explorations do not correspond round by
round (63 362 against 76 905 results at 4 terms and 8 rounds), as 5:D18.

**D19. The unchosen reading of identification.** Under the reading in which
a merged multiplicity is the *larger* of the parts instead of their sum, the
results are the same (every well-formed state: the sufficiency of D12
identifies terms only in states with nothing asserted at all), the
reachability criterion is the same (it depends on the names only), and the
cost is the same without `bra`: the identification case of D8(i) needs
`min(S, m0) ≥ p` with `p ≤ 1`, which the larger part gives. With `bra` given
the costs differ: identifying `a` and `b` in `a b; arb bra` gives `a; ara(2)`
under the sum reading (one change) and `a; ara` under the larger-of-the-two
reading, from which `a; ara(2)` is two changes away, while the potential's
identification case needs `M'(c,c) ≥ 2` and fails. So 5:D19 (both readings
give the same results and cost) does not survive; the unchosen reading is
kept as an alternative with the same results and reachability and a cost of
its own, not computed here (O6). Not in Lean; the proof is this paragraph.

## 5. What does not follow

Each item has two witnesses among the results, or a proof.

**N1. `bra`. N2. Not `bra`.** Both beginnings are results. Lean:
`bra_not_refuted`, `bra_not_derived` (1:N1, 1:N2, no change).

**N3. Anything on which two results differ**, and by D9 that is anything
about the asserting not true of every well-formed state: of the twenty-two
statements tested (the fifth's twenty-one plus "some `xrx` is asserted"),
exactly "at least one term" holds in every result within the bound of every
run (`statements_holding_in_every_result`), and it is proved for all results
(D6). Every other statement holds in some result and fails in another in
every run (`statements_that_do_not_follow`): the fifth's "no `xrx`" now fails
in round 1 (`a b; arb ara`, `a (a and b one term); ara`).

**N4. That there are exactly two terms.** Holds in what is given, fails
after adding a term, and fails after one change the other way (identify `a`
and `b`).

**N5. That what is given survives.** `arb` stays asserted: fails after one
change (remove it). `a` and `b` stay two terms: fails after one change
(identify them; 5:N5 had two changes without `bra`, three with it). Something
is asserted: fails after one change without `bra`, two with it. No `xrx`:
fails after one change (`follows_*.csv`: first failing rounds 1, 1, 1, 1
without `bra`).

**N6. Which answer an obstructed change gets.** Nothing is obstructed and
nothing is answered (D3, D10); the fifth's N6 has no object.

**N7. Growth.** Nothing forces terms or assertions to be added: what is given
adds none, one change gives a result that adds one of either, one change
gives a result with one term fewer or one assertion fewer. Every result is
finite (D6); every round has a new result (D9, D17).

**N8. That a result is reached by one sequence only, or by finitely many;
that results of one round are reached by equally many shortest
sequences.** Every result is reached by infinitely many sequences (D13).
What is given is reached by one shortest sequence, `a b; arb ara` by one,
`a; ara` by one, `a; nothing` by two, `a; ara(2)` by five, `a b; bra` by two,
all of rounds 1–2 (column `shortest_sequences_of_changes`; 72 of the 63 362
results of the ANCHORED 4-term run have one shortest sequence, 48 of them
asserting no `xrx`).

**N9. That the number of attempts on a result is the same for results of one
round with equally many terms.** It is `C(n, 2) + d + 1 + n²` (D3) and
depends on `d`: 6 for `a b; nothing asserted` and 8 for `a b; arb ara`, both
of round 1.

**N10. That nothing is asserted twice; that `arb` is asserted exactly once;
that all asserted assertions are asserted equally often; that `xry` and
`yrx`, when both asserted, are asserted equally often.** As 5:N10, with the
same witnesses (`follows_*.csv`).

**N11. That the two beginnings differ in what they reach, or in which
statements hold in some result.** Both reach every well-formed state (D9);
every statement independent under one beginning is independent under the
other (`statements_that_do_not_follow` the same list in every ANCHORED run).
They differ in the cost of each result (D8) and so in the rounds (D18).

**N12. That reachability is one-way, or that any two results are
incomparable.** Refuted and derived respectively (D13), as 5:N12.

**N13. That a multiplicity never falls; that the number of terms, the total
multiplicity, the size, or the fewest classes of a split never falls; that
no `xrx` stays asserted.** All refuted by witnesses (the fifth's, through the
embedding, plus adding `ara` to what is given). Computed: in the ANCHORED
4-term run 96 533 changes lower the number of terms, 82 349 a multiplicity,
178 882 the size, 3 730 the fewest classes (between results asserting no
`xrx`; the fifth's number), and 35 372 make some `xrx` asserted on a result
asserting none (`changes_lowering`).

**N14. That a state is contained in its outcome; that a sequence of changes
carries every assertion somewhere.** Refuted (the fourth's containment, the
second's carrying map): the fifth's `contains_fails` through the embedding.

**N15. That `a` and `b` stay two terms; that `arb` stays asserted; that no
`xrx` is ever asserted.** Refuted: D1, D2, D4, D6.

**Refuted** (each a proved impossibility): `a` and `b` one term to begin
with (R1, D1, on the given state); a result reached by more than one
attempt's refusal — there are none (R2, D3); telling `a` and `b` apart again
after identifying them; what is given reached from a one-term state (R5, D7);
`bra` together with passing on in a state asserting no `xrx` (R7, D15, on
legal states); a sequence of changes to a result shorter than its cost (R8,
D8); a well-formed state with at least one term that is not a result (R9,
D9); a change that keeps the cost, or the round, where it was (R10, D8(v));
a pair of results with the names apart that do not reach each other, or a
pair of results neither of which reaches the other (R12, D13); an obstructed
attempt, or an attempt not performed (R13, D3); the fifth's potential as a
lower bound on every result (R14, D8); the fifth's "removing first or last
gives the same state" on every state (R15, D5).

## 6. The exploration

**Protocol.** From each beginning, under each reading of sameness (four
combinations): round by round, every change on every result first reached in
the round before (C6), each result's changes fewest additions first —
identifications (each unordered pair once), removals (each asserted pair
once, diagonal pairs included), a term, then every ordered pair as an
addition, `xrx` included, asserted already or not (`C(n, 2) + d + 1 + n²`
changes, every one performed). Each attempt records whether its outcome
asserts some `xrx` while the state asserts none (what the fifth seed would
have obstructed). Three explorations per combination (C8′): the main run (5
terms under FREE, 4 under ANCHORED, 8 rounds), a deeper run (3 terms, 9
rounds), and the two-term run (the given terms only, 20 rounds). Beside every
run the fifth derivation's exploration is made at the same bound and rounds
and compared on the results asserting no `xrx` (D9). Files per run
(`evidence/sixth/`, tag `bound{N}_rounds{R}_{reading}_{beginning}`):
`results_*.csv` (one row per result: terms, assertions counted and asserted,
largest multiplicity, largest `xrx` multiplicity, additions to what is given,
round, cost by formula, destroyed givens by this derivation's formula and by
the fifth's, fewest classes where no `xrx` is asserted, changes, changes
making some `xrx` asserted, whether its changes were attempted, shortest
sequences and whether the count is exact, whether it reaches what is given,
whether the names are one term, whether it contains what is given, whether
it asserts nothing twice, whether it asserts no `xrx`, the fifth's
shortest-sequence count where it is a result of the fifth), `added_*.csv`,
`frontier_*.csv`, `rounds_*.csv`, `follows_*.csv`; per combination
`reach_bound3_rounds4_*.csv` and the full attempt log
`attempts_bound2_rounds3_*.jsonl`; `counts.csv`, `given.json`,
`summary.json` (every check, per run), `lean_axioms.txt`, `MANIFEST.sha256`.

**Results within the bound** (K1, K2). Every check of every run passes
(`summary.json`; `python code/generate_sixth.py` prints one line per run).

| run | results | by terms | asserting no `xrx` (the fifth's) | names one term (with `crc`) | shortest sequences (total) |
|---|---|---|---|---|---|
| FREE, no `bra`, 5 terms, 8 rounds | 22 618 | 9 / 355 / 4 128 / 10 763 / 7 363 | 5 015 | — | 110 119 099 |
| FREE, `bra`, 5 terms, 8 rounds | 38 075 | 10 / 400 / 5 875 / 18 494 / 13 296 | 9 492 | — | 166 017 436 |
| ANCHORED, no `bra`, 4 terms, 8 rounds | 63 362 | 9 / 881 / 15 720 / 46 752 | 14 061 | 2 615 (2 143) | 96 500 555 |
| ANCHORED, `bra`, 4 terms, 8 rounds | 76 905 | 10 / 1 064 / 19 600 / 56 231 | 17 240 | 2 767 (2 615) | 125 032 822 |
| FREE, no `bra`, 3 terms, 9 rounds | 8 724 | 10 / 500 / 8 214 | 892 | — | 88 637 078 |
| FREE, `bra`, 3 terms, 9 rounds | 12 403 | 11 / 560 / 11 832 | 1 284 | — | 133 010 892 |
| ANCHORED, no `bra`, 3 terms, 9 rounds | 35 241 | 10 / 1 294 / 33 937 | 4 124 | 3 616 (2 880) | 153 693 043 |
| ANCHORED, `bra`, 3 terms, 9 rounds | 43 905 | 11 / 1 551 / 42 343 | 5 003 | 3 928 (3 616) | 203 743 045 |
| FREE, no `bra`, 2 terms, 20 rounds | 6 357 | 21 / 6 336 | 133 | — | about 2.2 · 10^12 |
| FREE, `bra`, 2 terms, 20 rounds | 7 029 | 22 / 7 007 | 143 | — | about 2.8 · 10^12 |
| ANCHORED, no `bra`, 2 terms, 20 rounds | 20 642 | 21 / 20 621 | 423 | 8 476 (7 335) | about 4.2 · 10^12 |
| ANCHORED, `bra`, 2 terms, 20 rounds | 23 342 | 22 / 23 320 | 426 | 9 446 (8 476) | about 4.3 · 10^12 |

In every run the results asserting no `xrx`, with their rounds, are exactly
the fifth derivation's exploration's at the same bound and rounds (5:K1, 5:K2
computed again; the fifth's 14 061, 17 240, 5 015, 9 492 at the main bounds
reappear as the column), their shortest-sequence counts are the fifth's on
those with the names apart (FREE: two or more terms) and larger on every one
with the names one term (222 and 81 in the ANCHORED 4-term runs; the
one-term state under FREE). By destroyed givens (ANCHORED, no `bra`, 4
terms): 49 742 with none, 13 148 with one, 472 with two. Every count by terms,
total multiplicity and destroyed givens equals the independent count
(`explored_equals_independent_count`, D14), and every result's round is its
cost (D8).

**Rounds** (K2). ANCHORED, no `bra`, 4 terms
(`rounds_bound4_rounds8_anchored_without_bra.csv`): new results per round 1,
7, 27, 97, 352, 1 244, 4 258, 13 964, 43 412; of which asserting no `xrx` 1,
4, 13, 40, 129, 400, 1 195, 3 370, 8 909 (the fifth's); with the names one
term 0, 1, 3, 7, 21, 62, 186, 573, 1 762; without any bound on terms 1, 7,
27, 98, 364, 1 350, 5 060, 19 267, 74 674 (`layer_counts`; rounds 0–2 agree
with the run, as every round up to `N − 2` must). FREE, no `bra`, 5 terms: 1,
7, 21, 59, 171, 508, 1 553, 4 857, 15 441 against 1, 7, 21, 59, 172, 519,
1 614, 5 206, 17 386 without bound. With two terms, names kept: 1, 6, 16, 32,
59, 98, 151, 220, … (D17). Every round of every run has a new result.

**Attempts** (K3). 463 776 changes attempted in the ANCHORED 4-term run
(the fifth's 124 730 on the same legal results, plus those on results
asserting some `xrx`), 35 372 of them making some `xrx` asserted on a result
asserting none — exactly the fifth's 35 372 obstructed attempts (5:K3), now
performed; 7 and 3 in round 1 of the runs without `bra` (identify `a` and
`b`, giving `ara`; remove `arb`; a term; `ara` and `brb`; `arb` again; `bra`),
8 and 3 with `bra`. The totals equal `C(n, 2) + d + 1 + n²` and `n` plus the
related pairs, summed over the results whose changes were attempted (D3), in
every run. Of the 451 157 changes within the bound of the ANCHORED 4-term
run, 297 140 raise the round by one and 154 017 lower it (by one, three or
five); none keeps it (D8(v)).

**Frontier** (K5). Every result with `N` terms whose changes were attempted
has one entry (the term): 12 619 in the ANCHORED 4-term run, 1 592 in the
FREE 5-term run. The second part, the results of round 8 whose changes
await: 43 412 results with 1 115 640 changes (ANCHORED, 4 terms), 15 441
with 482 779 (FREE, 5 terms); 3 483 results after round 20 with
two terms.

**Results by what they add to what is given** (K6;
`added_bound4_rounds8_anchored_without_bra.csv`). One result adds (−1, −1)
(the one-term state asserting nothing, round 2), one adds (−1, 0) (`a; ara`,
round 1), one adds (−1, 1) (`a; ara(2)`, round 2), two add (0, −1), eight add
(0, 0) (rounds 0–4), twenty add (0, 1) (rounds 1–5), two add (1, −1), fourteen
add (1, 0). Results with the same additions appear in different rounds
because of the destroyed givens.

**Statements** (K7; `follows_*.csv`). Twenty-two statements tested (N3); the
one holding everywhere is proved (D6); the first failing rounds, names kept,
no `bra`: `arb` asserted 1; `a`, `b` two terms 1; something asserted 1; no
`xrx` 1; nothing twice 1; at least two terms 1; both ways never 1; `arb` once
1.

**Reachability within 3 terms and 4 rounds** (K8;
`reach_bound3_rounds4_*.csv`, `summary.json` `reachability`), along the
changes among the results of 3 terms and 7 rounds:

| reading, beginning | results (names one term; some `xrx`) | ordered pairs | reachable | unordered pairs both ways | the fifth's results / pairs / reachable under both |
|---|---|---|---|---|---|
| ANCHORED, no `bra` | 386 (31; 257) | 148 996 | 137 991 | 63 300 | 129 / 16 641 / 16 021 |
| ANCHORED, `bra` | 467 (33; 310) | 218 089 | 203 767 | 94 489 | 157 / 24 649 / 24 339 |
| FREE, no `bra` | 192 (—; 138) | 36 864 | 36 864 | 18 336 | 54 / 2 916 / 2 916 |
| FREE, `bra` | 221 (—; 152) | 48 841 | 48 841 | 24 310 | 69 / 4 761 / 4 761 |

The criterion agrees with the search on every pair; the unreachable pairs
are exactly those from a result with the names one term to one with them
apart (31 × 355 = 11 005; 33 × 434 = 14 322); on the fifth's results the two
criteria agree pair by pair.

**Census** (ANCHORED, 5 terms, 8 rounds, counts only): 93 392 results (9 /
881 / 15 720 / 46 752 / 30 030 by terms) without `bra`, 111 350 with it;
673 843 and 809 776 changes attempted, 55 119 and 66 376 making some `xrx`
asserted (the fifth's obstructed counts, 5:§6); the fifth's 25 212 and 30 264
results are the results asserting no `xrx` in both; every check passes.

**Independent counts** (K1; `counts.csv`): all well-formed states with `n ≤
5` terms by total multiplicity `0 … 12`, under any rewriting (13, 924, 49 357,
1 278 844, 15 677 058 for `n = 1 … 5`) and with the names kept, by how the
named terms stand (13, 3 640, 441 252, 20 324 339, 388 041 502), beside the
fifth's counts of states asserting no `xrx` (5:K1, cited and computed again:
the `xrx`-free part).

**What is given** (`given.json`): the two beginnings, their 7 or 8 attempts
with the records, all performed; identifying `a` and `b` gives `a (a and b
are one term); ara` (cost 1; the fifth's formula would say 3) or, with `bra`,
`ara(2)` (cost 1; the fifth's 5); adding `ara` costs 1; each beginning
reaches the other, the one-term states, `arb` twice, and `a b; nothing
asserted`, and all but the one-term states reach it back.

**Reproducibility** (K9, K10). `python code/generate_sixth.py` rewrites every
computed file of `evidence/sixth/` (about sixteen minutes here);
`--check` regenerates into a temporary folder and compares byte for byte
(matched); `MANIFEST.sha256` lists every file's hash. `python
code/lean_report_sixth.py` builds all six Lean libraries and rewrites
`evidence/sixth/lean_axioms.txt` (175 theorems, every one within
`propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit` or declared
axiom in `lean4/`). After this work the five earlier derivations' `--check`
and Lean reports were re-run (`paper/sixth/change_log.md`, item 15). Tests:
516 passed, six derivations; line coverage 99.96 %, branch coverage
99.47 % of all of `code/`, every evidence module fully covered (`python
code/xry/gate.py coverage.json`); `mypy --strict` clean; the prose watchlist
clean, with every pinned hit of this paper in §10.

## 7. What survives once nothing is forbidden

The task asks whether the results, the reachability criterion, the cost, and
the obstruction and answer notions survive. In one line each, with the Lean
statements of `Sixth/Compare.lean`:

- **The results extend.** Every result of the fifth seed is a result of the
  sixth at the same round (`results_extend_A`, `_B`); the sixth has results
  the fifth has not (`results_grow`); the results are now every well-formed
  state with at least one term (`results_are_every_wf_state`), and among the
  states asserting no `xrx` the two seeds agree (`legal_results_are_the_fifths`).
  So the fifth's set survives as a part, not as the whole.
- **The reachability criterion survives.** The names decide, for every
  well-formed target (`criterion_survives`); containment stays sufficient and
  not necessary; mutual reachability within the two classes, comparability
  and the two-change cycle stay (D12, D13).
- **The cost survives on the fifth's results and on every result with the
  names apart, and changes with the names one term.** There the fifth's
  fewest changes are the sixth's (`cost_survives_on_legal`,
  `cost_survives_names_apart`); with the names one term and `crc` asserted
  the fifth's potential is no bound (`cost_fails_names_merged`) and the
  destroyed givens become `m0 + 1 − min(M(c,c), m0)` (D8). The size difference
  survives on results containing what is given; parity survives.
- **The obstruction notion does not survive; its characterisation does.**
  Every attempt is a change (`nothing_obstructed`); on a state asserting no
  `xrx`, the changes that make some `xrx` asserted are exactly the fifth's
  obstructed attempts (`Step6.not_legal_iff`), and their number on the
  fifth's results is the fifth's (K3).
- **The answer notion does not survive.** There is nothing to refuse and
  nothing to build; the fifth's removal answer and the identification it
  answered are now two sequences to two different results
  (`remove_answer_differs`), and "removing first or last gives the same state"
  fails (`first_or_last_fails`).

## 8. Alternatives: kept, or eliminated by proof

| Alternative | Kept / eliminated |
|---|---|
| `bra` asserted to begin with / not | both kept: computed under both; N1, N2 |
| other beginnings (`bra` `k ≥ 2` times, more terms, some `xrx`) | eliminated as starting points by D9 (results of the chosen beginning, with the same results); not computed separately |
| FREE / ANCHORED sameness | both kept: every file exists under both |
| identification: multiplicities add up / the larger of the two | the first chosen and computed; the second kept as an alternative with the same results and reachability and a different cost with `bra` given (D19, O6) |
| the fifth's answers (refuse, remove the obstruction, build) | eliminated as answers (nothing to answer, D3); the sequences they named are kept as sequences (D5) |
| the other orders of attempts | not computed; same results and rounds (D8) |
| a bound on terms alone | eliminated: the results within it are infinite (D9) |
| every well-formed state within the bound, up to sameness | kept; none dropped (D14) |

Earlier results that fail under the sixth seed, each with the reason:
5:D3's obstruction (an attempt refused) — empty, D3; 5:D4 (adding `xrx`
obstructed in every state) — refuted, D4 (`xrx_is_a_result`); 5:D5's
`remove_obstruction_first_or_last5` — refuted without legality,
`first_or_last_fails`; 5:D6 "every result is legal", 1:D6 — refuted,
`legal_not_kept`; 5:D7's `Reach5.arb_gone_for_good`, 1:D7's
`Reach.arb_gone_for_good` — refuted, `arb_gone_fails`; 4:D1, 1:D1 "`a ≠ b`"
— survives on legal states only (D1); 5:D8's destroyed givens for the names
one term — replaced, `fifth_potential_fails`, `cost_loopState`; the cost
survives on legal states and with the names apart; 5:D9 (results = legal
states), 1:D9 — the set extends, D9; 5:D10 (answers reach nothing new) —
vacuous; 5:D15, 1:R7 (`bra` with passing on impossible) — on legal states
only, D15; 5:D17's `2r` — replaced by the cubic forms, D17; 5:D19 (the two
readings of identification agree in cost) — fails with `bra` given, D19;
5:N3's "no `xrx`" among the everywhere-true statements — fails, N3; 5:N5's
"two changes / three changes" to part the names — one now, N5; 5:N6, 5:R2,
5:R3, 5:R6, 5:R11 (about answers, obstructions and builds) — without object;
5:R4 (a state without terms) survives; 5:K3's obstructed count — recovered
as the count of changes making some `xrx` asserted on the fifth's results;
the fourth's `has_two_way` — counts `xrx` as both ways, written again
(`change_log.md`, item 5); every K-claim of the fifth — computed again as the
`xrx`-free part (§6). Everything else cited stands with the re-check given at
its citation.

## 9. Open

- O1 of the earlier papers (multiplicity) stays closed by the fourth seed.
- O2. Number of new results in rounds beyond the bound: given by the series
  and the cost formula for any round (D14, `layer_counts`); not listed.
- O3. Results beyond the declared bounds, listed: the frontier is exported
  (both parts); the census counts at 5 terms; the seed's 100 rounds with two
  terms are given in closed form (D17), not listed.
- O4. Other readings of "build structure": without object under this seed.
- O5. A closed form for the number of shortest sequences reaching a result
  with three or more terms, or with the names one term: computed per result
  within the bound (K7); with two terms and the names apart it is the
  multinomial of D17.
- O6. The cost under the unchosen reading of identification (the larger of
  the two multiplicities) with `bra` given: shown to differ from the chosen
  reading's (D19); not computed.
- O7. Lean statements of D8(iv) (exactly which changes raise the cost by
  one), of the exactness of the shortest-sequence counts (D14), and of D19:
  proved in the paper and checked by computation.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Directed multigraphs with loops under vertex identification, edge
  deletion and insertion.** Dropping "no `xrx`" turns the fifth's loopless
  marked multidigraphs into marked multidigraphs with loops, and the
  identification of adjacent vertices — barred as a loop-creating
  contraction under the earlier seeds — into an ordinary contraction that
  turns the arcs between the two vertices into loops at the merged vertex.
  D9 is that the edit graph on marked multidigraphs with loops is connected
  except for the one-way merge of the two marks; D12 and D13 that its strong
  components are the fifth's two (marks apart, marks merged) under ANCHORED
  and one under FREE.
- **Graph edit distance from a fixed small graph** (Sanfeliu and Fu, 1983),
  with contraction allowed everywhere. D8 is a closed form for the edit
  distance from the two-vertex marked multigraph `arb` to any marked
  multidigraph with loops, at unit cost per edit: the size difference plus
  twice the destroyed marks, where a contraction of the two marked vertices
  now keeps up to `m0` of the marked arcs as loops — the potential-function
  argument of the first derivation with the merge case re-done. On loopless
  targets and on targets with the marks apart it is the fifth's distance.
- **Pólya enumeration with the diagonal included.** The independent count
  (D14) is the cycle-index computation of the fourth and fifth derivations
  with the loops among the cycles of the rewriting (one cycle of loops per
  cycle of vertices), the figure series `1 / (1 − x)` or a truncated one
  where the largest loop multiplicity enters the cost.
- **Compositions.** With two vertices the results of round `r` are counted
  by compositions into four parts (`C(r+3, 3)`) and their degenerate cases
  (D17); the shortest sequences to a state with the marks apart are the
  arrangements of a multiset, a multinomial coefficient.
- **Reflexive relations.** A state asserting `xrx` at every term is a
  reflexive relation; nothing in the seed singles these out, and they are
  results like the others.

What appears to be specific to this seed: that dropping the one prohibition
removes the obstruction and answer apparatus entirely while leaving the
reachability criterion, the parity, the one irreversible change and the cost
on states with the marks apart exactly as they were (`Sixth/Compare.lean`);
that the only place the cost changes is the merge of the marks, where the
fifth's "everything given is lost" becomes "the merge keeps up to `m0` of the
givens as `ara`"; that the two readings of identification, which the fifth
derivation proved to agree on results and cost, now disagree on the cost with
`bra` given (D19); and that with the given terms only the results of round
`r` grow as `r³` (D17), where every earlier seed had at most `2r`.
