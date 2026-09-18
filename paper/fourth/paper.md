# What follows from `arb` once, no `xrx`, and assertions that are counted

Fourth derivation. Input: `prompt/fourth/seed_prompt.md`. Task:
`prompt/fourth/prompt.md`. Claim IDs refer to `paper/fourth/claim_ledger.md`;
an ID written `1:D8` refers to the first derivation's ledger
(`paper/claim_ledger.md`, paper `paper/paper.md`), `2:D8` to the second's
(`paper/second/`), `3:D8` to the third's (`paper/third/`). Lean names in the
namespace `Seed.Fourth` are in `lean4/Fourth/`; names in `Seed.Third`,
`Seed.Second`, `Seed` are the earlier derivations' (`lean4/Third/`,
`lean4/Second/`, `lean4/H3V7N5QF/`). The axiom report for every theorem cited
here, of any of the four libraries, is `evidence/fourth/lean_axioms.txt`.
Computed files are in `evidence/fourth/`, written by
`python code/generate_fourth.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; the unchosen
readings are listed), **derived** (proved), **computed** (output of `code/`),
**refuted** (proved impossible), **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the fourth seed, and the re-check says whether the result *survives the
assertion being counted*. The re-check is one of four kinds. *(no change)*:
the statement mentions no assertion, or only whether an assertion is asserted
(read here as "has positive multiplicity"), so it stands as it is.
*(through the maps)*: the statement is about the earlier states or changes;
two maps connect them with the counted states — the *support* of a counted
state (the earlier state asserting exactly what has positive multiplicity,
Lean `toSt`) and the *indicator* of an earlier state (the counted state
asserting everything once, `ofSt`); every change of the third seed is a
change of the fourth on indicator states (`Step2.toStep4`,
`Reach2.toReach4`), and a change of the fourth whose outcome asserts nothing
twice is a change of the third on the supports (`Step4.toStep2`,
`Reach4.toReach2`). So the earlier statement survives exactly on the states
that assert nothing twice ("simple" states, `Simple`), and what is stated
here for all counted states is its extension. *(re-proved)*: the earlier
proof used that an assertion is asserted or not, and a statement covering
multiplicities is proved afresh. *(computed again)*: a computed statement of
the third derivation is re-run beside the fourth exploration and the two are
compared on the results asserting nothing twice. Results of the earlier
derivations that fail under the fourth seed are listed in §7.

## 0. Findings in brief

1. The fourth seed is the third with the assertions counted: each `xry` is
   asserted a number of times, adding it raises that number by one, and `arb`
   is asserted once (given, §1). The earlier derivations' reading C1
   ("asserted is yes or no") and their open item O1 are replaced by the seed.
2. `a` and `b` are two terms; there are two beginnings, with and without
   `bra`, the one without reaching the one with in one change and never the
   other way (D1, D2). But the given terms alone now carry infinitely many
   legal states that contain what is given — `arb` `i` times, `bra` `j` times
   — of which exactly two assert nothing twice (D2); the earlier "exactly two
   states on the given terms" does not survive as stated (§7).
3. Every change leaves its state contained in its outcome, with every
   multiplicity the same or higher (D5). What is given survives, no
   multiplicity ever decreases, obstructions are never cleared, the fewest
   classes of a split never decreases (D6, D7, D13). The multiplicity of
   `arb` is not kept at one: adding `arb` again is a change (N11).
4. The obstructed changes are exactly the additions of some `xrx`; every
   result with `n` terms has `1 + n²` changes, `n` of them obstructed,
   whatever it asserts (D3). "Remove the obstruction" is impossible or
   coincides with refusal (R3, C7); the one-term builds are exactly two
   (D10).
5. Size, counting multiplicities, rises by exactly one per change; every
   sequence of changes to a result has the same length, the size difference;
   the round of a result is its size difference (D8). **The cost survives**
   the counting, with `m` read as the sum of the multiplicities.
6. The results are the legal states containing what is given, multiplicities
   compared one by one (D9). **The results survive and extend**: the results
   asserting nothing twice are exactly the third seed's results, in the same
   rounds, reached by the same sequences (D9, computed again on every run);
   and the set is now infinite within any bound on terms — every round has
   new results even with the given terms only.
7. **The reachability criterion survives**: a result reaches another exactly
   when an embedding carries it into the other with every multiplicity at
   most the image's (D12); on results asserting nothing twice this is the
   third's criterion, in Lean both ways. **One-way reachability survives**:
   two results reachable from each other are the same result, a result once
   left is never returned to, only what is given reaches what is given (D13).
8. 100 rounds complete only with the given terms: the results at round `r`
   are then `r + 1` (names kept) and all 5 151 results of 100 rounds are
   listed, with the number of sequences reaching each in closed form
   (`C(i + j, i)`, D17). With 3 or more terms the bound is on terms and on
   rounds together (C8); within it the exploration is complete, certified by
   an independent count by series (D14), and the frontier is exported in
   two parts (§6). Everything claimed as derived is in Lean, including the
   every-writing (FREE) statements and the comparison with the third
   derivation, except the within-bound completeness (D14), the two-term
   closed forms (D17) and the correspondence of the two ANCHORED explorations
   (D18), proved in the paper and checked by computation.

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2′ | An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one. |
| G3′ | `arb` is asserted with multiplicity one. |
| G4 | For no term `x` may `xrx` be asserted. |
| G5 | Whether `bra` is asserted is not given. |
| G6″ | A change is exactly one of: adding a term; adding an assertion. Nothing else is a change. |
| G8 | A change that makes some `xrx` asserted is obstructed. |
| G9 | An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which; record the change, the obstruction, the answer. |
| G10 | A refused change is recorded and changes nothing. |
| G11 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, prove what is complete within it. |
| G14 | Any outcome is valid. |

G2′ and G3′ are the two sentences that differ from the third seed (`diff`;
`research/fourth/reading_the_seed.md`). G1, G4, G5, G6″, G8–G14 are the
third seed's word for word.

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry` | given (G1, G2′) | |
| multiplicity of an assertion; adding raises it by one | given (G2′) | replaces 1:C1 and O1 of the three earlier papers |
| asserted = multiplicity at least one | chosen (C1′) | unchosen: none found that fits G3′ and G4 |
| an assertion has a first and a second term | derived (1:§2, no change) | the seed treats `arb` and `bra` as different |
| legal state (no `xrx`) | given (G4) | every `xrx` has multiplicity zero |
| counted state; support; indicator | chosen (C1′) | the model; the two maps to the earlier model (§0) |
| `a`, `b` are two terms | derived (D1) | |
| what is given has exactly the terms `a`, `b`; `arb` once | given (G3′), chosen (C2′) | unchosen: more to begin with; harmless (D9) |
| two beginnings; `bra` once if given | chosen (C2′) | unchosen: `bra` `k ≥ 2` times; harmless (D2) |
| supply of letters not capped | chosen (C3) | harmless for results and fewest changes |
| `r` does not write a term | chosen (C9) | writing only |
| change, two kinds | given (G6″) | |
| adding an asserted assertion is a change | derived from G2′, G6″ (C5′) | replaces the earlier reading C5 |
| a new term has no assertion; an added assertion is between terms there | chosen (C5′) | |
| the order of the changes of a result | chosen (C6) | a term, then the pairs in order; both add one |
| obstructed change | given (G8) | characterised: derived (D3) |
| the obstruction of a change | chosen (C7) | the assertion the change adds |
| refuse / remove the obstruction / build structure | given (G9, G10) | content: chosen (C7); removal impossible or refusal: refuted (R3); results independent of the choice: derived (D10) |
| containment, multiplicities compared one by one | derived (D5) | |
| result | chosen (C6) | a legal counted state up to sameness |
| the results, as a set | derived (D9) | legal states containing what is given; infinite; the third's are those asserting nothing twice |
| sameness | given (G12) | two readings, both kept: chosen (C4) |
| terms and assertions added to what is given | given (G11) | assertions counted with multiplicity, against `a`, `b`, `arb` once for both beginnings; never negative, never decreasing (D6) |
| round; what counts as one change | chosen (C6) | the round of a result is its size difference (D8) |
| bound, frontier | given (G13) | bound on terms and on rounds: chosen (C8′) |
| size, cost, length of a sequence | derived (D8) | size = terms + sum of multiplicities; every sequence has the same length |
| number of sequences reaching a result | computed (K7); two terms: derived (D17) | exact within the bound; `C(i + j, i)` with two terms |
| reachability between results | derived (D12) | containment with multiplicities, one-way (D13) |
| fewest classes of a split | derived (D13) | of the support; never decreases |
| counts of results by terms and total multiplicity | computed (K1) | by series; the third's counts are the simple part |
| what survives the counting | derived (D9, D12, D13, D8; `Fourth/Compare.lean`) | see §7 for what does not |

## 3. Readings that had to be chosen

C3, C4, C6, C7, C9 are the earlier derivations', unchanged in wording or
restated where the multiplicity changes what they imply; C1′, C2′, C5′, C8′
replace C1, C2, C5, C8.

**C1′. Asserted means multiplicity at least one; the state is counted.** The
seed says an assertion "is asserted a number of times" and, of `arb`, "is
asserted with multiplicity one"; G4 forbids `xrx` to be asserted. Reading:
"asserted" is "has multiplicity at least one", so a legal state gives every
`xrx` multiplicity zero, and "whether `bra` is asserted" is whether `bra` has
positive multiplicity. A state is: terms, a multiplicity for each ordered
pair of terms, names (`code/fourth/state.py`, Lean `MSt`). No other reading
was found that gives G3′ and G4 a meaning. This replaces 1:C1, whose unchosen
reading (multiplicity) the three earlier papers left open as O1; O1 is closed
by the seed, not by a choice.

**C2′. To begin with: the terms `a` and `b`; `arb` once; `bra` once or not at
all.** `arb` once is given (G3′). `bra`: the seed says only whether it is
asserted is not given; if asserted, its multiplicity is not said. Chosen:
multiplicity one, by the same wording as for `arb`. Unchosen: `bra` asserted
`k ≥ 2` times to begin with. Harmless: such a beginning is reached from the
beginning with `bra` once by adding `bra` `k − 1` times (D9, additions reach
everything containing the state), so it is one of that beginning's results,
and its own results — the legal states containing it — are among that
beginning's results; the reading moves the starting point and adds no result,
as the earlier C2 argued for further terms (2:C2, 3:C2; the argument is the
same with the path of D9).

**C3. No cap on the number of terms.** As 3:C3: no sequence of changes ever
has more terms than its last state (D5), so a cap `L ≥ 2` leaves every
statement about results with at most `L` terms unchanged; builds need one
term more than the state (D10); nothing is claimed for them under a cap.

**C4. Sameness, two readings, both kept.** FREE and ANCHORED as 1:C4, on
counted states: a rewriting of the terms carries each multiplicity along. All
computations are done under both.

**C5′. What is a change.** A new term comes with no assertion; an added
assertion is between terms already there (as 1:C5). Adding an assertion that
is asserted already *is* a change: by G2′ it raises the multiplicity by one,
so the outcome differs from the state. This replaces the clause of the earlier
C5 "adding what is asserted changes nothing, so it is not a change", which
the counted seed refutes (§7). Consequence: a state with `n` terms has
`1 + n²` changes (D3), not `1 + n² − m`.

**C6. Results and rounds.** As 3:C6: a result is a legal state up to
sameness; round `k` attempts every change on every result first reached in
round `k − 1`; a performed change counts one; a refused change is an attempt
of its round that changes nothing; the further changes of an answer count one
each. Both kinds add one, so "fewest additions first" does not order them;
each result's changes are attempted in the seed's order of kinds — a term,
then the assertions, pair by pair in the order of the writing. Unchosen: other
orders; an obstructed change and its answer counted as one. The order cannot
move a result to another round (D8); counting an answered change as one would
change rounds but not results (D10), as under the third seed.

**C7. Obstruction and answers.** As 3:C7, restated. The obstruction of a
change is the set of assertions that would become some `xrx`; under this seed
only adding `xrx` is obstructed (D3), and the obstruction is the one assertion
the change adds, raising its multiplicity from none to one. *Refuse*:
recorded, nothing changes. *Remove the obstruction*: two readings, both kept.
(i) Lower the multiplicity of `xrx` back to none after raising it, then the
change stands — no change lowers a multiplicity (D6), so this answer is
recorded as impossible on every obstructed attempt:
`"remove the obstruction": "impossible: the obstruction is the assertion the
change itself adds, raising its multiplicity from none to one; no change
lowers a multiplicity, and not adding it is refusal"`. (ii) Do not add it —
that is to withdraw the change, which coincides with refusal and adds no
result. *Build structure*: by additions, reach a legal state that stands for
the would-be outcome — read with the added terms as `x`, the multiplicities
of the pairs that become one pair adding up, it is exactly that outcome —
fewest additions first: add a term `t` and `xrt` or `trx` (D10). With
multiplicities counted the criterion is stricter than the third's: a build
that adds `xrt` and `trx` both stands for `xrx` twice, and a build that copies
an asserted `xry` as `try` stands for one `xry` more than the outcome has; so
exactly two builds add one term (D10), where the third seed had `3 · 2^d`.
Unchosen: any further additions at all count as a build; by D10 the results
are the same set under any reading in which the further changes are changes
of the two kinds. "Declare which" is read as in 1:C7: every answer is recorded
with its kind and all are kept; the seed does not fix one (N6).

**C8′. Bound on terms and on rounds.** Within any bound on terms the results
are infinite (D9: `arb` asserted `k` times is a result for every `k`), so a
bound on terms alone does not make a run finite, and the declared bound is on
terms and on rounds together. Three explorations per beginning and reading:
5 terms (FREE) or 4 terms (ANCHORED) with 8 rounds; 3 terms with 12 rounds;
2 terms — the given terms only — with all 100 rounds, the only setting in
which the seed's 100 rounds complete. Under ANCHORED a counts-only census at
5 terms with 8 rounds. Full attempt logs at 2 terms and 6 rounds;
reachability at 3 terms and 6 rounds, which holds every result of the third
seed within 3 terms. The frontier has two parts: the attempts whose outcome or
answer has more terms than the bound (exported as before), and the results of
the last round, whose changes await the next round (listed in the results
file with their round; `changes_attempted = 0`). Within the bound the
exploration is complete (D14).

**C9.** `r` writes assertions, not terms.

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. `a` and `b` are two terms.** If they were one, `arb` with positive
multiplicity would be `xrx`. Lean: `names_apart_of_legal`, which is the first
derivation's `given_distinct` applied to the relation "has positive
multiplicity" (1:D1, no change: `given_distinct` mentions no multiplicity).

**D2. The beginnings.** On the terms `a`, `b` alone, a legal counted state
containing what is given asserts `arb` `i ≥ 1` times and `bra` `j ≥ 0`
times, and every such pair `(i, j)` is one: infinitely many, of which
`K (K + 1)` have no multiplicity above `K` (computed for `K = 3`: 12,
`given.json`), and exactly two assert nothing twice — `arb` only, or `arb`
and `bra`, the earlier derivations' two states (`two_states_on_given_terms`,
`two_states_differ`, 1:D2, no change on the supports; they no longer count
all states on the given terms, §7). The two beginnings (C2′) are these two.
The one without `bra` reaches the one with it by adding `bra`:
`givenA4_to_givenB4` (3:D2's `givenA_to_givenB2`, re-proved). The other
direction is impossible, by size: `givenB4_never_givenA4` (R8).

**D3. Which attempts are obstructed; how many changes a result has.** An
attempt (`Try4`: a new term, or `xry` between terms that are there, `xrx`
included, asserted already or not) makes some `xrx` asserted exactly when it
adds some `xrx` — adding a term or `xry` with `x ≠ y` leaves every `xrx` at
multiplicity zero: `Try4.obstructed_iff`, `Try4.legal_iff`,
`Try4.step4_or_xrx`, `addTerm_unobstructed4`,
`addAssertion_again_unobstructed` (3:D3 re-proved on counted states; the new
clause is that re-adding is unobstructed). So a result with `n` terms has
`1 + n²` changes — a term, every ordered pair — of which the `n` additions
of some `xrx` are obstructed, whatever it asserts (C5′; computed:
`attempts_equal_formula_1_plus_n_squared`, `obstructed_equal_formula_n` true
in every run). The third's `1 + n² − m` does not survive (§7).

**D4. Adding `xrx` is obstructed in every state and after every sequence of
changes.** `adding_xrx_always_obstructed4`, `Reach4.xrx_still_obstructed`
(1:D4, 3:D4 re-proved: the outcome gives `xrx` multiplicity one).

**D5. Containment with multiplicities.** A change adds a term or raises one
multiplicity by one and takes nothing away, so every term and both names of a
state are in place in its outcome and every multiplicity is the same or
higher (`Contains4`): `Step4.contains`; containment composes
(`Contains4.trans`), so `Reach4.contains`; and it is one-way: two states
contained in each other are the same state, since multiplicities equal both
ways are equal (`Contains4.antisymm`). Through the maps: a counted
containment gives the third's containment of the supports (`Contains4.toSt`),
a containment of earlier states gives a counted containment of the
indicators (`Contains.ofSt`), and on states asserting nothing twice the two
are the same (`contains4_of_toSt`, `contains4_iff_contains`). 3:D5 survives
through the maps and is re-proved in the stronger form.

**D6. What is given survives; nothing decreases.** Along every sequence of
changes every term persists (`Reach4.term_persists`), every multiplicity is
the same or higher (`Reach4.mult_le`), whatever is asserted stays asserted
(`Reach4.asserted_persists`), the names are unchanged (`Reach4.name_a`,
`Reach4.name_b`), `a` and `b` stay two terms (`Reach4.names_apart`), `arb`
stays asserted with at least its multiplicity (`Reach4.arb_persists`,
`Reach4.arb_mult_le`) and so does `bra` if asserted (`Reach4.bra_persists`),
every result has at least two terms (`Reach4.two_terms`,
`reach4_givenA_two_terms`, `reach4_givenB_two_terms`), the number of terms and
the total multiplicity never decrease (`Reach4.card_T_le`,
`Contains4.total_le`, `Reach4.total_le`), and every result is legal, well
formed and finite (`Reach4.legal`, `Reach4.wf`, `Reach4.nonempty`). Computed:
`counts_lowered_by` empty on every unobstructed change within the bound of
every run (§6), `additions_never_negative` true. 3:D6 survives: its
statements about which assertions are asserted are the support form, and the
counted form is new (no multiplicity decreases). The second derivation's
counts-can-decrease (2:N8) stays refuted.

**D7. An obstruction is never cleared; no change lowers a multiplicity.**
Whatever is asserted stays asserted (`Reach4.obstruction_persists`); no state
reached from a legal state asserts any `xrx` (`no_change_asserts_xrx4`), so
the would-be outcome of an obstructed attempt is unreachable
(`xrx_outcome_unreachable4`); no multiplicity is ever lowered (D6,
`Reach4.mult_le`). So "remove the obstruction" is impossible under reading
(i) of C7 (R3). 3:D7 survives, re-proved with multiplicities.

**D8. Every sequence to a result has the same length: the size difference,
multiplicities counted.** Let the size of a state be its number of terms
plus the sum of its multiplicities (`MSt.size`). Adding a term raises it by
one (`size_addTerm`) and so does raising a multiplicity (`size_addAssertion`):
`Step4.size_eq`; a sequence of `n` changes raises it by exactly `n`
(`Reach4.size_eq`), so any two sequences between the same two states have the
same length (`Reach4.length_unique`). From what is given (size 3, or 4 with
`bra`: `size_givenA4`, `size_givenB4`) every sequence to a result has length
`size − 3` or `size − 4` (`fewest_changes4_lower_A`, `_B`), and one exists
(`fewest_changes4_upper_A`, `_B`, from D9's path): `fewest_changes4_A`,
`fewest_changes4_B`; for every writing of what is given,
`fewest_changes4_every_writing_A`, `_B`. So the round of a result is its size
difference and does not depend on the order of attempts (C6). Computed:
`round_equals_cost_formula_for_every_result` true in every run and census;
`round_not_raised_by_one` empty; the FREE closed form agrees with the best
placement of the names on every legal state with at most 3 terms and no
multiplicity above 2 (`free_cost_closed_form_checked_on`). **The cost
survives**: on states asserting nothing twice the size is the size of the
support (`size_toSt`, `size_ofSt`), so 3:D8's formula `terms + assertions −
size(given)` is this one with each assertion counted once; with multiplicities
the same formula holds with `assertions` read as their sum. The second
derivation's `additions_count` and the third's `Step2.size_eq` are the
support forms (through the maps).

**D9. The results are the legal states containing what is given,
multiplicities compared one by one; the third's results are those asserting
nothing twice.** Necessity: whatever is reached from what is given is legal,
well formed, keeps `a`, `b` two terms and asserts `arb` (and `bra` if given)
(`reach4_givenA_contains`, `reach4_givenB_contains`, from D6). Sufficiency:
a legal, well-formed state containing a state is reached from it by adding
the missing terms, then raising each multiplicity as often as it falls short
(`reach4_addTerms`, `reach4_raise` — induction on the total that falls short:
if it is zero the states are the same, else some pair falls short and raising
it is an unobstructed change, since a pair with `x = y` cannot fall short of a
legal state; `reach4_by_additions`, `reach4_of_contains`). For every writing:
`result4_iff_A`, `result4_iff_B` — a state is reached from some writing of
what is given exactly when it is legal, well formed, keeps `a` and `b` two
terms and asserts `arb` (and `bra`, if given). Under FREE, "some writing
contains what is given" is "some pair has positive multiplicity" (without
`bra`) or "some pair has positive multiplicity both ways" (with `bra`), as in
3:D9 (paper §4 there; the argument mentions only whether a pair is asserted).
The set is infinite within any bound on terms: `arb` `k` times is a result for
every `k` (round `k − 1`). **The results survive and extend.** Every result
of the third seed is a result of the fourth, its indicator, in the same number
of changes (`results_extend`, `results_extend_B`); a well-formed state
asserting nothing twice is a result of the fourth exactly when its support is
a result of the third, in the same number of changes (`reach4_givenA_iff`,
`reach4_givenB_iff`); and the fourth has results the third has not
(`arb_twice_result`: `arb` twice, round 1, asserts something twice). Computed:
in every run and census the results asserting nothing twice, their rounds and
their sequence counts are exactly the third's exploration's at the same bound
and rounds (`same_results_and_rounds_as_third_derivation`,
`same_sequence_counts_as_third_derivation`); and every result is one of the
independent count (`explored_equals_independent_count`, D14). 3:D9 survives
through the maps; its necessity is re-proved with multiplicities; 2:K1's
counts are the simple part of K1 (computed again, `counts.csv`).

**D10. Answers.** Every answer is refusal (nothing) or a build of two
additions: a term `t` and `xrt` or `trx` (`build_answer4`,
`build_answer4_reverse`; 3:D10 re-proved). Exactly two builds add one term:
the would-be outcome of adding `xrx` gives `xrx` multiplicity one and leaves
every other multiplicity as it is; reading the added term `t` as `x` sends
`xrt`, `trx` and `trt` to `xrx`, `try` to `xry` and `yrt` to `yrx`, with
multiplicities adding up; so the multiplicities of `xrt`, `trx`, `trt` add up
to one (and `trt` is illegal), and every `try`, `yrt` has multiplicity zero:
`xrt` alone or `trx` alone (`one_term_builds`; computed: of every candidate
with one added term and no multiplicity above 2 on the beginnings, exactly
these two are builds, `tests/test_fourth_changes.py`; `given.json`,
`one_term_builds: 2`). The first derivation's `build_gives_back`,
`build_needs_term_and_assertion` are the support forms (they mention the
earlier states; through the maps on states asserting nothing twice). Answers
reach nothing the changes do not reach: every answer is nothing or two
additions, so its result is a result of the exploration, reached no later
than the round of the state plus two (computed: `answers_reaching_something_new`
empty in every run); every result is reached by additions
(`reach4_by_additions`); no answer removes the obstruction
(`answers_removing_the_obstruction: 0`).

**D11. Changes commute with one-to-one rewriting; sequences keep their
length.** `rename4`, `Step4.rename`, `Reach4.rename`, with `size_rename4`,
`legal_rename4`, `wf_rename4`, `simple_rename4`, `rename4_symm_apply` (3:D11
re-proved on counted states; the third's lemmas are about the earlier states
and are not reused).

**D12. Reachability is containment, up to rewriting an embedding.** A legal,
well-formed state is reachable from a well-formed state exactly when it
contains it (`reach4_iff`, `reach4_of_contains`, D5, D9); up to rewriting,
exactly when it contains some writing of it (`reach4_iff_some_writing`).
Computed: an embedding — a one-to-one map of the terms carrying the names and
each multiplicity to one at least as large (`embedding`) — is found exactly
when a breadth-first search within the bound finds a sequence, on every
ordered pair of results within 3 terms and 6 rounds, in all four runs
(`embedding_agrees_with_search`, §6). **The criterion survives**: on states
asserting nothing twice it is the third's — counted containment is
containment of the supports (`contains4_iff_contains`), and reachability
under the fourth seed is reachability under the third, in the same number of
changes (`reach4_iff_reach2`; 3:D12's `reach2_iff` through the maps).
Computed: on every ordered pair of results asserting nothing twice, the
third derivation's reachability agrees with this seed's
(`third_derivation_agrees_on_every_pair_asserting_nothing_twice` true in all
four runs). The new pairs are those where a multiplicity of the target
exceeds one: `a b; arb` reaches `a b; arb(2)`, never the reverse.

**D13. Reachability is one-way; the fewest classes of a split never
decrease.** Reached both ways means zero changes and the same state
(`Reach4.antisymm`); a state once left is never returned to
(`Reach4.no_return`); up to rewriting, `reach4_antisymm_writing`. Only what
is given reaches what is given (computed: `results_that_reach_what_is_given:
1` in every run). **One-way reachability survives**: on states asserting
nothing twice it is the third's `Reach2.antisymm` and it holds for all
counted states (`antisymm_survives`). The fewest classes of a split of the
support (no two related terms in one class; relatedness does not see
multiplicity) never decrease along changes (`Reach4.split_mono`, through
`Contains4.toSt` and the second derivation's `Carries.split`; computed:
`fewest_classes_lowered_by` empty in every run).

**D14. Within the bound the exploration is complete; the frontier is exact;
the sequence counts are exact.** *Completeness.* Every legal state containing
what is given with at most `N` terms and size at most `size(given) + R` is
reached by a sequence of additions whose states all have at most `N` terms
and size at most its own (D9's path only adds), hence within the bound on
terms and rounds; so the exploration, which attempts every change on every
result of round `< R`, reaches it in round `size − size(given) ≤ R` (D8).
The results with `n` terms and total multiplicity `t` are counted
independently by the orbit method with a series per cycle (K1): a rewriting
of the terms fixes a counted state exactly when the multiplicity is constant
along each cycle of its action on ordered pairs, so the fixed states with
total `t` are the coefficient of `x^t` in a product of `1 / (1 − x^L)` over
the pair cycles of length `L` — with `x / (1 − x)` for `arb`, whose
multiplicity is positive, and likewise `bra` if given (names kept); without
names, the states with some positive multiplicity are all but the empty one,
and those with a pair positive both ways are all minus those with no such
pair, the latter counted by `(1 + x^L) / (1 − x^L)` per cycle of unordered
pairs that can carry one direction and `1` per cycle that turns a pair
around (`code/fourth/orbits.py`; the cycle-length machinery is 1:K1's,
`partitions`, `class_size`, `pair_cycles`, no change). The explored counts by
terms and total multiplicity equal the independent counts in every run and
census (`explored_equals_independent_count`). *Frontier.* An attempt leaves
the bound on terms exactly when it is "add a term" on a result with `N` terms
or a build of an obstructed change on such a result (`1 + 2N` entries per
such result whose changes were attempted, computed:
`frontier_entries_are_1_plus_2N_per_state_with_N_terms`); the results of
round `R` are the second part (`results_of_the_last_round_whose_changes_await`,
`changes_awaiting`). *Sequences.* A sequence to a result within the bound
never has more terms or more changes than the result, so the count of
sequences by dynamic programming over the explored results is exact (K7).
*Rounds.* The number of results of round `r` with no bound on terms is the
number of results of size `size(given) + r`, summed over the possible numbers
of terms (`layer_counts`); rounds `0 … N − 2` of a run within `N` terms agree
with it (`rounds_agreeing_with_unbounded_formula`). 3:D14 survives with the
bound on rounds added; the counting is new.

**D15. With `bra` given, passing on and "never both ways" hold in no
result.** `bra` persists (`Reach4.bra_persists`), and `arb` with `bra` and
passing on would give `ara` (`passing_on_refutes_bra` on the relation "has
positive multiplicity"; 1:R7, no change). Computed:
`follows_*_with_bra.csv` (no `first_holds` for `passes_on`,
`both_ways_never`).

**D16. A result reached by two different sequences.** `a b c; arb bra` by
adding the term first or `bra` first (`two_sequences4`, the third's witness on
indicator states), and — new, with the given terms only — `a b; arb(2) bra`
by adding `arb` first or `bra` first (`two_sequences_counted`); of the same
length (`Reach4.length_unique`). Computed: column `sequences_of_changes`, 2
for both.

**D17. Two terms: the results of every round and the sequences to each, in
closed form.** With the given terms only (names kept, `bra` not given) the
results of round `r` are the states `arb` `1 + i` times, `bra` `j` times with
`i + j = r`: `r + 1` of them, `5 151` in 100 rounds; with `bra` given, `arb`
`1 + i`, `bra` `1 + j`: `r + 1` again. Without names (FREE) the two
multiplicities are unordered: `⌊(r + 1) / 2⌋ + 1` results without `bra`
(`{1 + i, j}` with `i + j = r`, `u + v = r + 1` up to order) and `⌊r / 2⌋ + 1`
with `bra`. The number of sequences reaching `(1 + i, j)` from what is given
is `C(i + j, i)`: a sequence is a word of `i` additions of `arb` and `j` of
`bra`, in any order, and different words are different sequences (each
addition raises one multiplicity, so the word is read off the sequence). So
the sequences of round `r` add up to `2^r`, and those of 100 rounds to
`2^101 − 1`. Computed on all 100 rounds of all four two-term runs
(`two_term_sequences_equal_binomial`, `rounds_bound2_rounds100_*.csv`,
`tests/test_fourth_explore.py::test_two_terms_all_rounds`).

**D18. Names kept, the exploration with `bra` given is the exploration
without it with `bra` added once throughout.** Let `+bra` send a counted
state with names to the state with the multiplicity of `bra` raised by one.
It sends a result of the beginning without `bra` of round `r` to a result of
the beginning with `bra` of round `r` (the state still contains what is
given, now with `bra`; its size rises by one and so does the size of what is
given, D8, D9); it is one-to-one; and it is onto, since a result of the
beginning with `bra` asserts `bra` at least once (D6) and lowering it by one
leaves a legal state containing `arb`, a result of the other beginning (D9).
It commutes with every change: raising a multiplicity or adding a term
commutes with raising `bra`, and the same pair is obstructed on both sides.
So the changes attempted, their outcomes, the rounds and the sequences of the
two explorations correspond one to one, and every count agrees. Under the
third seed `+bra` is not defined on a result that asserts `bra` already, and
the counts differed (3:K1: 1 090 against 545 at 4 terms); under FREE a
rewriting may swap `a` and `b`, and the counts differ (§6). Computed: the
same number of results in every round and the same sequence totals in every
ANCHORED pair of runs and in the census (§6). Not in Lean; the proof is the
one above.

## 5. What does not follow

Each item has two legal witnesses among the results, or a proof.

**N1. `bra`. N2. Not `bra`.** Both beginnings are legal and contain what is
given. Lean: `bra_not_refuted`, `bra_not_derived` (1:N1, 1:N2, no change: the
relation "has positive multiplicity" is one).

**N3. Anything on which the two beginnings differ, from the beginning without
`bra`.** "Never both `xry` and `yrx`": holds in what is given, fails after
adding `bra` (round 1). "Whenever `xry` and `yrz` then `xrz`": holds
(vacuously), fails after adding `bra`. "Every term is first in some
assertion": fails in what is given, holds after adding `bra`. "Whenever `xry`
then `yrx`": fails, then holds. (`follows_*_without_bra.csv`; 3:N3, computed
again on the supports.) From the beginning with `bra` the first two are
refuted in every result (D15) and the last two are independent.

**N4. That there are exactly two terms.** Holds in what is given, fails after
adding a term (3:N4, computed again).

**N5. Anything about the asserting that is not true of every legal state
containing what is given.** By D9 every such state is a result. Of the
nineteen statements tested (the earlier fifteen on the support, `arb` once,
and three about multiplicity), those holding in every result within the bound
are exactly "no `xrx`", "at least one term", "at least two terms", "something
is asserted", and with names "`arb` is asserted", "`a` and `b` are two terms",
plus "`bra` is asserted" when `bra` is given; each is proved for all results
(D6). Every other statement has a result where it holds and one where it
fails, except the two of D15 under the beginning with `bra` (3:N5, computed
again; the multiplicity statements are new, N11, N12).

**N6. Which answer an obstructed change gets.** Refusal is always possible;
removal never, or is refusal (R3, C7); a build always (adding a term is never
obstructed, D3). No result needs a build, and no result needs an obstructed
change to be attempted at all (D10). "Must be answered" does not determine
the answer.

**N7. Growth.** Nothing forces terms to be added: what is given adds no term,
and one change gives a result that adds one; nor assertions: one change gives
a result that adds a term only. Every result is finite (D6); whether terms or
multiplicities can grow without end is not given (C3), though every round has
a new result (D9).

**N8. That any two results are comparable — that one reaches the other.**
`a b c; arb`, `a b; arb bra` and `a b; arb(2)`, the three results of round 1
(names kept, no `bra`), reach none of each other (none contains another;
`reach_bound3_rounds6_*.csv`), while what is given reaches all three.
Reachability is one-way (D13) but not total.

**N9. That a result is reached by one sequence only, or that results of one
round are reached by equally many.** What is given is reached by one sequence
(the empty one), `a b; arb(2)` by one, `a b; arb(2) bra` by two (D16),
`a b c; arb arc` by one and `a b c; arb bra` by two (the last three all of
round 2); with two terms the count is `C(i + j, i)` (D17). Column
`sequences_of_changes` of `results_*.csv` (K7).

**N10. That the number of attempts on a result is the same for results of
one round.** It is `1 + n²` (D3): 10 for `a b c; arb` and 5 for
`a b; arb bra`, both of round 1. It no longer depends on what is asserted, so
results of one round with equally many terms have equally many attempts —
which does follow (D3), unlike under the third seed (3:N10).

**N11. That nothing is asserted twice; that `arb` is asserted exactly once.**
Both hold in what is given and fail after one change, adding `arb`
(`arb_twice`, `arb_twice_result`; `follows_*.csv`, statements `nothing_twice`,
`arb_once`). The opposite, that something is asserted twice, fails in what is
given and holds after that change. So the multiplicity of `arb` is given as
one to begin with and is not kept.

**N12. That all asserted assertions are asserted equally often; that `xry`
and `yrx`, when both asserted, are asserted equally often.** Both hold in
what is given and in `a b; arb bra`, and fail in `a b; arb(2) bra`
(`same_multiplicity`, `both_ways_equal` in `follows_*.csv`).

**Refuted** (each a proved impossibility): `a` and `b` one term to begin with
(R1, D1); an answer that makes adding `xrx` performable (R2, D4); removing the
obstruction of any obstructed change — lowering a multiplicity by any change
(R3, D7); a result with fewer than two terms, in particular the one-term
state (R4, D6, `oneTerm_unreachable4_A`, `oneTerm_unreachable4_B`);
identifying `a` and `b`, or lowering the multiplicity of `arb`, ever (R5,
D6); an answer that reaches a result additions do not reach (R6, D10); `bra`
together with passing on, and, with `bra` given, passing on in any result
(R7, D15); the beginning with `bra` reaching the beginning without (R8, D2);
a result that does not contain what is given (R9, D9); a sequence of changes
to a result whose length is not the size difference (R10, D8); a change that
lowers the fewest classes (R11, D13); a change that lowers the number of
terms, the total multiplicity or any multiplicity, or that leaves the size
where it was or raises it by more than one (R12, D6, D8); a result returned
to after being left, and any result other than what is given that reaches
what is given (R13, D13); two different results reachable from each other
(R14, D13); a third one-term build for an obstructed `xrx`, or a one-term
build that copies an assertion of `x` (R15, D10).

## 6. The exploration

**Protocol.** From each beginning, under each reading of sameness (four
combinations): round by round, every change on every result first reached in
the round before (C6), each result's changes in the seed's order of kinds —
adding a term, then every ordered pair of terms in the order of the writing,
`xrx` included, asserted already or not (`1 + n²` changes). Refusal and every
build are recorded for every obstructed attempt, with the declaration that
removing the obstruction is impossible (C7); the exploration spreads along
unobstructed changes and checks the answers afterwards (D10). Three
explorations per combination (C8′): the main run (5 terms under FREE, 4 under
ANCHORED, 8 rounds), a deeper run (3 terms, 12 rounds), and the two-term run
(the given terms only, all 100 rounds). Beside every run the third
derivation's exploration is made at the same bound and rounds and compared
on the results asserting nothing twice (D9). Files per run
(`evidence/fourth/`, tag `bound{N}_rounds{R}_{reading}_{beginning}`):
`results_*.csv` (one row per result: terms, assertions counted and asserted,
largest multiplicity, additions to what is given, round, cost by formula,
fewest classes, changes and obstructed changes, whether its changes were
attempted, sequences reaching it, whether it reaches what is given, whether
it asserts nothing twice), `added_*.csv`, `frontier_*.csv`, `rounds_*.csv`,
`follows_*.csv`; per combination `reach_bound3_rounds6_*.csv` and the full
attempt log `attempts_bound2_rounds6_*.jsonl`; `counts.csv`, `given.json`,
`summary.json` (every check, per run), `lean_axioms.txt`, `MANIFEST.sha256`.

**Results within the bound** (K1, K2). Every check of every run passes
(`summary.json`; `python code/generate_fourth.py` prints one line per run).

| run | results | by terms | asserting nothing twice (the third's) | sequences (total) | reached by one sequence |
|---|---|---|---|---|---|
| FREE, no `bra`, 5 terms, 8 rounds | 5 010 | 29 / 519 / 2 214 / 2 248 | 803 | 20 633 666 | 15 |
| FREE, `bra`, 5 terms, 8 rounds | 8 594 | 25 / 655 / 3 720 / 4 194 | 1 077 | 20 633 666 | 4 |
| ANCHORED, no `bra`, 4 terms, 8 rounds | 11 157 | 45 / 1 716 / 9 396 | 798 | 8 238 149 | 47 |
| ANCHORED, `bra`, 4 terms, 8 rounds | 11 157 | 45 / 1 716 / 9 396 | 454 | 8 238 149 | 47 |
| FREE, no `bra`, 3 terms, 12 rounds | 3 195 | 55 / 3 140 | 17 | 653 040 844 | 17 |
| FREE, `bra`, 3 terms, 12 rounds | 4 058 | 49 / 4 009 | 10 | 653 040 844 | 2 |
| ANCHORED, no `bra`, 3 terms, 12 rounds | 12 467 | 91 / 12 376 | 34 | 653 040 844 | 70 |
| ANCHORED, `bra`, 3 terms, 12 rounds | 12 467 | 91 / 12 376 | 17 | 653 040 844 | 70 |
| FREE, no `bra`, 2 terms, 100 rounds | 2 651 | 2 651 | 2 | 2^101 − 1 | 102 |
| FREE, `bra`, 2 terms, 100 rounds | 2 601 | 2 601 | 1 | 2^101 − 1 | 1 |
| ANCHORED, no `bra`, 2 terms, 100 rounds | 5 151 | 5 151 | 2 | 2^101 − 1 | 201 |
| ANCHORED, `bra`, 2 terms, 100 rounds | 5 151 | 5 151 | 1 | 2^101 − 1 | 201 |

In every run the results asserting nothing twice, with their rounds and
their sequence counts, are exactly the third derivation's exploration's at
the same bound and rounds (`same_results_and_rounds_as_third_derivation`,
`same_sequence_counts_as_third_derivation`; 3:K1, 3:K2, 3:K7 computed
again): 798 and 454 are the third's counts at 4 terms within 8 rounds, 34 and
17 its complete counts at 3 terms (3:K1's 2 + 32 and 1 + 16), and the
two-term runs hold its two and one results on the given terms. Every count by
terms and total multiplicity equals the independent count by series
(`explored_equals_independent_count`, D14, K1), and every result's round is
its size difference (`round_equals_cost_formula_for_every_result`, D8).

**Rounds** (K2). ANCHORED, no `bra`, 4 terms
(`rounds_bound4_rounds8_anchored_without_bra.csv`): new results per round
1, 3, 10, 32, 104, 321, 959, 2 682, 7 045; asserting nothing twice 1, 2, 6,
16, 40, 90, 171, 236, 236 (the third's, which is complete from round 7 on);
without any bound on terms 1, 3, 10, 33, 112, 379, 1 327, 4 724, 17 273
(`layer_counts`, D14) — rounds 0 to 2 agree with the run, as every round up
to `N − 2` must. FREE, no `bra`, 5 terms: 1, 3, 8, 20, 53, 138, 393, 1 118,
3 276 within the bound against 1, 3, 8, 20, 54, 145, 424, 1 275, 4 039
without. With two terms, names kept, round `r` has `r + 1` new results
(D17): 1, 2, 3, …, 101; without names `⌊(r + 1) / 2⌋ + 1` (no `bra`) and
`⌊r / 2⌋ + 1` (`bra`). Every round of every run has a new result
(`last_round_with_a_new_result` is the last round run).

**Attempts** (K3). Changes attempted and obstructed per round are in
`rounds_*.csv` (`changes_attempted_so_far`, `of_which_obstructed`): 63 004
and 15 452 in the ANCHORED 4-term run, 5 and 2 in round 1 of every run (the
five changes of the beginning: a term, `ara`, `arb`, `bra`, `brb`). The totals
equal `1 + n²` and `n` summed over the results whose changes were attempted
(D3) in every run. The two-term runs attempt 5 changes on each of the 5 050
results of rounds 0 to 99 (names kept): 25 250 attempts, 10 100 obstructed,
the same 25 250 frontier entries (every "add a term" and every build leaves
the bound of two terms).

**Frontier** (K4). Every result with `N` terms whose changes were attempted
has `1 + N` attempts leaving the bound on terms — "add a term", and the `N`
obstructed additions' two builds each, `1 + 2N` entries
(`frontier_entries_are_1_plus_2N_per_state_with_N_terms` true in every run):
3 152 such results and 28 368 entries in the ANCHORED 4-term run, 567 and
6 237 in the FREE 5-term run. The second part of the frontier, the results of
the last round whose changes await the next round: 7 045 results and
114 113 changes (ANCHORED, 4 terms), 3 276 and 69 207 (FREE, 5 terms), 4 381
and 43 745 (ANCHORED, 3 terms), 101 and 505 (two terms, names kept).

**Results by what they add to what is given** (K5;
`added_bound4_rounds8_anchored_without_bra.csv`). Additions of terms and of
assertions (counted with multiplicity) never come out negative; every result
of round `r` adds exactly `r` things (D8). With 0 terms added the results of
round `r` are `r + 1`; with 1 term added `C(r + 4, 5)`: 1, 6, 21, 56, 126,
252, 462, 792 for `r = 1 … 8` (a term and `r − 1` units of multiplicity over
6 pairs; the third's row was 1, 6, 15, 20, 15, 6, 1 — the subsets); with 2
terms added 1, 7, 43, 189, 700, 2 212, 6 244 for `r = 2 … 8`.

**Statements that hold in every result** (K6; `follows_*.csv`). Of the
nineteen statements tested (N5), those holding in every result within the
bound are, names kept: `arb` is asserted; `a`, `b` are two terms; something
is asserted; at least one term; at least two terms; no `xrx`; and `bra` is
asserted when given. Each is proved for all results (D6). The four
multiplicity statements — nothing twice, something twice, all asserted
equally often, both ways equally often — hold in some result and fail in
another in every run (N11, N12); `arb` exactly once holds in what is given
and fails in round 1.

**Sequences** (K7). Column `sequences_of_changes`; the totals in the table.
Two terms: `C(i + j, i)` per result and `2^r` per round (D17); 201 of the
5 151 results (names kept) are reached by one sequence only — the 101 with
`bra` never added and the 100 with `arb` never re-added, what is given
counted once. With 3 terms and 12 rounds the FREE and ANCHORED totals agree
(653 040 844), as they did for the third seed (3:K7): the sequences are the
same, only the results are gathered differently. The third's totals 393 and
66 at 3 terms are the sums over the results asserting nothing twice
(`tests/test_fourth_explore.py`).

**Reachability within 3 terms and 6 rounds** (K8;
`reach_bound3_rounds6_*.csv`, `summary.json` `reachability`). Every ordered
pair of results is tested by embedding and by search, and they agree
(`embedding_agrees_with_search`); no pair of different results is reachable
both ways (`unordered_pairs_reachable_both_ways: 0`); on every pair of
results asserting nothing twice the third derivation's reachability agrees
(`third_derivation_agrees_on_every_pair_asserting_nothing_twice`).

| reading, beginning | results | ordered pairs | reachable | pairs asserting nothing twice | of which reachable (the third's) | reachable with a multiplicity above one |
|---|---|---|---|---|---|---|
| ANCHORED, no `bra` | 490 | 240 100 | 7 685 | 1 156 | 294 | 7 391 |
| ANCHORED, `bra` | 490 | 240 100 | 7 685 | 289 | 98 | 7 587 |
| FREE, no `bra` | 184 | 33 856 | 3 162 | 289 | 117 | 3 045 |
| FREE, `bra` | 213 | 45 369 | 3 174 | 100 | 46 | 3 128 |

The column "of which reachable" is the third derivation's 3:K8 (294, 98,
117, 46) computed again on the same pairs. The file lists every reachable
pair with its embedding and every pair of results asserting nothing twice
with the third's verdict; a pair absent from it is unreachable with a
multiplicity above one on one side (the totals are in `summary.json`). One
result reaches what is given in every run (`results_that_reach_what_is_given:
1`, D13).

**With and without `bra`, names kept** (D18). The ANCHORED runs with and
without `bra` have the same number of results in every round (5 151, 11 157,
12 467; 20 654 in the census), the same attempts and the same sequence
totals, as D18 says they must; under FREE the counts differ (2 651 against
2 601 with two terms; 5 010 against 8 594 at 5 terms).

**Census** (ANCHORED, 5 terms, 8 rounds, counts only): 20 654 results
(45 / 1 716 / 9 396 / 9 497 by terms), 114 978 changes attempted, 25 447
obstructed, 1 999 frontier results with 21 989 entries, 14 543 results of
round 8 awaiting; every check passes, and the results asserting nothing twice
are the third's 3 750 (no `bra`) and 2 672 (`bra`) at 5 terms within 8
rounds.

**Independent counts** (K1; `counts.csv`): results with `n ≤ 5` terms by
total multiplicity `0 … 12` under the four combinations, beside the results
asserting nothing twice by number of assertions (the third's 3:K1, cited and
computed again). For instance with 3 terms, names kept, no `bra`: 1, 6, 21,
56, 126, 252, 462, 792, … results with total multiplicity 1, 2, 3, …
(`C(t + 4, 5)`), of which asserting nothing twice 1, 5, 10, 10, 5, 1, 0, …
(the subsets of the six pairs). Totals over `t ≤ 12` for `n = 2, 3, 4, 5`:
78, 12 376, 677 392, 14 189 998 (ANCHORED, no `bra`); 66, 8 008, 324 214,
5 047 199 (ANCHORED, `bra`); 48, 3 140, 113 839, 1 907 441 (FREE, no `bra`);
36, 2 694, 98 259, 1 571 497 (FREE, `bra`).

**What is given** (`given.json`): the two states on the given terms
asserting nothing twice, the 12 with no multiplicity above 3, the formula
`K (K + 1)`; every attempt on each beginning with its record (round 1: five
attempts, two obstructed, each with refusal and the two builds and the
declaration on removal; `raises_a_multiplicity_to` says which multiplicity an
addition raises and to what — 2 for "add `arb`"); the beginning without
`bra` reaches the beginning with it and the state with `arb` twice, neither
reaches back, and no beginning reaches the one-term state.

**Reproducibility** (K9, K10). `python code/generate_fourth.py` rewrites
every computed file of `evidence/fourth/` (about two minutes here);
`--check` regenerates into a temporary folder and compares byte for byte;
`MANIFEST.sha256` lists every file's hash. `python code/lean_report_fourth.py`
builds all four Lean libraries and rewrites `evidence/fourth/lean_axioms.txt`,
refusing if the build warns of `sorry` or a cited theorem depends on an axiom
other than `propext`, `Classical.choice`, `Quot.sound`. After this work the
first and second derivations' `--check` were re-run and matched; the third's
`--check` and the three earlier Lean reports were started in the same run but
that run was stopped by the environment for low memory before they finished
(`paper/fourth/change_log.md`, item 13), and they were not repeated. Their
inputs are unchanged: no file of `code/xry/`, `code/second/`, `code/third/`,
`lean4/H3V7N5QF/`, `lean4/Second/`, `lean4/Third/`, their tests or their
evidence differs from the branch's starting point (`git diff --stat`), and the
fourth's Lean report built all four libraries. Tests: 358 passed, four
derivations; line coverage 99.90 %, branch coverage 98.94 % of all of
`code/` (`python code/xry/gate.py coverage.json`); `mypy --strict` clean; the
prose watchlist clean, with every pinned hit of this paper in §9.

## 7. Alternatives: kept, or eliminated by proof

| Alternative | Kept / eliminated |
|---|---|
| `bra` asserted to begin with / not | both kept: computed under both; N1, N2 |
| `bra` asserted `k ≥ 2` times to begin with | eliminated as a starting point by D9 (a result of the beginning with `bra` once; adds no result); not computed separately |
| FREE / ANCHORED sameness | both kept: every file exists under both |
| removing the obstruction, reading (i) | eliminated: impossible (R3, D7) |
| removing the obstruction, reading (ii) | kept as a record: coincides with refusal, adds no result |
| a build with `xrt` and `trx` both, or with a copy of an assertion of `x` | eliminated as a build (R15, D10): it stands for something other than the would-be outcome; kept as a result (it is one, D9) |
| further readings of "build structure" | kept as to records; eliminated as to results (D10) |
| the other order of the two kinds; other orders of the pairs | not computed; same results and rounds (D8) |
| counting an answered change as one | not computed; same results (D10), rounds differ (C6) |
| a bound on terms alone | eliminated: the results within it are infinite (D9) |
| the third seed's states (asserted or not) as the state | eliminated by G2′: the outcome of adding an asserted assertion is not a state of that model (C1′) |

Earlier results that fail under the fourth seed, each with the reason: 1:C1,
2:C1, 3:C1 (asserted is yes or no) — replaced by the seed; 1:C5, 3:C5's
clause "adding what is asserted is not a change" — refuted by G2′
(`addAssertion_again_unobstructed`); 1:D2, 3:D2's "exactly two legal states
on the given terms contain what is given" — false: infinitely many (D2), the
two are those asserting nothing twice; 3:D3's count `1 + n² − m` of the
changes of a result — now `1 + n²` (D3); 1:D11, 3:D10's `3 · 2^d` one-term
builds — now 2 (D10, R15); 3:N10 (attempts differ within a round for results
with equally many terms) — no longer true for equally many terms (N10); 3:D14
(complete within a bound on terms) — needs the bound on rounds (D14); every
K-claim of the earlier derivations — computed again as the simple part (§6).
From the first and second derivations, everything the third listed in 3:§7
fails here for the same reasons (their removal and identification clauses
have no object). Everything else cited stands with the re-check given at its
citation, and survives the counting as said there.

## 8. Open

- O1 of the earlier papers (multiplicity) is closed: the seed gives it. In
  its place, what the earlier derivations chose is now refuted or superseded
  (§7).
- O2. Number of new results in rounds beyond the bound: given by the counting
  of D14 for any round (`layer_counts`, computed to round 20 in every
  `rounds_*.csv`; to round 100 for the two-term runs, D17); not listed.
- O3. Results beyond the declared bounds, listed: the frontier is exported
  (both parts); the census counts at 5 terms.
- O4. Other readings of "build structure": open as to records; closed as to
  results (D10).
- O5. A closed form for the number of sequences reaching a result with three
  or more terms: computed per result within the bound (K7); with two terms it
  is `C(i + j, i)` (D17).
- O6. A closed form for the number of results with `n ≥ 3` terms at round
  `r`: the series of D14 gives it for every `n` and `r` (a polynomial in `r`
  for each `n`), but no formula is written out.

## 9. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Directed multigraphs; the sub-multigraph order.** A counted state is a
  loopless directed multigraph (a multidigraph) with two marked vertices,
  the multiplicity of `xry` being the number of parallel arcs from `x` to
  `y`; a state asserting nothing twice is a plain digraph, and the support
  and indicator maps are the usual forgetful map and its section. Containment
  (D5) is the sub-multigraph relation with the marks fixed, and an embedding
  (D12) is an injective homomorphism that does not lower multiplicities. D12
  says reachability is the sub-multigraph order on marked loopless
  multidigraphs, a partial order on isomorphism classes (D13 is its
  antisymmetry); restricted to plain digraphs it is the third derivation's
  subgraph order (3:§9), which is the content of "the criterion survives".
- **Graded posets; multisets under the product order.** D8 says every
  maximal chain from what is given to a result has the same length, the
  difference in vertices plus arcs counted with multiplicity: the order is
  graded with rank `|V| + Σ multiplicities`, and the rounds are its rank
  levels. With the vertex set fixed the results form an up-set of the product
  order on `ℕ^{n(n−1)}` (the multisets of arcs), and with two vertices the
  order is the product order on `ℕ × ℕ` above `(1, 0)`; N8 is that a product
  of chains is not a chain. Dickson's lemma (every infinite set of multisets
  has two comparable elements) applies to the results with a fixed vertex
  set; it was not used.
- **Pólya enumeration with weights.** The independent count (D14) is
  Pólya's theorem for the action of the symmetric group on ordered pairs,
  with the figure-counting series `1/(1 − x)` (one figure of each weight, the
  multiplicity) instead of `1 + x` (present or absent): the cycle index
  evaluated at `Π 1/(1 − x^L)`; the marked pairs `ab`, `ba` get `x/(1 − x)`.
  The "no pair both ways" count is the same theorem for the induced action on
  unordered pairs with the series `(1 + x^L)/(1 − x^L)`. With two vertices the
  counts are the compositions of `r + 1` into two parts (`r + 1`) and, up to
  swapping, the partitions into at most two parts (`⌊(r + 1)/2⌋ + 1`), D17.
- **Lattice paths.** The sequences reaching the two-vertex result
  `(1 + i, j)` are the monotone lattice paths from `(0, 0)` to `(i, j)`,
  counted by the binomial coefficient `C(i + j, i)` (D17); the sequences of a
  round add up to `2^r`. With more vertices the count is the number of
  linear extensions of the order "an arc after both its endpoints" on a
  multiset of additions, computed but not in closed form (O5), as for the
  third seed.
- **Insertion-only edit distance on multigraphs.** When only insertions of
  vertices and of parallel arcs are allowed, every edit script between two
  structures has the same length, the size difference with arcs counted;
  D8 is that remark, and "the cost survives" is that counting the arcs does
  not change it on plain digraphs.
- **Irreflexive plus transitive gives asymmetric** (strict partial orders):
  `passing_on_refutes_bra`, as before (D15).
- **Independence by two models**: N1, N2, as before.

What appears to be specific to this seed: that the results, the reachability
criterion, the cost and one-way reachability all survive the counting and
extend to the counted states with the same Lean statements (D9, D12, D8,
D13; `Fourth/Compare.lean`), while what does not survive is exactly what
counted assertions as present or absent — the number of changes of a result,
the one-term builds, the finiteness within a bound on terms, the two states
on the given terms (§7); that a seed sentence ("`arb` with multiplicity one")
fixes a quantity that no result keeps (N11); that with the given terms only
the seed's 100 rounds complete and every quantity has a closed form (D17);
that exactly two builds add one term where the third seed had `3 · 2^d`
(D10); and that, names kept, the exploration with `bra` given is the
exploration without it with `bra` added once throughout (D18).
