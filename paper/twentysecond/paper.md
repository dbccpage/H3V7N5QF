# Two relations, nothing given, and a pair asserted in both relations taken out: what follows

Twenty-second derivation. Input: `prompt/twentysecond/seed_prompt.md`. Task:
`prompt/twentysecond/prompt.md`. Claim IDs refer to
`paper/twentysecond/claim_ledger.md`; an ID written `9:D4` refers to the ninth
derivation's ledger (`paper/ninth/claim_ledger.md`, paper `paper/ninth/paper.md`),
`7:D11` to the seventh's, `8:C4` to the eighth's, `1:C4` to the first's — the
ninth is the parent, and the seventh, the eighth and the first are cited through
it; no other derivation is read. Lean names without a namespace are in the
namespace `Twentysecond` of the new package `lean4_core/` (library
`Twentysecond`, no `require`, toolchain `leanprover/lean4:v4.33.1`); it imports
nothing from `lean4/`, and re-proves what it uses. The axiom report for every
theorem of the library is `evidence/twentysecond/lean_axioms.txt`: all 210
theorems rest on `propext` and `Quot.sound` at most, and many on neither.
Computed files are in `evidence/twentysecond/`, written by
`python code/run_twentysecond.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent or ambiguous; the
unchosen readings are listed), **derived** (proved), **computed** (output of
`code/`), **refuted** (proved impossible), **open**.

Where a result of an earlier derivation is used it is cited, and the ledger's
re-check column says how its proof was checked from this seed: *no change*
(the statement is about states and changes, which this seed does not touch, or
mentions no sameness of results), *re-proved* (proved afresh in `lean4_core/`
or here for this seed's results), or *computed again* (the earlier derivation's
exploration is re-run beside this one and compared).

## 0. Findings in brief

1. The seed is the ninth's with one sentence changed: two results that differ
   only by an `xry` and an `xsy` asserted together are also the same result.
   States, the empty beginning and the four kinds of change are the ninth's;
   only *when two states are one result* changes.
2. **Sameness.** The sameness the changed sentence generates is exactly: equally
   many terms and, after one rewriting of the terms, the same *excess*
   `M_r(x, y) − M_s(x, y)` at every ordered pair (D1; `gen_iff_same`,
   `same_iff_excess`, `genW_iff_sameW`). Every result has one *plain state* up to
   writing — at every pair at most one relation asserts — and a result is an
   excess function (a whole number of either sign at each ordered pair) on its
   terms, up to rewriting.
3. **In the ninth no addition undoes an earlier addition; here one does.**
   In the ninth every addition raises the size by one and the ninth's sameness
   keeps the size, so a non-empty run of additions never returns to its start's
   result, in any writing (D5; `ninth_additions_never_return_every_writing`).
   Here adding `xry` and then `xsy` returns to the result before both
   (`addition_undoes_addition`) — the start and the two outcomes are three
   different ninth results (`addition_undoes_not_in_ninth`). On every state, adding `xsy` has the
   result of removing `xry` (`same_remove_add_partner`). At a fixed writing two
   additions in a row return exactly when they are one pair in the two relations
   (`two_additions_return_iff`); after a rewriting other pairs can too
   (`given.json`).
4. **Fewest changes.** The fewest changes from what is given to a result is
   `n + Σ |excess|` — the terms plus the assertions of its plain state, which is
   the ninth's cost of the plain state (D4; `fewest_changes`,
   `fewest_changes_every_writing`). The ninth's size of any other state of the
   result exceeds it by twice the pairs that state asserts together
   (`size_eq_phi_add_together`). A shortest sequence is additions only, never
   adds both relations at one pair, and every state along it is plain
   (`shortest_additions`, `shortest_all_plain`). Every change changes the parity
   of the cost (`Step.phi_parity`), so no change keeps a result in its round and
   none returns to its own result (`Step.not_same`); the ninth's "every change
   moves the cost by exactly one" fails: an identification can lower it by any
   odd number (D6).
5. **Which changes lower what is recorded, and by how much** (D6). What is
   recorded for a result is read on its plain state: its terms, its assertions
   in `r`, in `s` (reading C-R). Adding a term: never lowers (terms `+1`).
   Adding `xqy`: lowers the assertions by exactly one when the result asserts the
   pair in the other relation, raises them by one otherwise (`record_add`).
   Removing `xqy`: lowers them by exactly one when the result asserts `xqy`,
   raises them by one otherwise — possible from a state asserting the pair in
   both relations (`record_remove`). Identifying two terms: lowers the terms by
   one and the assertions by an even number `2c ≥ 0` (`record_identify`), any
   even number (`identify_takes`: `c` copies of `0r1` and of `1s0` lose all `2c`
   at once). In the ninth only a removal (one assertion) and an identification
   (one term) lower it, and no addition does (`ninth_record_add`).
6. **Which of the ninth's results remain different.** The ninth's results that
   assert no pair in both relations remain pairwise different, in every writing
   (`plain_states_stay_apart_every_writing`), and every ninth result is the same
   here as exactly one of them (`same_plainSt`, `together_plain`). A merge loses
   exactly the pairs asserted together, `min(M_r, M_s)` at each pair
   (`count_together`): a ninth state is determined by its result and that common
   part (`state_of_result_and_together`); with it go the ninth's size, both
   totals, each part as a seventh state, and the joint statement "some pair
   asserted in both relations" (`merge_loses`). Computed: of the ninth's 22 021
   results with two terms and 12 rounds, 17 786 merge away into 4 235 results
   here; one result takes in up to 70 of them (K4).
7. **Relating the seed to the earlier ones.** The ninth's states do not map one
   to one into this seed's results (witness: `a` and `a; ara asa`,
   `ninth_not_one_to_one`), and no map carrying every ninth addition to the same
   addition here can keep them apart (`carried_additions_merge`). The seventh's
   states do (D8): a seventh state read as asserting nothing with `s` (`ofR`) is
   its own plain state, every seventh change is carried to a change of the same
   kind (`Step7.embed`, `Reach7.embed`), and two seventh states give one result
   exactly when they are one seventh result (`ofR_same_iff`, and in every
   writing `ofR_sameW_iff`). The map back (`readBack`) reads the plain state: its
   `r` part if it asserts nothing with `s`, "none" otherwise; it returns the
   original on every mapped state (`readBack_ofR`), answers exactly the embedded
   results (`same_ofR_of_readBack`), and answers "none" on the one-term result
   asserting `asa` once (`readBack_asa`), **the smallest such result**: every
   result answered "none" costs at least two changes (`readBack_none_phi`) and the
   only one costing two is it (`readBack_none_smallest`). The eighth's and the
   first's states carry names that results here forget: not one to one (D8).
8. **What of the ninth holds here.** Reachability (a result reaches another
   exactly when the other has a term or the first is empty) holds, re-proved
   (`reach_criterion`); the empty state is never returned to
   (`empty_never_returned`). The exchange of the two relations is still a
   symmetry of results, cost and reachability, and now negates every excess
   (`same_swap_iff`, `phi_swap`, `excess_swap`, `Step.swap`). The cost holds on
   plain states only (cost = size exactly there). The ninth's "the relations
   interact through the terms alone" fails for results: adding `xsy` can take
   `xry` out of a result's plain state. The ninth's one-term interleaving count
   `C(p + q, p)` fails: a one-term result has one shortest sequence (the
   seventh's 7:D11 is back). The ninth's count fails: here each cycle of pairs
   of a rewriting contributes `(1 + x^L)/(1 − x^L)`, and with at most two terms
   the results of round `r` are `[r = 0] + [r ≥ 1]·one(r − 1) + [r ≥ 2]·two(r − 2)`,
   `one(0) = 1`, `one(t) = 2`, `two(0) = 1`, `two(t) = 4t(t² + 2)/3 + [t even]·t`
   — of order `r³`, the ninth's being of order `r⁷` (D11): 31 391 855 results
   with at most two terms within the seed's 100 rounds, given by formula.
9. **Readings kept.** The chosen reading (C-J1) takes the extra `xry` and `xsy`
   on one pair of terms. Kept and computed: C-J2 (any `xry` with any `usv`:
   a result is its terms and `Σ M_r − Σ M_s`), and C-J3 (only `x ≠ y`: loops not
   merged); under C-J3 a change of a result depends on the state taken, and
   round 3 already holds infinitely many results (D15).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2⁗ | An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G3″ | Nothing is given: to begin with there are no terms and nothing is asserted. |
| G6 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G11 | Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. |
| G12′ | Two results that differ only in how their terms are written, or only by an `xry` and an `xsy` asserted together, are the same result. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, and prove what is complete within it. |
| G14 | Any outcome is valid. |

Against the ninth seed G12′ replaces G12; every other sentence is the ninth's,
character for character (`diff`; `research/twentysecond/reading_the_seed.md`).

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry` or `xsy`, the two relations, multiplicity | given (G1, G2⁗) | the ninth's |
| the state: terms and a multiplicity for each ordered pair in each relation | chosen (9:C1′, no change) | `code/ninth/state.py`; Lean `St` (terms `0 … n − 1`, atoms counted) |
| the beginning: no terms, nothing asserted | given (G3″) | one beginning |
| change, four kinds; what identifying does | given (G6, G7) | on states, the ninth's |
| multiplicities of merged pairs add up; removing what is not asserted is not a change | chosen (9:C5⁗, no change) | unchosen "larger of the two": D14 |
| a pair asserted together (one `xry` and one `xsy` on the same terms) | given (G12′), chosen (C-J1) | unchosen C-J2, C-J3 kept (D15) |
| the sameness of results | given (G12′), derived (D1) | same terms and, after one rewriting, the same excess |
| the excess `M_r(x, y) − M_s(x, y)` | derived (D1) | a whole number of either sign; `excess` |
| the plain state of a result | derived (D1) | no pair asserted in both relations; `plain`, `plainSt` |
| result | given (G12′), derived (D1) | an excess function on the terms up to rewriting |
| a change of a result | chosen (C-X) | a change of any state of it; unchosen C-X′ gives the same results one change away (D2) |
| what is recorded for a result | given (G11), chosen (C-R) | the plain state's terms and assertions, by relation |
| cost (fewest changes) | derived (D4) | `n + Σ |excess|` |
| round; what counts as one change | chosen (9:C6, no change) | the round of a result is its cost (D4) |
| bound, frontier | given (G13); bound on terms and rounds chosen (9:C8′) | §6 |
| undoing (an addition returning to the result before an earlier one) | chosen (the task's word, §7) | two additions in a row whose second gives back the result before the first |
| which changes lower what is recorded, and by how much | derived (D6) | per kind |
| the seventh's states in; the map back | derived (D8) | `ofR`, `readBack` |
| what a merge of ninth results loses | derived (D7) | the pairs asserted together |
| reachability between results | derived (D9) | the ninth's criterion, re-proved |
| the exchange of the two relations | derived (D10) | negates the excess |
| counts of results by terms and recorded assertions | computed (K1), derived (D11) | a factor per cycle of pairs |
| shortest sequences to a result | computed (K5), derived (D4, D12) | additions only; one per one-term result |
| the ninth's statements about the asserting | computed again (K6) | read on the plain state |
| names `a`, `b`, `arb`, `bra`, destroyed givens | — (not in the seed) | without object, as under the ninth |
| the unchosen readings C-J2, C-J3 | chosen as alternatives, computed (D15, K8) | |

## 3. Readings that had to be chosen

Inherited without change from the ninth (9:C1′, C3, C5⁗, C6, C8′, C9): the
state, no cap on letters, what a change is and that merged multiplicities add
up, the order of the attempts (identifications, removals in `r`, in `s`, a
term, additions in `r`, in `s`), the bound on terms and rounds, and that `r`, `s`
write assertions, not terms. Each is about states or changes, which the changed
sentence does not touch (re-check: no change).

**C-J1 (chosen). What "differ only by an `xry` and an `xsy` asserted together"
means.** One state is the other with one more `xry` and one more `xsy` on the
same two terms — the letters `x`, `y` repeat in the sentence — and `x = y` is
allowed, since the seed writes every assertion `xry` and `xrx` is one (G2⁗).
"Are the same result" makes the sameness an equivalence, so it is the
equivalence these steps and rewriting generate (D1 proves what it is).

**C-J2 (unchosen, kept, computed).** The letters as placeholders: any `xry`
together with any `usv`. **C-J3 (unchosen, kept, computed).** Only two different
terms: `xrx` with `xsx` is not taken out. Both give different results (D15).
Set aside, with the words that refuse them: "one result has `xry` where the
other has `xsy`" (refused by "asserted together": both are in one result); "the
same for one extra pair but not for two" (refused by "are the same result": a
sameness that holds of the first and second and of the second and third holds
of the first and third).

**C-X (chosen). A change of a result.** A change of any state that is the
result; its outcome is the result of the outcome state. Unchosen C-X′: only the
plain state's changes are the result's. By D2 the two give the same results one
change away, hence the same rounds, costs and reachability; the exploration
attempts the plain state's changes.

**C-R (chosen). What is recorded for a result.** "For every result, record how
many terms and assertions it adds to what is given": nothing is given, and the
states of a result assert different numbers of assertions, so the record is
read on the result's plain state — its terms, its assertions in `r` and in `s`,
the same for every writing (`recorded_same`). Unchosen: the counts of the state
a particular sequence reached — a record of a sequence, not of a result; kept
in the attempt log (`reaches_the_state` beside `which_is_the_result`). By
`shortest_additions` a shortest sequence ends at the plain state, so on
shortest sequences the two agree.

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. Sameness: the same terms and the same excess.** At a fixed writing, the
equivalence generated by "one more `xry` and `xsy` on one pair" (the inductive
`Gen`, the list order of atoms not being data) holds of two well-formed states
exactly when they have equally many terms and the same *plain part*
(`gen_iff_same`), equivalently the same excess at every ordered pair
(`same_iff_excess`). The plain part of a list of atoms (`plain`) takes out every
pair asserted in both relations; its multiplicity of `xqy` is the multiplicity
of `xqy` less that of the same pair in the other relation, cut at zero
(`count_plain`); no pair is asserted in both relations in it (`plain_reduced`);
rearranged lists have rearranged plain parts (`plain_perm`). Writing included:
a rewriting carries the plain part along (`plain_rename`), and the full
sameness `SameW` — some rewriting, then the same plain part — is an equivalence
(`SameW.refl`, `SameW.symm`, `SameW.trans`) and is exactly the one the changed
sentence generates from its two clauses (`genW_iff_sameW`). So a result *is* an
excess function on its terms up to rewriting, and its plain state is unique up
to writing. Computed: on all 1 242 states with at most two terms and at most
three assertions in each relation, joining each state to its rewritings and to
itself with one more pair asserted together gives 247 classes, exactly the
classes of this criterion (`check_sameness`, `summary.json`
`generated_sameness`).

**D2. The changes of a result do not depend on the state taken.** For two
states of one result, every change of the first has, up to the seed's sameness,
the outcome of a change of the second (`step_of_same`): adding a term or an
assertion and identifying two terms respect the sameness (`Same.addTerm`,
`Same.add`, `Same.identify`); removing an atom both states assert respects it
(`Same.remove`); and removing `xry` is the same result as adding `xsy`
(`same_remove_add_partner`). Hence sequences from any state of a result reach
the same results (`reach_of_same`), C-X and C-X′ agree on the results one change
away, and a result attempts its plain state's changes: `C(n, 2) + d + 1 + 2n²`
of them, `d` the pairs its plain state asserts (9:D3 read on the plain state;
computed again, `attempts_equal_formula` true in every run). Computed: every
removal from a state of a result that is not plain (one pair asserted together
added at each pair, then either relation removed there) lands on an outcome of
the plain state's changes — 32 672, 238 796 and 575 090 such removals in the
three runs (`removal_outside` empty).

**D3. The first change adds a term; the empty state is never returned to.**
On the empty state the only change is adding a term (`first_change_adds_term`);
every change of a well-formed state leaves a term if there was one
(`Step.n_pos`, `Reach.n_pos`), and the sameness keeps the number of terms. So
the empty result is reached only from itself (`empty_never_returned`). 9:D1,
9:D2 re-proved.

**D4. Fewest changes: `n + Σ |excess|`.** Let `phi G` be the terms of `G` plus
the assertions of its plain part. Then `phi` is the same for states of one
result (`Same.phi`, `SameW.phi`); every change raises it by at most one
(`Step.phi_le`), an identification lowers it by at least one
(`Step.phi_identify`), so a state reached from the empty state in `k` changes
has `phi ≤ k` (`Reach.phi_le`); and `phi G` additions reach the plain state
(`reach_plainSt`: the terms, then the plain part's assertions). So the fewest
changes to the result of `G` is `phi G`, at a fixed writing (`fewest_changes`)
and in every writing (`fewest_changes_every_writing`). The ninth's cost of a
state, its size (9:D4), is `phi` plus the atoms of the pairs it asserts together
(`size_eq_phi_add_together`): the ninth's cost survives exactly on the plain
states. **A shortest sequence** from the empty state is additions only and ends
at a plain state (`shortest_additions`: the size moves by exactly one per
change, and is at least `phi`); each of its prefixes is shortest
(`shortest_prefix`); every state along it asserts no pair in both relations
(`shortest_all_plain`), so it never adds both relations at one pair. The
seventh's cost of a seventh state is this seed's cost of its embedded result
(`phi_ofR`). Computed: the round of every explored result equals its cost in
all three runs (`round_not_cost` empty); no change raises the cost by more than
one (`cost_raised_by_more_than_one` empty); every change raising the round is
an addition (`raising_not_addition` empty).

**D5. Undoing.** *The ninth:* an addition raises the ninth's size by one
(`AddStep.size`, `AddReach.size`) and the ninth's sameness keeps the size
(`SameState9.size`, `size_rename`), so a non-empty sequence of additions never
returns to its start's result (`ninth_additions_never_return`, in every writing
`ninth_additions_never_return_every_writing`). No addition undoes an earlier
one. *Here:* on every state with terms `x`, `y`, adding `xry` then `xsy` is two
additions ending at the start's result (`addition_undoes_addition`), while the
start and the end are two different ninth states (`addition_undoes_not_in_ninth`;
the state between them differs from both by its size).
Removing `xry` and adding `xsy` have one result (`same_remove_add_partner`), so
the second addition does what a removal of the first would. At a fixed writing
two additions in a row return to the start's result exactly when they are one
pair in the two relations (`same_add_add_iff`, `two_additions_return_iff`).
Writing included, other pairs can: on two terms with `0r0`, adding `1r1` then
`0s0` gives the same result, the two terms exchanged (`given.json`,
`two_additions_on_different_pairs_that_undo_up_to_writing`). Computed: at every
pair of every result whose changes were attempted, `xry` then `xsy` returns to
the result (`undo_failed` empty in every run).

**D6. What is recorded, and which changes lower it.** Recorded (C-R): the terms
and the plain state's assertions, by relation (`recorded`, `recorded_same`,
`recorded_sum`: their sum is the cost). By kind:
- adding a term: terms `+1`, assertions unchanged (`record_addTerm`) — never
  lowers;
- adding `xqy`: assertions `−1` exactly when the result asserts the pair in the
  other relation, else `+1` (`record_add`);
- removing `xqy` from a state asserting it: `−1` exactly when the result asserts
  `xqy`, else `+1` — the second only from a state asserting the pair in both
  relations (`record_remove`);
- identifying two terms: terms `−1` and assertions `−2c`, `c ≥ 0`
  (`record_identify`), `c` being, over the pairs the identification merges, the
  part of their excesses of opposite signs; any `c` occurs
  (`identify_takes`).

So in total the cost changes by `+1` (a term; an addition or a removal that
does not take out), `−1` (an addition or a removal that does), or `−(1 + 2c)`
(an identification): always by an odd number (`Step.phi_parity`), so no change
keeps a result's round and none returns to its own result (`Step.not_same`). In
the ninth an addition always raises the record (`ninth_record_add`), a removal
lowers the assertions by one and an identification the terms by one, keeping
the total. Computed, in the 5-term run (44 890 changes): a term `+1` 1 662
times; an addition `+1` 27 720 times and `−1` 4 952 times; a removal (of the
plain state) `−1` 4 952 times; an identification `−1` term with `−0`, `−2`, `−4`
assertions 4 226, 1 242, 136 times; in the two-term run identifications take out
up to 20 assertions at once. Every change's move agrees with the rule computed
from the excesses alone (`predicted_move`; `record_move_mismatch` empty).

**D7. Which of the ninth's results remain different; what a merge loses.** Every
state is the same result as its plain state (`same_plainSt`), which asserts no
pair in both relations (`together_plain`). Two such states are one result here
exactly when they are one ninth state (`plain_states_stay_apart`), in every
writing (`plain_states_stay_apart_every_writing`). So the ninth's results that
remain different are the plain ones, and each ninth result is one result here
with exactly one of them. A merge loses exactly the pairs asserted together: at
`xqy`, `min(M_q, M_other)` of them (`count_together`); a ninth state is
determined by its result here and that common part
(`state_of_result_and_together`). With it go: the ninth's size (it exceeds the
cost by the common part's atoms, `size_eq_phi_add_together`), the totals of
each relation, each relation's part as a seventh state, and whether some pair
is asserted in both relations — `a` and `a; ara asa` are one result with sizes
1 and 3 and different totals (`merge_loses`). What is kept: the terms, the
excess, the cost, the plain state. Computed again (9:K1 re-run; K4): every ninth
result is a result here at the round of its cost; the plain ninth results are
exactly the results here within the ninth's rounds, one each.

**D8. Relating this seed to the earlier ones.** *The ninth* does not map one to
one: `a` and `a; ara asa` are different ninth states (sizes differ) and one
result here (`ninth_not_one_to_one`). More: any map `f` from the ninth's states
that sends the empty state to the empty result and each addition to the same
addition here, up to this seed's sameness, sends those two to one result
(`carried_additions_merge`). *The seventh* maps one to one. Its state (one
relation, re-written in `lean4_core` as `St7`: `n` terms and a list of pairs)
read as a state asserting nothing with `s` (`ofR`) is its own plain state
(`plain_ofR`); every seventh change is carried to a change of the same kind
(`Step7.embed`, `Reach7.embed`); two seventh states give the same result here
exactly when they are the same seventh state (`ofR_same_iff`), and in every
writing exactly when a rewriting makes them the same (`ofR_sameW_iff`). *The
map back* `readBack` answers the plain state's `r` part as a seventh state when
the plain state asserts nothing with `s`, and "none" otherwise. It returns the
original on every mapped state (`readBack_ofR`); the results it answers are
exactly the images (`same_ofR_of_readBack`); it is a function of the result
(`readBack_same`, and in every writing `readBack_none_rename`); it answers
"none" on the one-term result asserting `asa` once (`readBack_asa`). **The
smallest result answered "none"** is that one: every result answered "none" has
a term and an assertion of `s` in its plain state, so costs at least two changes
(`readBack_none_phi`), and the only one costing two is the one-term result
asserting `asa` once (`readBack_none_smallest`; `phi_asa`). Computed: it is the
first result answered "none" in round order in every run, at round 2
(`seventh_derivation` blocks). *The eighth* (names `a`, `b`, `arb` given) does
not map one to one: two terms asserting `0r1` with `a`, `b` on terms 0 and 1,
and the same with both names on term 0, are different eighth states (its
sameness keeps whether the names are one term) and one result here
(`given.json`, `the_eighth_does_not_map_one_to_one`). *The first* likewise: the
same two states read with one relation asserting each pair at most once are
different first-seed states (1:C4 keeps the names) and one result here; the
first's states carry names results here do not have (paper).

**D9. Reachability: the ninth's criterion holds.** A result reaches another
exactly when the other has a term or the first is the empty state
(`reach_criterion`): necessity by D3; sufficiency by removing every assertion,
identifying the terms down to one, adding terms, and adding the target's plain
part (`reach_clear`, `reach_collapse`, `reach_grow`, `addReach_atoms`). Results
with a term reach each other both ways (`reach_mutual`). 9:D8, 9:D9 re-proved.
New: every result with a term has a two-change cycle made of two additions
(D5), and none of one change (`Step.not_same`). Computed (K7): within 3 terms and
4 rounds, 36 results, 1 296 ordered pairs, 1 261 reachable, the 35 unreachable
being those into the empty state; the criterion agrees with a search along the
changes on every pair.

**D10. The exchange of the two relations.** Exchanging `r` and `s` in every
assertion (`St.swap`) negates every excess (`excess_swap`), carries the plain
part to the plain part (`plain_swap`), keeps the sameness both ways
(`same_swap_iff`) and the cost (`phi_swap`), and carries every change to a
change of the same kind (`Step.swap`): a symmetry of results, cost and
reachability, as in the ninth (9:D16 re-proved). New: every state whose two
relations agree everywhere is the result asserting nothing on its terms, and a
result is unchanged by the exchange exactly when its excess function is, up to
rewriting, its own negative. Computed: every explored result's exchange is a
result at the same round with the same number of shortest sequences and its
record's relations exchanged (`exchange_mismatch` empty).

**D11. Counting the results; the two-term closed form.** A result with `n`
terms records `t = Σ |excess|` assertions and costs `n + t`. A rewriting fixes an
excess function exactly when it is constant on each cycle of ordered pairs; a
cycle of length `L` carrying `e` weighs `L·|e|`; so the rewriting contributes
`Π (1 + x^L)/(1 − x^L)` over its cycles of pairs, and the results are the average
over the rewritings of `n` terms (`code/twentysecond/orbits.py`,
`count_results`). With one term: one result recording 0 assertions, two for
every `t ≥ 1` (`e(0, 0) = ±t`). With two terms: the four excesses with
`Σ |e| = t` number `Σ_k C(4, k)·2^k·C(t − 1, k − 1) = 8t(t² + 2)/3` for `t ≥ 1`
(`k` of them non-zero, each of either sign); the exchange of the two terms,
`(e00, e01, e10, e11) → (e11, e10, e01, e00)`, fixes those with `e00 = e11`,
`e01 = e10`, `2(|e00| + |e01|) = t`: `2t` of them for even `t ≥ 2`; halved,
`two(t) = 4t(t² + 2)/3 + [t even]·t` for `t ≥ 1`, `two(0) = 1`: 1, 4, 18, 44, 100,
180, 310, 476, … So the results of round `r` with at most two terms are
`[r = 0] + [r ≥ 1]·one(r − 1) + [r ≥ 2]·two(r − 2)` = 1, 1, 3, 6, 20, 46, 102,
182, 312, 478, … (`two_term_round_count`), of order `(4/3)r³`; within the seed's
100 rounds, 31 391 855 results (`summary.json`, `independent_counts`). Without a
bound on terms the results of round `r` number 1, 1, 3, 7, 25, 83, 316, 1 272,
5 506, 25 035, 120 137, … (`layer_counts`; the ninth's were 1, 1, 3, 8, 29, 104,
420, …). Not in Lean; the count agrees with a listing of every excess table for
small `n`, `t` (`tests/test_twentysecond_explore_orbits.py`) and with the
explorations (K1).

**D12. One shortest sequence per one-term result.** A shortest sequence is
additions only along plain states (D4), so to the one-term result with
`e(0, 0) = p > 0` it is: the term, then `p` times `ara` — one sequence; likewise
with `asa`. The ninth's `C(p + q, p)` (9:D11) fails, and the seventh's "one
shortest sequence" (7:D11) holds again. Computed: every one-term result is
reached by exactly one shortest sequence in every run
(`one_term_not_one_sequence` empty).

**D13. Completeness within the bound; the frontier.** Let the bound be `N`
terms and `R` rounds. Every result with at most `N` terms and cost at most `R`
is reached by the additions of D4, whose states never have more terms than the
target and whose cost rises by one per change, so the exploration finds it at
the round of its cost; every explored result is within the bound by
construction. The explored counts by (terms, recorded assertions) equal the
independent counts restricted to `n + t ≤ R` in every run (`count_mismatch`
empty). The frontier: an attempt leaves the bound on terms exactly when it adds
a term to a result with `N` terms — one entry per such result whose changes
were attempted (`frontier_entries_are_1_per_state_with_N_terms` true); the
results of round `R` are the second part. Shortest-sequence counts are exact
within the bound (D4: a shortest sequence never has more terms than its end).

**D14. The unchosen reading of identification (9:C5⁗, "the larger of the two").**
The ninth kept, as an unchosen alternative, merged multiplicities taking the
larger of the parts in each relation (9:D15: same results, reachability and
cost there). Here: the results are the same (D4's additions identify nothing),
reachability is the same (D9's path identifies terms with nothing asserted), and
the cost is the same, since for any state of the result
`|max_i (r_i + c_i) − max_i (s_i + c_i)| ≤ Σ_i |r_i − s_i|` (take `i` where the
larger maximum is attained), so an identification still lowers `phi` by at
least one. What changes: under that reading an identification's outcome, as a
result, depends on the state taken (two terms asserting `0r0`: identified
directly the result is `ara`; with a pair `1r1`, `1s1` asserted together first,
it is the result asserting nothing), so C-X and C-X′ differ there in the
results one change away but not in the rounds. Not computed; proof here.

**D15. The unchosen readings C-J2 and C-J3.** *C-J2* (any `xry` with any `usv`):
the sameness keeps the terms and `D = Σ M_r − Σ M_s` only — with a term, two
states with equally many terms and one `D` are joined by adding a pair and
taking out another — so a result is `(n, D)` (`D = 0` without terms), its cost
`n + |D|` (identification keeps both totals; every change moves `n + |D|` by at
most one; additions reach it), and the results of round `r` within `N` terms
are `[r = 0] + [1 ≤ r ≤ N] + 2·min(r − 1, N)`. *C-J3* (only `x ≠ y`): off the
diagonal the excess is kept, on it both multiplicities; under C-X′ the cost is
the size of the reduced state and each cycle of pairs contributes
`(1 + x^L)/(1 − x^L)` off the diagonal and `1/(1 − x^L)²` on it. Under C-X a
change of a C-J3 result depends on the state taken: two terms asserting
nothing, and the same with `k` copies of `0r1` and `0s1` (one C-J3 result),
identify to one term asserting nothing and to one term asserting `ara` and `asa`
`k` times each — a different result for every `k`, each three changes from the
empty state while its reduced size is `1 + 2k`. So under C-J3 with C-X round 3
is infinite and no bound on terms and rounds makes a round finite. Computed
(K8, `readings.json`): at 2 terms and 8 rounds, 673 results under C-J1, 29
under C-J2 (per round 1, 1, 3, 4, 4, …) and 1 081 under C-J3 (per round 1, 1, 3,
7, 23, 57, 140, 287, 562 — more than C-J1, the loops keeping both
multiplicities); the rounds equal the cost formulas, the C-J2 rounds their
closed form, the C-J3 counts its orbit count, and the padded identifications of
the witness give `a; ara asa`, `a; ara(2) asa(2)`, `a; ara(3) asa(3)`, of reduced
sizes 3, 5, 7.

**D16. Nothing about the asserting holds in every result.** The ninth's
forty-two statements (9:D14), read on the plain state (C-R): none holds in every
explored result; one, "some pair asserted in both relations", holds in none —
by construction of the plain state, not a property of the asserting; every other
holds in some and fails in another (K6).

## 5. What does not follow

Each item has two witnesses, or a proof.

- **N1.** That the ninth's size, either total, or either part is kept by the
  sameness: `a` and `a; ara asa` (sizes 1 and 3, totals 0 and 1) are one result
  (`merge_loses`); kept are the terms and the excess (D1).
- **N2.** That an addition raises what is recorded: `a; ara` plus `asa` lowers
  it from (1, 1, 0) to (1, 0, 0); `a` plus `ara` raises it (`given.json`,
  `record_add`).
- **N3.** That a removal lowers what is recorded: from `a; ara asa` (a state of
  the result `a`) removing `ara` raises it from (1, 0, 0) to (1, 0, 1); from
  `a; ara` removing `ara` lowers it (`record_remove`).
- **N4.** That an identification lowers the recorded assertions by at most a
  fixed number: `c` copies of `0r1` and `1s0` lose `2c` (`identify_takes`); two
  terms asserting `0r0` and `1r1` lose none.
- **N5.** That two additions returning to their start's result are one pair in
  the two relations: at a fixed writing yes (`two_additions_return_iff`); with a
  rewriting, `1r1` then `0s0` on two terms asserting `0r0` also return (D5).
- **N6.** That the cost moves by exactly one per change: an identification of
  `0` and `1` in `a b; arb bsa` lowers it from 4 to 1 (`given.json`); an
  addition moves it by one.
- **N7.** That the results' plain `r` and `s` parts are free of each other: in
  a plain state the two relations never assert the same pair
  (`plain_reduced`), whereas the ninth's two parts were jointly free (9:D5);
  every pair of parts is a state here, but `(M_r, M_s)` and
  `(M_r + c, M_s + c)` are one result.
- **N8.** That results of one round with equally many terms have equally many
  changes: `C(n, 2) + d + 1 + 2n²` depends on the pairs `d` the plain state
  asserts (3 for `a`, 4 for `a; ara`, both one term).
- **N9.** That a result is reached by one shortest sequence: one-term results
  are (D12); the two-term result with one assertion between its terms
  (`a b; bra` in the files) is reached by two — on the two terms, adding `arb`
  and adding `bra` are two changes with that one result (K5); 49 of the 86 201
  results of the two-term run have one.
- **N10.** Anything about the asserting (D16), except what the plain state has
  by construction.
- **N11.** That the seventh's states cover the results: 6 369 of the 7 168
  results of the 5-term run are answered "none" by the map back (K3).
- **Refuted** (proved impossible): a change other than adding a term on the
  empty state (D3); a sequence from a result with a term back to the empty
  state (D3); fewer changes to a result than `n + Σ |excess|` (D4); a shortest
  sequence with a removal or an identification, or through a state asserting a
  pair in both relations (D4); a change that keeps a result's round, or returns
  it to itself (D6); a non-empty run of ninth additions returning to its start's
  ninth result (D5); two plain states that are one result here and two ninth
  results (D7); two seventh results that are one result here (D8); a result
  answered "none" costing fewer than two changes, or costing two and other than
  `a; asa` (D8).

## 6. The exploration

**Protocol.** From the empty state, under this seed's sameness (the least
writing of the plain state is the result): round by round, the changes of every
result first reached in the round before — its plain state's changes (C-X, D2),
fewest additions first. Three runs: 5 terms and 8 rounds, 3 terms and 10
rounds, 2 terms and 24 rounds (reading 9:C8′; each completed in minutes here).
Beside each, the seventh's exploration at the same bounds and the ninth's at the
same bound on terms with 8, 9 and 12 rounds (its own bounds). A full attempt log
at 2 terms and 3 rounds; reachability at 3 terms and 4 rounds; the generated
sameness on every state of at most two terms and three assertions per relation;
the unchosen readings at 2 terms and 8 rounds. Files: `results_*.csv`,
`added_*.csv` (results by what they record), `frontier_*.csv`, `rounds_*.csv`,
`follows_*.csv`, `reach_bound3_rounds4.csv`, `attempts_bound2_rounds3.jsonl`,
`counts.csv`, `given.json`, `readings.json`, `summary.json` (every check, and the
disagreement lists of `JointCheck`, all empty), `lean_axioms.txt`,
`MANIFEST.sha256`.

**K1. Results within the bounds.**

| run | results | by terms | attempts | the map back returns a seventh state | shortest sequences (total) |
|---|---|---|---|---|---|
| 5 terms, 8 rounds | 7 168 | 1 / 15 / 657 / 3 811 / 2 340 / 344 | 44 930 | 799 | 5 370 224 |
| 3 terms, 10 rounds | 39 526 | 1 / 19 / 1 845 / 37 661 | 349 352 | 2 232 | 404 184 064 |
| 2 terms, 24 rounds | 86 201 | 1 / 47 / 86 153 | 979 814 | 7 539 | 498 329 110 651 631 |

In every run: every round has a new result; the round of every result is its
cost; the counts equal the independent count; with at most two terms the rounds
follow the closed form (D11); rounds `0 … N` agree with the unbounded count; no
change keeps the round (in the 5-term run 29 382 raise it, 15 508 lower it).

**K2. The seventh, computed again.** In every run the seventh's results at the
same bounds, read as asserting nothing with `s`, are exactly the results whose
plain state asserts nothing with `s` (799, 2 232, 7 539), at the same rounds,
with the same shortest-sequence counts; the map back returns each (7:K1, 7:K2,
7:K7 computed again).

**K3. The map back.** It answers "none" on 6 369, 37 294 and 78 662 results of
the three runs; the first in round order is `a; asa`, round 2.

**K4. The ninth, computed again.** 5 terms, 8 ninth rounds: 10 416 ninth results
→ 7 168 results here (the plain ninth results, one each); 3 248 merged away;
434 results take in more than one, up to 55. 3 terms, 9 rounds: 25 965 → 13 912;
12 053 merged away; 1 343 take in more than one, up to 55. 2 terms, 12 rounds:
22 021 → 4 235; 17 786 merged away; 1 864 take in more than one, up to 70. Every
ninth result is a result here at the round of its cost; the ninth's round (its
size) equals the cost here exactly on the plain ones (9:K1, 9:K2 computed again).

**K5. Shortest sequences.** Exact within the bound (D13); one per one-term
result (D12); 20, 22 and 49 results with one shortest sequence in the three runs.

**K6. Statements.** 42 tested (9:K7's, read on the plain state): none holds in
every result; "some pair asserted in both relations" holds in none; every other
holds in some and fails in another (`follows_*.csv`).

**K7. Reachability** within 3 terms and 4 rounds: see D9.

**K8. The unchosen readings** at 2 terms and 8 rounds: see D15 and
`readings.json`.

**K9. Changes and what is recorded**: see D6; the full attempt log records, for
each of its 22 attempts, the state reached, whether it asserts a pair in both
relations, its result, what that result records and the move.

**Reproducibility.** `python code/run_twentysecond.py` rewrites every computed
file; `--check` regenerates into a temporary folder and compares byte for byte;
`python code/lean_report_twentysecond.py` builds `lean4_core/` and rewrites
`lean_axioms.txt`, refusing any axiom other than `propext` and `Quot.sound`.

## 7. The task's questions

- **Can an addition undo an earlier addition?** In the ninth, no (D5): additions
  raise the size, which the ninth's sameness keeps. Here, yes: `xsy` undoes
  `xry` (and in general does what removing `xry` would do); two additions in a
  row give back their start's result exactly when they are one pair in the two
  relations at a fixed writing, and also for other pairs up to rewriting.
- **The fewest changes to each result**: `n + Σ |excess|`, the terms and the
  assertions of its plain state (D4).
- **Which changes lower what is recorded, and by how much**: an addition or a
  removal by exactly one assertion when it takes out a pair the result asserts
  in the other relation (addition) or asserts itself (removal), otherwise it
  raises by one; an identification by one term and an even number of assertions,
  any even number; adding a term never (D6).
- **Which of the ninth's results remain different**: exactly those asserting no
  pair in both relations, pairwise, in every writing; each ninth result is one
  of them here; a merge loses the pairs asserted together (D7).
- **An earlier seed mapped in one to one, and back**: the seventh (D8), with the
  map back answering "none" first on `a; asa`.

## 8. What of the ninth holds here, and where it does not

- **Cost** (9:D4, size): holds on plain states only; in general the cost is the
  plain state's size, `n + Σ |excess|`, and every other state of the result has
  a larger size. Its "every change moves the cost by exactly one" fails
  (identifications, D6); "no change keeps the round" (9:D4(v)) holds, by parity.
  "Every shortest sequence is additions only" (9:D4(vi)) holds.
- **Reachability** (9:D8, 9:D9): holds, re-proved; the empty state is still the
  one irreversible exit; results with a term reach each other both ways.
- **The exchange** (9:D16): holds, now negating the excess.
- **The results** (9:D5): every well-formed state is still reached, but many
  states are one result; jointly free parts fail as results (N7).
- **The interaction through the terms alone** (9:D17): fails for results — an
  assertion of one relation can take out an assertion of the other from the
  plain state (D6).
- **The count** (9:D10, 9:D11): fails; new closed forms (D11). One-term
  interleaving `C(p + q, p)` fails (D12).
- **The change count** (9:D3): holds, read on the plain state (D2).
- **One sameness, no names** (9:D12): holds.
- **The first change, the empty state** (9:D1, 9:D2): hold (D3).
- **Nothing about the asserting holds in every result** (9:D14): holds (D16).
- **The unchosen identification reading** (9:D15): same results, cost and
  reachability; the outcome of an identification as a result depends on the
  state under it (D14).

## 9. Alternatives: kept, or eliminated by proof

| Alternative | Kept / eliminated |
|---|---|
| C-J1 / C-J2 / C-J3 readings of the changed sentence | C-J1 chosen; C-J2, C-J3 kept and computed (D15) |
| "one result has `xry` where the other has `xsy`" | set aside: refused by "asserted together" |
| sameness not closed under repetition | set aside: refused by "are the same result" |
| C-X / C-X′ (changes of any state / of the plain state) | the same results one change away (D2) |
| C-R: record of the plain state / of the state a sequence reached | the first chosen; the second kept in the attempt log |
| multiplicities add up / the larger of the two | the first chosen; the second kept, same results, cost, reachability (D14) |
| other orders of attempts | not computed; same results and rounds (D4) |
| a bound on terms alone | eliminated: the results within it are infinite (D11) |
| every excess function within the bound, up to rewriting | kept; none dropped (D13) |
| names, `arb`, `bra`, what is given | without object, as under the ninth |

## 10. Open

- O1. A closed form for the number of shortest sequences reaching a result with
  two or more terms: computed per result within the bound, exact there (D13).
- O2. Results beyond the declared bounds, listed: counted by formula (D11), not
  listed; the frontier is exported.
- O3. Lean statements of the count and the closed forms (D11, D12, D13), of the
  unchosen readings (D14, D15), and of the first seed's witness (D8): proved here
  and checked by computation.

## 11. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **The Grothendieck group of a commutative monoid.** Taking a pair of
  multiplicity functions `(M_r, M_s)` up to adding the same amount to both at a
  pair is the construction of the integers from pairs of naturals, pair by pair:
  the excess is the formal difference, and the plain state is the reduced
  representative. D1 is that construction applied at every ordered pair and then
  divided by the permutations of the vertices; D4 is that the word length from
  zero, with the four changes as generators, is the `ℓ¹` norm of the reduced
  representative plus the vertex count.
- **Signed multigraphs / integer-weighted directed graphs with loops, up to
  isomorphism.** The results are these; D11 is their orbit count by total
  absolute weight, each cycle of arcs contributing `(1 + x^L)/(1 − x^L)`.
- **Graph edit distance with signed arcs.** D4, D6: with unit-cost vertex and arc
  insertions and deletions and vertex contraction, the distance from the empty
  graph is vertices plus total absolute weight; contraction can cancel weight of
  opposite signs, which is where the ninth's "each change moves the cost by one"
  fails.
- **Free abelian groups on arcs, and cancellation in pairs.** D5's "an addition
  undoes an addition" is the familiar statement that in a group every element
  has an inverse among the generators here (`xsy` for `xry`), which the ninth's
  monoid of multiplicities lacks.

What appears to be specific to this seed: that the two relations of the ninth,
once a pair asserted in both is taken out, become one relation with signed
multiplicities, so that the ninth's jointly free parts, its size-as-cost, its
count and its one-term interleaving all fail while its reachability, its
exchange symmetry and its parity survive; that the seventh (and not the ninth)
maps in one to one, with the one-term result asserting `asa` once as the
smallest result outside its image; and that the readings of the changed sentence
split sharply — placeholder letters collapse every result to its terms and one
number, and sparing the loops makes a change of a result depend on the state
taken, with an infinite round 3.
