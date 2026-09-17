# What follows from `arb`, no `xrx`, and four kinds of change

Input: `prompt/seed_prompt.md`. Task: `prompt/prompt.md`. Claim IDs refer to
`paper/claim_ledger.md`. Lean names refer to `lean4/H3V7N5QF/`; their axiom
report is `evidence/lean_axioms.txt`. Computed files are in `evidence/`, written
by `python code/generate.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; the unchosen
readings are listed), **derived** (proved), **computed** (output of `code/`),
**refuted** (proved impossible), **open**.

## 0. Findings in brief

1. `a` and `b` are two terms (derived). Whether `bra` is asserted is
   independent of what is given (derived: two legal models). On the given terms
   there are exactly two legal states containing `arb`; both are kept as
   alternatives for what is given, and each is one change away from the other.
2. Exactly two kinds of change can be obstructed: adding `xrx`, and identifying
   `x` and `y` while `xry` or `yrx` is asserted (derived). The first is
   obstructed in every state and nothing can clear it. The second is cleared by
   removing the assertions between the two terms and by nothing else.
3. However obstructed changes are answered, the results are the same: every
   answer is a sequence of unobstructed changes (derived). The protocol of
   obstruction and answer adds records, not results.
4. The results are all finite legal states with at least one term — every one
   of them, and nothing else (derived). So a statement about the asserting
   holds in every result only if it holds in every finite legal state; nothing
   beyond "no `xrx`" is forced.
5. The fewest changes that reach a result is given by a closed formula (derived,
   Lean): *terms plus assertions of the result, minus terms plus assertions of
   what is given, plus two for each given that the result has destroyed.* A
   destroyed given is a given assertion no longer asserted between `a` and `b`,
   or the twoness of `a` and `b`.
6. Identifying `a` and `b` is the one thing that cannot be undone: no sequence
   of changes tells them apart again, and `arb` is then never asserted again
   (derived; meaningful only when the names `a`, `b` are kept).
7. 100 rounds cannot be listed: every round has new results, 33 748 590 999 of
   them in round 20 alone under one reading (computed from 5.). Declared bound:
   at most 5 terms (any rewriting) and 4 terms (names kept). Within the bound
   the exploration is complete, certified by an independent count, and the
   frontier is exported exactly.

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2 | An assertion is written `xry`, where `x` and `y` are terms. |
| G3 | `arb` is asserted. |
| G4 | For no term `x` may `xrx` be asserted. |
| G5 | Whether `bra` is asserted is not given. |
| G6 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G8 | A change that makes some `xrx` asserted is obstructed. |
| G9 | An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which; record the change, the obstruction, the answer. |
| G10 | A refused change is recorded and changes nothing. |
| G11 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, prove what is complete within it. |
| G14 | Any outcome is valid. |

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry`, asserted | given (G1–G3) | |
| an assertion has a first and a second term | derived | the seed treats `arb` and `bra` as different (G3, G5) |
| asserted is yes/no, no multiplicity | chosen (C1) | unchosen: multiplicity; open O1 |
| legal state (no `xrx`) | given (G4) | a rule for every state ("may") |
| `a`, `b` are two terms | derived (D1) | |
| what is given has exactly the terms `a`, `b` | chosen (C2) | unchosen: more to begin with; shown harmless (D9) |
| two alternatives for what is given | derived (D2) | given C2 |
| supply of letters not capped | chosen (C3) | unchosen: a cap; shown harmless (D8 remark) |
| `r` does not write a term | chosen (C9) | writing only |
| change, four kinds | given (G6, G7) | |
| non-changes; a new term has no assertion; an added assertion is between terms there | chosen (C5) | read off "exactly one of", "nothing else" |
| obstructed change | given (G8) | characterised: derived (D3) |
| the obstruction of a change | chosen (C7) | the assertions that would become `xrx` |
| refuse / remove the obstruction / build structure | given (G9, G10) | their exact content: chosen (C7); results independent of the choice: derived (D10) |
| result | chosen (C6) | a legal state up to sameness |
| sameness | given (G12) | two readings, both kept: chosen (C4) |
| terms and assertions added to what is given | given (G11) | two terms and one assertion are given; may be negative |
| round; what counts as one change | chosen (C6) | |
| bound, frontier | given (G13) | bound on terms: chosen (C8) |
| destroyed given, cost | derived (D8) | |
| counts of results | computed (K-claims) | |

## 3. Readings that had to be chosen

**C1. Asserted is yes or no.** The seed says "is asserted" of an assertion and
asks "whether `bra` is asserted". No sentence uses multiplicity. Unchosen: an
assertion may be asserted several times. Not explored (O1).

**C2. To begin with there are exactly the terms `a` and `b`.** Support: on
`a`, `b` the possible assertions are `ara`, `arb`, `bra`, `brb`; two are
forbidden, one is given, and the seed flags exactly the fourth as not given.
Unchosen: further terms or assertions to begin with. Every such beginning is a
legal state containing `arb`; by D9 it is a result of the chosen beginning,
reached by additions alone. So the unchosen reading moves the starting point and
adds no result.

**C3. No cap on the number of terms.** Not given either way. If at most `L ≥ 2`
terms can be written, every statement below holds for states with at most `L`
terms: the sequences of changes used in the proofs never have more terms than
their target, or two.

**C4. Sameness, two readings, both kept.** FREE: any rewriting of terms, `a`
and `b` included (the literal reading of G12). ANCHORED: rewritings that keep
the writing of `a` and `b` (because "what is given" names them and G11 compares
with it). Under ANCHORED a state remembers which terms carry the names; after an
identification one term may carry both. Under FREE, `arb` alone and `bra` alone
are the same result; under ANCHORED they are not. Nothing in the seed
eliminates either reading. All computations are done under both.

**C5. Non-changes.** Adding what is asserted, removing what is not, identifying
a term with itself: these change nothing, so by G6 they are not changes. A
change is exactly one of the four: a new term comes with no assertion, and an
added assertion is between terms already there.

**C6. Results and rounds.** A result is a legal state up to sameness. Round `k`
attempts every change on every result known after round `k − 1`. Each performed
change counts one; a refused change is an attempt of its round that changes
nothing; the further changes of an answer count one each. Unchosen: an
obstructed change and its answer count as one. By D10 the results are the same
under both; only round numbers move.

**C7. Obstruction and answers.** The obstruction of a change is the set of
assertions that would become some `xrx`: for identifying `x`, `y` those of
`xry`, `yrx` that are asserted; for adding `xrx` that assertion itself.
*Refuse*: recorded, nothing changes. *Remove the obstruction*: remove those
assertions, then perform the change. *Build structure*: by additions only, reach
a legal state from which identifying the added terms back gives exactly the
would-be outcome of the obstructed change; fewest additions first. For an
obstructed identification the state itself is such a build, with no addition
(the two terms stay two). For adding `xrx` the builds with fewest additions add
one term `t` and one assertion, `xrt` or `trx` (D11). Two other readings were
tried and dropped for cause (`research/reading_the_seed.md`): "perform, then
repair" cannot avoid a removal (D5), and "build until the change is
unobstructed" never succeeds (D4, D5). Under *any* reading in which further
changes are changes of the four kinds and no state holds `xrx`, the results are
the same set (D10).

**C8. Bound.** At most 5 terms under FREE, 4 under ANCHORED: the largest that
complete in under a minute here (9 846 and 2 973 results).

**C9.** `r` writes assertions, not terms. Writing only.

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. `a` and `b` are two terms.** If they were one, `arb` would be `xrx`.
Lean: `given_distinct`.

**D2. Exactly two beginnings.** On the terms `a`, `b` alone, a legal state that
contains `arb` either asserts `arb` only, or `arb` and `bra`; these differ.
Lean: `two_states_on_given_terms`, `two_states_differ`. Computed:
`evidence/given.json` (count 2). Each is one change from the other (add `bra`;
remove `bra`): `givenA_to_givenB`, `givenB_to_givenA`.

**D3. Which changes are obstructed.** In a legal state: identifying `u` and `v`
is obstructed exactly when `urv` or `vru` is asserted; adding `xry` is
obstructed exactly when `x` and `y` are one term; removing an assertion and
adding a term are never obstructed. Lean: `identify_legal_iff`,
`addAssertion_legal_iff`, `remove_legal`, `addTerm_legal`; for arbitrary (also
infinite) sets of terms `identification_obstructed_iff`, `image_loop_iff`.
Computed check on every change of all 69 legal states written on at most 3
terms: `tests/test_changes.py`.

**D4. Adding `xrx` is obstructed in every state.** No removal and no building
beforehand makes it unobstructed. Lean: `adding_xrx_always_obstructed`.

**D5. What clears an obstruction.** If `urv` is asserted then after any one
performed change either that change removed `urv`, or `urv` is still asserted,
or the change was an identification and the assertion between the replaced
terms is asserted; and a performed identification never merges the two terms of
an assertion. So identifying `u` and `v` stays obstructed until `urv` (and
`vru`) is removed. Lean: `obstruction_persists`, `identify_keeps_apart`. And
once some `xrx` is asserted, every replacement of terms and every addition
leaves some `xrx` asserted; a legal state is reached again only by un-asserting
something: `loop_survives_replacement`, `loop_survives_additions`,
`only_removal_restores`.

**D6. What every result has.** Every result is legal, has at least one term,
and is finite. Lean: `Reach.legal`, `Reach.nonempty` (there is no change that
removes a term; an identification needs two). Finiteness: what is given is
finite and a change adds at most one term or one assertion; in Lean it is built
into the type of states.

**D7. The one irreversible change (ANCHORED).** Once `a` and `b` are one term,
they are one term after every sequence of changes, and `arb` is never asserted
again. Lean: `Reach.names_stay_merged`, `Reach.arb_gone_for_good`. Under FREE
there are no names and every result is reachable from every result (remove
everything, identify down to one term, then D9).

**D8. Fewest changes (cost).** Let what is given have `m0` assertions (`1`
without `bra`, `2` with), so size `2 + m0`. For a legal state `G` with names let
`lost(G)` be the number of given assertions not asserted in `G` between the
terms named `a` and `b` if these are two terms, and `m0 + 1` if they are one
term. Then the fewest changes from what is given to `G` is

    terms(G) + assertions(G) − (2 + m0) + 2 · lost(G).

*Lower bound.* `size + 2·lost` rises by at most one per performed change:
adding raises size by one and loses nothing; a removal lowers size by one and
loses at most one given (one removal cannot be both `arb` and `bra`, since `a`
and `b` are two terms while either is asserted); an identification lowers size
by at least one and loses at most one given (it can merge `a` and `b` only when
nothing is asserted between them, by D3). A refused change changes nothing.
Lean: `Step.costA_le`, `Step.costB_le`, `fewest_changes_lower_A`,
`fewest_changes_lower_B`.
*Upper bound.* Remove the given assertions that `G` lacks; if `a` and `b` are
one term in `G`, identify them; add the missing terms; add the missing
assertions. Lean: `reach_by_edits`, `edits_count`, `givenA_to_oneTerm`,
`givenB_to_oneTerm`, and the two bounds together: `fewest_changes_A`,
`fewest_changes_B`.
*Scope of the Lean statement.* Lean speaks of written states and proves the
lower bound for every state reached, however written, and the upper bound for
states written with `a = 0`, `b = 1` (or `a = b = 0`). Two steps carry this to
results, which are states up to sameness; they are proved here, not in Lean
(O3). (1) Terms, assertions and destroyed givens are counted the same in every
writing, and every state with names has a writing with `a = 0`, `b = 1` or
`a = b = 0`. (2) A sequence of changes on results is a sequence of changes on
written states, because every change commutes with a one-to-one rewriting `π`:
adding the term `t` becomes adding `π(t)`; adding or removing `xry` becomes
adding or removing `π(x) r π(y)`; identifying `u`, `v` becomes identifying
`π(u)`, `π(v)`, since replacing after rewriting is rewriting after replacing;
"new", "asserted", "there" and "two terms" are kept because `π` is one-to-one;
and writing the one term of an identification as `v` instead of `u` is again a
rewriting. Under ANCHORED `π` keeps the names; under FREE the names are dropped
at the end.
*Under FREE* the names may be put anywhere, so the fewest changes is the least
value over all placements. In closed form `lost` becomes: `m0 + 1` for the
one-term state; `m0` if nothing is asserted; `1` if `bra` was asserted to begin
with and the state never asserts both `xry` and `yrx`; `0` otherwise. Computed:
closed form equals best placement on all 476 checks
(`evidence/summary.json`), and the round of first appearance equals the formula
for every explored result under all four combinations (0 mismatches among
9 846 + 9 846 + 2 973 + 2 973).
*Remark (cap on terms).* The sequence of the upper bound never has more terms
than `max(2, terms(G))`. So a cap on the number of terms, and the declared
bound of the exploration, do not change fewest changes.

**D9. Everything legal is a result.** Every finite legal state with at least
one term, with the names on any terms, is a result under either beginning.
Lean: `reach_by_edits` (from any state to any legal state on at least the same
terms with the names in place), with `givenA_to_oneTerm`, `givenB_to_oneTerm`
for the case where `a` and `b` are one term.

**D10. Answers reach nothing new.** Removing the obstruction of an
identification is two or three performed changes (`remove_answer_one_way`,
`remove_answer_two_way`), and removing first or removing the resulting `xrx`
last gives the same state (`remove_obstruction_first_or_last`). A build is
performed additions (`build_answer`, `build_answer_reverse`). Refusal changes
nothing. Hence every answer is a sequence of unobstructed changes, and the set
of results is the set reached by unobstructed changes alone, under any reading
of G9 in which further changes are changes of the four kinds. Computed: for all
24 859 (ANCHORED) and 121 792 (FREE) obstructed attempts within the bound, every
answer's result is an explored result, reached no later than the round of the
state plus the changes the answer performs (`answers_reaching_something_new` is
empty in `evidence/summary.json`).

**D11. Builds.** For an obstructed `xrx` on a state that has `x` and lacks `t`:
adding `t` and `xrt` (or `trx`) and then identifying `t` with `x` gives exactly
the would-be outcome of adding `xrx` (`build_gives_back`,
`build_reverse_gives_back`). No build does with less: a legal state whose terms,
replaced by a map that keeps the old terms, give `xrx`, asserts something new
that mentions a new term (`build_needs_term_and_assertion`). Computed: a state
in which `x` occurs in `d` assertions has `3 · 2^d` builds with one added term
(`tests/test_changes.py`). Remark (computed, FREE only): the one-term state,
asked to add `ara`, has three such builds; up to sameness they are exactly the
two alternatives for what is given (`evidence/given.json`).

**D12. Completeness within the bound.** Let `N` be the bound on terms.
(i) The exploration's results are exactly the legal states with at most `N`
terms. Every explored state is one by construction. Conversely the sequence of
D8's upper bound stays within `max(2, terms) ≤ N` terms; the exploration applies
every change to every result it finds and drops only outcomes with more than `N`
terms; so by induction along that sequence every such state is found.
Certificate (computed, independent method): for every number of terms and
assertions the number of explored results equals the number of legal states
obtained by orbit counting (`explored_equals_independent_count`).
(ii) The round in which a result first appears within the bound is its fewest
changes without any bound: not less, since sequences within the bound are
sequences; not more, by the remark in D8.
(iii) The frontier is exact: only adding a term raises the number of terms, so
the attempts that leave the bound are, for each result with `N` terms, "add a
term" and the two fewest-addition builds for each of its `N` obstructed `xrx`.
Computed: `1 + 2N` leaving attempts per such result (`evidence/frontier_*.csv`).

## 5. What does not follow

Each item has two legal witnesses, or a proof.

**N1. `bra`. N2. Not `bra`.** Both beginnings are legal and contain what is
given. Lean: `bra_not_refuted`, `bra_not_derived`.

**N3. Anything on which the two beginnings differ.** "Never both `xry` and
`yrx`": holds without `bra`, fails with it. "Whenever `xry` and `yrz` then
`xrz`": holds without `bra` (vacuously), fails with it (`arb`, `bra`, no `ara`).
"Every term is first in some assertion": fails without `bra`, holds with it.
"Whenever `xry` then `yrx`": fails without, holds with.
(`evidence/follows_anchored_*.csv`, column `in_what_is_given`.)
Note the conditional fact, which is derived but whose premise is not given: if
asserting passed on from `xry`, `yrz` to `xrz`, then `bra` would be refuted
(`passing_on_refutes_bra`). Since passing on is not given, nothing follows.

**N4. That what is given survives.** `arb` stays asserted: fails after one
change. `a` and `b` stay two: fails after two changes. Exactly two terms: fails
after one. Something is asserted: fails after one.
(`evidence/follows_*.csv`, first rounds 1, 2, 1, 1.)

**N5. Anything about the asserting that is not true of every finite legal
state.** By D9 every finite legal state with at least one term is a result. So a
statement about which assertions are asserted that holds in one such state and
fails in another does not follow. Of the
thirteen statements tested, exactly "no `xrx`" and "at least one term" held in
every result within the bound (`statements_holding_in_every_result`); both are
proved for all results (D6).

**N6. Which answer an obstructed change gets.** Refusal is always possible;
removal is possible exactly for identifications (D4, D5); a build is always
possible (adding a term is never obstructed, D3). No result needs a build, and
no result needs an obstructed change to be attempted at all (D10). The seed's
"must be answered" does not determine the answer.

**N7. Growth, or anything infinite.** Every result is finite (D6). Nothing
forces terms to be added. Whether terms can be added without end is not given
(C3).

**Refuted** (each a proved impossibility): `a` and `b` one term to begin with
(R1, D1); an answer that makes adding `xrx` performable (R2, D4); clearing an
obstructed identification by building, without a removal (R3, D5); a state
without terms (R4, D6); telling `a` and `b` apart again, or asserting `arb`
again, after identifying them (R5, D7); an answer that reaches a result
unobstructed changes do not reach (R6, D10); `bra` together with passing on (R7).

## 6. The exploration

**Protocol.** From each beginning, under each reading of sameness (four runs):
round by round, every change on every result, fewest additions first
(identifications and removals add nothing; then adding a term; then adding an
assertion — the seed's order). For every attempt the change, the obstruction
and every answer are recorded; all three dispositions of an obstructed change
are kept as alternatives. Full logs for the bound of 3 terms:
`evidence/attempts_bound3_*.jsonl` (228 and 1 350 attempts). Attempts on what is
given: `evidence/given.json`.

**The six attempts on what is given, without `bra`** (names kept):

| change | adds | obstruction | outcome or answers |
|---|---|---|---|
| identify `a` and `b` | 0, 0 | `arb` | refused: nothing changes · remove the obstruction: remove `arb`, then identify → one term, nothing asserted (−1, −1) · build: the state itself |
| remove `arb` | 0, 0 | — | `a b`; nothing asserted (0, −1) |
| add a term | 1, 0 | — | `a b c`; `arb` (1, 0) |
| add `ara` | 0, 1 | `ara` | refused · remove the obstruction: impossible (D4) · build: add `c`, add `arc` (1, 1); or add `c`, add `cra` (1, 1) |
| add `bra` | 0, 1 | — | the other beginning (0, 1) |
| add `brb` | 0, 1 | `brb` | refused · impossible · build: add `c`, add `brc`; or add `c`, add `crb` |

With `bra` the list is: identify (obstructed by `arb` and `bra`; removal takes
two removals), remove `arb`, remove `bra`, add a term, add `ara`, add `brb`
(both obstructed).

**Results by what they add to what is given** (ANCHORED, without `bra`, bound 4;
all rows in `evidence/added_*.csv`). A negative number means fewer than given.

| terms added | assertions added | results | first round | last round |
|---|---|---|---|---|
| −1 | −1 | 1 | 2 | 2 |
| 0 | −1 | 2 | 1 | 3 |
| 0 | 0 | 4 | 0 | 4 |
| 0 | 1 | 2 | 1 | 5 |
| 1 | −1 | 2 | 2 | 4 |
| 1 | 0 | 9 | 1 | 5 |
| 1 | 1 | 24 | 2 | 6 |
| 2 | −1 | 2 | 3 | 5 |
| 2 | 0 | 10 | 2 | 6 |
| 1 | 2 | 30 | 3 | 7 |
| 2 | 1 | 50 | 3 | 7 |

Results with the same additions appear in different rounds because of destroyed
givens: `a b; bra` adds (0, 0) like what is given, and needs two changes.

**Rounds.** New results per round within the bound, and without any bound (the
latter from D8 by orbit counting, exact, to round 20; `evidence/rounds_*.csv`):

| round | FREE, no `bra`: bound 5 / no bound | FREE, `bra`: bound 5 / no bound | ANCHORED, no `bra`: bound 4 / no bound | ANCHORED, `bra`: bound 4 / no bound |
|---|---|---|---|---|
| 0 | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| 1 | 3 / 3 | 2 / 2 | 3 / 3 | 3 / 3 |
| 2 | 7 / 7 | 5 / 5 | 9 / 9 | 8 / 8 |
| 3 | 11 / 11 | 14 / 14 | 23 / 24 | 23 / 24 |
| 4 | 23 / 24 | 27 / 28 | 59 / 67 | 57 / 65 |
| 5 | 44 / 51 | 64 / 69 | 135 / 186 | 133 / 184 |
| 10 | 1 168 / 6 512 | 1 589 / 12 986 | 398 / 52 823 | 348 / 52 520 |
| 20 | 5 / 2 007 940 774 | 1 / 6 545 687 688 | 0 / 33 748 590 999 | 0 / 33 697 933 916 |
| last round with a new result within the bound | 22 | 21 | 17 | 18 |
| rounds after that, to 100 | none new | none new | none new | none new |

Rounds `0 … N − 2` within the bound `N` agree with the counts without bound
(a result of round `k` has at most `k + 2` terms); later rounds are complete for
the states within the bound and blind beyond it. No change was invented: after
the last round with a new result, every attempt on every known result repeats a
known result or leaves the bound. Without a bound every round has a new result
(what is given plus `k` new terms costs `k`), so 100 rounds cannot be listed;
the set of results of round `k` is nevertheless determined for every `k` by D8
— membership is a formula — and only its size beyond round 20 is left open (O2).

**Totals.** Results within the bound: 9 846 (FREE; 1, 3, 16, 218, 9 608 by
number of terms) and 2 973 (ANCHORED; 1, 8, 100, 2 864). Changes attempted on
them: 351 130 and 67 222, of which obstructed 121 792 and 24 859. Results in
which every identification is obstructed: 633 and 564; what is given is one of
them under either beginning.

**Frontier.** Every result with `N` terms, each with `1 + 2N` attempts leaving
the bound: 9 608 results and 105 688 attempts (FREE), 2 864 and 25 776
(ANCHORED). `evidence/frontier_*.csv`.

**Reproducibility.** `python code/generate.py` rewrites every computed file;
`evidence/MANIFEST.sha256` lists their hashes; a second run into another folder
gave identical hashes for all 27 files. `python code/lean_report.py` rebuilds
`lean4/` and rewrites `evidence/lean_axioms.txt`. Tests: 80 passed; line
coverage 100.00 %, branch coverage 99.28 % of `code/` (`python code/xry/gate.py`
on the coverage report); `mypy --strict` clean.

## 7. Alternatives: kept, or eliminated by proof

| Alternative | Status |
|---|---|
| `bra` asserted / not asserted to begin with | both kept (N1, N2); all runs done for both |
| FREE / ANCHORED sameness | both kept (C4); all runs done for both |
| `a`, `b` one term to begin with | eliminated (D1) |
| a third legal beginning on the given terms | eliminated (D2) |
| more terms or assertions to begin with | kept as results of the chosen beginning (D9) |
| refuse / remove / build for each obstructed change | all kept in the records; as results they coincide with unobstructed changes (D10) |
| "remove the obstruction" for adding `xrx` | eliminated (D4) |
| builds with more than one added term or assertion | kept as results (they are legal states, D9); not listed as answers beyond the fewest (C7) |
| every legal state within the bound, up to sameness | kept; none dropped (D12) |
| counting an answered change as one | not computed; same results (D10), rounds differ |
| assertions with multiplicity | not explored (O1) |

## 8. Open

- O1. Assertions with multiplicity (C1 unchosen).
- O2. The number of results of rounds 21–100 (finite and determined by D8).
- O3. Lean: the two steps from written states to results (D8, "Scope"): counts
  do not depend on the writing, and changes commute with one-to-one rewriting.
  Proved on paper, checked by computation within the bound, not formalised.
- O4. Listing results beyond the declared bound (the frontier says where to
  continue).
- O5. Readings of "build structure" other than C7: by D10 they cannot change
  the results; they could change which records count as answers.

## 9. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Finite irreflexive relations, that is, loopless directed graphs.** A state
  is one; D9 says the process generates all of them. Their numbers up to
  isomorphism (1, 3, 16, 218, 9 608, 1 540 944 for 1–6 points) and those of
  oriented graphs (1, 2, 7, 42, 582, 21 480) are classical (Harary and Palmer,
  *Graphical Enumeration*; Pólya counting / the Cauchy–Frobenius lemma), and the
  computed counts reproduce them. Different here: the counts with two named
  points (1, 8, 100, 2 864, 224 904, 54 411 072), split by how the named points
  stand to each other, and the counts by cost (section 6).
- **Graph edit distance** (for instance Sanfeliu and Fu, 1983). Fewest changes
  is an edit distance, with two differences: there is no deletion of a point,
  only identification of two non-adjacent points, and the distance is from one
  fixed small graph. For that case D8 gives a closed form, which general edit
  distance does not have. The form "size difference plus twice the destroyed
  givens" and its proof by a potential that rises by at most one per step is the
  standard potential-function method; the statement itself was not found in
  memory as a known result.
- **Identification of non-adjacent vertices; homomorphisms; colourings.**
  Identifying two terms with nothing asserted between them is the elementary
  homomorphism of graph theory. Following identifications alone, the fewest and
  most terms one can end with are the chromatic and the achromatic number of
  the underlying graph (Harary and Hedetniemi); `research/notes.md` checks this
  on 238 states. The seed's process differs by allowing removals and additions,
  which is why every state is reachable and no such invariant survives.
- **Irreflexive plus transitive gives asymmetric** (strict partial orders).
  `passing_on_refutes_bra` is this textbook fact. The seed does not give
  transitivity, and the finding is that `bra` is independent.
- **Independence by exhibiting two models** is the standard method of model
  theory; N1–N5 use nothing more.
- **Loops and their unfoldings.** Replacing a forbidden `xrx` by a new term `t`
  with `xrt` is the smallest case of unfolding a loop (covering constructions,
  the path and the two-cycle over a single loop). D11 is that remark with a
  minimality proof; the observation that what is given is itself such an
  unfolding of a one-term `xrx` is elementary and is only recorded.

What appears to be specific to this seed: the protocol of obstruction and
answer is conservative (D10); the cost of a result counts each destroyed given
twice (D8); and with names kept, the identification of the two given terms is
the only irreversible event (D7).
