# What follows when `xrx` is not forbidden, and is still obstructed

Seventeenth derivation. Input: `prompt/seventeenth/seed_prompt.md`. Task:
`prompt/seventeenth/prompt.md`. The parent is the base
(`prompt/seed_prompt.md`, `paper/paper.md`, `code/xry/`, `lean4/H3V7N5QF/`).
Claim IDs refer to `paper/seventeenth/claim_ledger.md`; an ID written `1:D8`
refers to the base ledger (`paper/claim_ledger.md`). Lean names in the
namespace `Seed.Seventeenth` are in `lean4/Seventeenth/`; names in `Seed` are
the base's. Computed files are in `evidence/seventeenth/`, written by
`python code/run_seventeenth.py`. The axiom report is
`evidence/seventeenth/lean_axioms.txt`, written by
`python code/lean_report_seventeenth.py`. Every theorem it prints depends
only on `propext`, `Classical.choice` and `Quot.sound`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; the unchosen
readings are listed), **derived** (proved), **computed** (output of `code/`),
**refuted** (proved impossible), **open**.

Where a result of the base is used it is cited and re-checked from this
seed, and the re-check says whether it rested on the struck sentence ("for
no term `x` may `xrx` be asserted") or only on the obstruction paragraph,
which is kept. The re-check is one of: *no change* (the statement mentions
no ban and no change); *re-proved* (a `Step17` theorem that does not assume
the ban); *through the embedding* (an unobstructed `Step17` on a loop-free
state is a base `Step`, and conversely); *computed again* (this exploration
against `xry.explore` on the results that assert no `xrx`).

## 0. Findings in brief

1. The seed is the base seed with one sentence struck: "For no term `x` may
   `xrx` be asserted." The obstruction paragraph is unchanged. A change that
   makes some `xrx` asserted is still obstructed and must still be answered.
2. "Makes some `xrx`" has two readings, both kept. **M1** (chosen; the base's
   obstruction): the assertions that would become some `xrx`. **M2**
   (unchosen): the outcome asserts some `xrx`, whether or not the change just
   made it. On a loop-free state they name the same changes (derived). On a
   state that already asserts `ara`, identifying two other terms with nothing
   between them is obstructed under M2 and not under M1 (derived).
3. What is done with an obstructed change has two readings, both kept.
   **A-replace** does not enter it (the base). **A-perform** enters it, and
   the outcome is a result. Refusal still changes nothing, under both.
4. Under A-replace, from either beginning, every result asserts no `xrx`
   (derived, and computed on the bound). The obstruction rule together with
   "do not enter an obstructed change" reconstructs the struck sentence for
   the results. The base's results, rounds and cost survive on that set,
   through the embedding.
5. Under A-perform the predicate `has_xrx` is true of a reached result.
   Adding `ara` to what is given, and identifying `a` with `b` while `arb`
   is asserted, are each one change, and each outcome asserts `ara`. The
   struck sentence is not redundant under this reading. The base cost of the
   one-term outcome is 3 without `bra` and 4 with `bra`; the length is 1, so
   the base cost is not a lower bound (derived).
6. Remove-then-identify and identify-then-remove end at the same state
   (the base's theorem, re-checked). Only the second path has an `xrx` in
   between, and under A-perform that intermediate is a result.
7. The process does not terminate: adding a term is never obstructed under
   M1 and produces a new state, so every round has a new result if no bound
   is imposed (derived, written). Declared bound: 3 terms and 6 rounds, both
   beginnings, both readings of sameness. The frontier exports both cuts:
   every attempt whose outcome has more than 3 terms, and every result first
   reached in round 6, whose changes the round bound left unattempted. The
   round bound binds: every A-perform run, and A-replace with names kept,
   still found new results in round 6 (computed, `unexpanded_by_run`).
   Within the declared bound A-replace is certified by listing every
   loop-free state whose base cost is at most 6. A-perform is the
   breadth-first closure; there is no separate count of every state that
   asserts `xrx` (the count is partial, O4).

## 1. What the seed gives

`diff` of `prompt/seventeenth/seed_prompt.md` against `prompt/seed_prompt.md`
deletes one bullet and nothing else:

- For no term `x` may `xrx` be asserted.

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2 | An assertion is written `xry`, where `x` and `y` are terms. |
| G3 | `arb` is asserted. |
| G4 | Struck. Not a sentence of this seed. |
| G5 | Whether `bra` is asserted is not given. |
| G6 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G8 | A change that makes some `xrx` asserted is obstructed. |
| G9 | An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which; record the change, the obstruction, the answer. |
| G10 | A refused change is recorded and changes nothing. |
| G11 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative; do not invent a change; if too many, declare a finite bound, export the exact frontier, prove what is complete within it. |
| G14 | Any outcome is valid. |

G14 is what lets an outcome that asserts `xrx` stand, once G4 is not there
to withdraw it.

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, assertion `xry`, `arb` | given (G1–G3) | |
| no `xrx` as a rule for every state | refuted as a given (G4) | the predicate `has_xrx` / `LoopFree` is derived as a predicate, not a given |
| `bra` not given | given (G5) | both alternatives kept (C2) |
| four kinds of change | given (G6, G7) | |
| what is not a change | chosen (C5) | the base's reading; it does not use G4 |
| obstructed | given (G8) | what "makes" covers: M1 chosen, M2 kept (C7) |
| refuse / remove the obstruction / build | given (G9, G10) | whether the obstructed change is entered: A-replace and A-perform, both kept |
| result | chosen (C6) | up to sameness; under A-replace, a loop-free state; under A-perform, any outcome of `perform` |
| sameness, two readings | given (G12); chosen (C4) | both kept |
| round; one performed change counts one | chosen (C6) | a refusal counts as an attempt and not as a change |
| bound, frontier | given (G13); the numbers chosen (C8) | the frontier has a `\|terms` entry for each attempt past the term bound and a `\|rounds` entry for each result the round bound left unexpanded |
| what a result adds to what is given | given (G11) | recorded per result in `results_bound3_rounds6.csv` (K5) |
| `has_xrx` | derived | true when some `xrx` is asserted |
| base cost | cited (1:D8) | re-checked: a lower bound along A-replace; not along A-perform |

## 3. Readings that had to be chosen

**C2.** To begin with there are the terms `a`, `b`, `arb` asserted, and `bra`
either asserted or not. Unchosen, kept, and computed: the same, plus `ara`;
the same, plus `brb`. The base set those aside because G4 forbade them. G4
is gone, so they are not dropped. Under A-replace neither is a result of the
chosen beginning. Under A-perform each is one addition (computed, K1).

**C4.** Sameness under both readings, names kept (ANCHORED) and any rewriting
(FREE). Nothing in the seed picks one.

**C5.** Adding what is asserted, removing what is not, and identifying a term
with itself are not changes. A new term carries no assertion. An added
assertion is between terms that are there. Read off "exactly one of" and
"nothing else". Unchanged from the base.

**C6.** A result is a state up to sameness reached by performed changes.
Under A-replace an obstructed change is not performed. Under A-perform it
is. One performed change counts one. Round `k` attempts the changes of the
results first reached in round `k − 1`, fewest additions first (the base's
`xry.explore.order`, reused).

**C7, two pairs.**

- M1, chosen. The obstruction is the assertions that would become some `xrx`:
  for identifying `u` and `v`, `urv` and `vru` if asserted; for adding `xrx`,
  that assertion. An `xrx` already asserted does not obstruct an unrelated
  change. This is `xry.changes.obstruction`, and `Step17.obstructedM1`.
- M2, unchosen, kept. A change is obstructed when its outcome asserts some
  `xrx`. This is `Step17.obstructedM2`.
- A-replace, the base's reading of G9. The obstructed change is not entered.
  Refusal changes nothing. Removing the obstruction is those removals, then
  the change. Building is additions only, as in `xry.changes.answers`.
- A-perform, kept because G4 no longer makes the outcome impossible. The
  obstructed change is performed. Refusal still does not perform it.

**C8.** Bound: 3 terms and 6 rounds, for all four runs (both values of `bra`,
both readings of sameness). Full attempt log at 2 terms and 3 rounds. The
plan's wider bounds were not run; this is the bound that is certified. 100
rounds are not listed (D10).

## 4. What follows

**On a loop-free state, M1 and M2 agree.** `m1_iff_m2_of_loopFree`: for each
of the four kinds, the outcome asserts some `xrx` exactly when M1 says so.
The "related, hence the outcome asserts `xrx`" direction is the base's
`identify_legal_iff` and does not assume the ban as a hypothesis on every
state; the converse uses loop-freeness of the start. Adding `xrx` is
obstructed under M1 with no loop-free hypothesis
(`adding_xrx_step_obstructed`, `adding_xrx_obstructed`). Computed: on every
A-replace result within the bound, the two tests name the same changes
(`m_disagree_loopfree` empty).

**They do not agree once `ara` is asserted.** `loopyWitness` has terms
`0, 1, 2`, asserts `0r0`, and asserts nothing between `1` and `2`.
Identifying `1` with `2` is not obstructed under M1 (`loopy_m1_allows`) and
is obstructed under M2 (`loopy_m2_obstructs`), because `0r0` is still
asserted. Computed: `m_agree_on_loop` empty (the tests differ).

**An unobstructed step keeps loop-freeness.** From a loop-free state, a
`Step17` that is not M1-obstructed has a loop-free outcome
(`Step17.loopFree_out`, `Step17.no_xrx_of_unobstructed`). A sequence of such
steps stays loop-free (`Reach17.loopFree`). So under A-replace, from either
beginning, no result asserts `xrx`. Computed: `replace_has_xrx` empty at 3
terms and 6 rounds. This is the sense in which the obstruction rule
reconstructs the struck sentence: only together with not entering the
obstructed change.

**The base's unobstructed steps are these steps.** Every base `Step` is an
unobstructed `Step17` (`Step.toStep17`, `Step.unobstructed17`). Every
unobstructed `Step17` is a base `Step`, with no hypothesis on the state
(`Step17.toStep`). Sequences match (`Reach.toReach17`, `Reach17.toReach`).
The base's side-conditions (no added `xrx`; an identification only of
unrelated terms) are exactly M1, not an extra ban.

**The base cost survives along those sequences.** For a loop-free
well-formed state with `a = 0` and `b ∈ {0, 1}`, the fewest unobstructed
changes from either beginning is the base formula (`fewest_changes17_A`,
`fewest_changes17_B`), by the embedding into `fewest_changes_A` and
`fewest_changes_B` (1:D8). The lower bound along any unobstructed sequence
is the same (`fewest_changes17_lower_A`, `fewest_changes17_lower_B`).
Computed: every A-replace result's round equals `xry.cost.cost`, and the
set of results is exactly the loop-free states of at most 3 terms whose
base cost is at most 6 (`replace_cost_mismatch` and `replace_not_formula`
empty; `replace_not_base` empty, so the closure is `xry.explore`).

**Performing the obstructed change leaves the base cost.** Identifying `a`
with `b` in what is given is one `Step17` (`identify_givenA_step`, and the
same for the beginning with `bra`). The outcome is the one-term state
asserting `ara`, with both names on that term (`names_merged_with_loop`,
`mergedA_hasXrx`). Lean's `costA` of that state is 6 and `costB` is 8
(`cost_not_lower_bound_A`, `cost_not_lower_bound_B`): the base formula says
the fewest changes are `costA − 3 = 3` without `bra` and `costB − 4 = 4`
with `bra`, and neither is ≤ 1. Adding `ara` is likewise one step whose
outcome asserts `ara` (`add_ara_hasXrx`) and which no unobstructed sequence
reaches (`add_ara_not_unobstructed`). Computed: the same one-term state is
at round 1 in every A-perform run, and `xry.cost.cost` of it is greater
than 1 (`perform_misses_witness` and `perform_cost_not_above` empty).

**Answers.** Removing `urv` and `vru` and then identifying equals
identifying and then removing the `xrx` that results
(`remove_first_eq_perform_first`, which is the base's
`remove_obstruction_first_or_last` on a loop-free start). The intermediate
of the second path asserts `xrx` (`perform_first_intermediate_has_xrx`), so
the equality does not show that intermediate is not a result. Under
A-perform it is a result (`perform_first_givenA` is a `ReachAll` of length
2). Refusal of adding `ara` does not enter: the step is M1-obstructed, and
no unobstructed sequence from what is given reaches its outcome
(`refusal_does_not_enter`). Computed: the base answer's removal and
perform-then-remove end at the same state, and the refusal returns the
start (`remove_first_differs` and `refusal_changes_something` empty).

**What does not use the ban.** Well-formedness, at least one term, and
"once `a` and `b` are one term they stay one term" hold of every `Step17`,
obstructed or not (`Step17.wf`, `Step17.nonempty`, `Step17.names_stay_merged`,
and the same for `Reach17` and `ReachAll`). An injective rewriting carries
steps, unobstructed sequences, and sequences that may be obstructed
(`Step17.rename`, `Reach17.rename`, `ReachAll.rename`), and it carries
loop-freeness (`loopFree_rename`).

**It does not terminate.** `Step17.addTerm` is a change, and
`Step17.obstructedM1` of that constructor is `False`, so the change is
unobstructed under M1 and is entered under both readings. The new term was
not there, so the outcome is a different state, with one more term. From
any state, repeating it produces a new result at every later round. No
bound on terms was given (1:C3, the base's reading, kept). The seed's 100
rounds are therefore not a last round. The declared bound is the cut, not
a theorem that the process stops.

## 5. What does not follow

Each item has a witness where it holds and one where it fails, or a proof
that it cannot hold.

- **Every well-formed state asserts no `xrx`.** Holds of every A-replace
  result (`Reach17.loopFree` from either beginning; `replace_has_xrx` empty).
  Fails of the one-term state asserting `ara` (`oneLoop_hasXrx`, reached in
  one A-perform step).
- **A-replace and A-perform have the same results.** They do not. Adding
  `ara`, adding `brb`, and identifying `a` with `b` are in the A-perform
  closure and not in the A-replace closure (computed, K1;
  `add_ara_not_unobstructed` for the first).
- **M1 and M2 disagree on a loop-free state.** They do not
  (`m1_iff_m2_of_loopFree`). They do disagree on `loopyWitness`.
- **The base cost is the fewest changes once an obstructed change is
  performed.** It is not (`cost_not_lower_bound_A`, `cost_not_lower_bound_B`).
  It is the fewest along unobstructed steps (`fewest_changes17_A`,
  `fewest_changes17_B`, for names at `0` and at `0` or `1`).
- **`a` and `b` are two terms in every result.** They are two terms in what
  is given (the chosen beginning has `a = 0`, `b = 1`). They are one term
  in the outcome of identifying them (`names_merged_with_loop`). After they
  are one term, no later change of either reading makes them two again
  (`ReachAll.names_stay_merged`).
- **Once `a` and `b` are one term, `arb` is never asserted again.** Along
  unobstructed steps from a loop-free state the base's
  `Reach.arb_gone_for_good` applies, because `Reach17.toReach` supplies a
  base `Reach` (the result stays loop-free, so `(a, a)` is not asserted).
  It fails of the perform-first identification: `(a, a)` is asserted
  (`arb_not_gone`). Read as a statement about two terms, there is nothing
  left to assert `arb` of, because the two terms are gone.

## 6. The exploration

Both readings are breadth-first, fewest additions first, the same order as
`xry.explore`. A-replace skips a change whose base obstruction is non-empty.
A-perform enters `perform` of every change. An outcome with more terms than
the bound is frontier, not a result.

Declared bound (C8): 3 terms, 6 rounds, four runs. The check
`seventeenth.evidence.check_bounds` compares, on that bound:

- the A-replace closure with `xry.explore`, state by state and round by round;
- each A-replace round with `xry.cost.cost`;
- the set of A-replace results with the set of loop-free states of at most
  3 terms whose base cost is at most 6 (listed by masks and name placements,
  then the least writing — not by walking the changes);
- the A-perform closure against the one-step identification witness;
- M1 against M2 on the A-replace results, and on `loopyWitness`;
- the base's remove-answer against perform-then-remove;
- the refusal of adding `ara` against the state it was refused on;
- the two unchosen beginnings against both closures.

Every disagreement list is empty (`summary.json`, `passes` true). The four
runs, from `by_run`, with the results first reached in round 6 from
`unexpanded_by_run` in brackets:

| Run | A-replace | A-perform |
|---|---|---|
| any rewriting, `bra` not asserted | 20 (1) | 105 (17) |
| names kept, `bra` not asserted | 85 (15) | 486 (171) |
| any rewriting, `bra` asserted | 20 (0) | 111 (15) |
| names kept, `bra` asserted | 76 (10) | 486 (171) |

Summed: 201 A-replace results and 1188 A-perform results. The frontier,
one line each and prefixed by the run and the reading, has two kinds of
entry: `|terms`, an attempt whose outcome has more than 3 terms (874), and
`|rounds`, a result first reached in round 6, whose changes the round bound
left unattempted (400). Together they are the exact frontier of the
declared bound. Only the A-replace run with any rewriting and `bra`
asserted has no `|rounds` entry: it finished inside 3 terms before round 6.
`results_bound3_rounds6.csv` records, for each of the 1389 results, the run,
the reading, how many terms and assertions it adds to what is given, the
round it is first reached, and whether it asserts `xrx` (G11). The attempt
log at 2 terms and 3 rounds is `attempts_bound2_rounds3.jsonl`.

The A-replace listing is the completeness certificate inside the bound: a
loop-free state of at most 3 terms is a result exactly when its base cost
is at most 6, and then the round is that cost. That is 1:D8 and 1:D9
restricted to this bound, computed again.

The A-perform closure is not certified against a listing of every
well-formed state. A state can assert `xrx`, and the base cost is not its
round, so the legal-state count does not apply. Every A-perform run still
found new results in round 6, so the round bound, not exhaustion, ended
it; whether it would grow further inside 3 terms is not decided (O4).
Paths that leave the term bound and return are not searched (O3). The round recorded for an A-perform result is
the shortest sequence that stays inside the bound; a path of that length
exists, and it is not proved to be the fewest among all sequences.

## 7. Which base results survive

| Base claim | Rested on the struck sentence? | Here |
|---|---|---|
| `Legal` as a filter on every state (1:G4) | yes | not a given; `LoopFree` is a predicate |
| `a ≠ b` whenever `arb` is asserted (`given_distinct`) | yes, it assumes `Legal` | survives for a loop-free asserting; fails as a claim about every A-perform result (`names_merged_with_loop`) |
| exactly two states on the given terms (`two_states_on_given_terms`) | yes, it assumes `Legal` | survives for loop-free states; a third state on those terms asserts `ara` (`add_ara_reach`) |
| adding `xrx` is obstructed (`adding_xrx_always_obstructed`) | the outcome is not `Legal`; the proof does not assume the start is | survives (`adding_xrx_obstructed`); it does not by itself keep the outcome out of the results |
| base `Step` (no diagonal, no related identification) | yes, the constructors | the unobstructed fragment is `Step17` (`Step17.toStep`); A-perform adds the other steps |
| `Step.legal` / `Reach.legal` | yes, hypothesis `Legal` | re-proved as loop-freeness along unobstructed steps; false along `ReachAll` |
| at least one term; well-formedness; names once merged stay merged | no | re-proved for `Step17` and for `ReachAll` |
| cost formula (1:D8) | the paths stay loop-free | survives along `Reach17`; not a lower bound along `ReachAll` |
| `arb` gone once the names are one term (`Reach.arb_gone_for_good`) | yes, the result stays `Legal` | survives along `Reach17` via `Reach17.toReach`; fails for the perform-first merge (`arb_not_gone`) |
| answers reach nothing new (1:D10) | the obstructed outcome is not a result | the final state of the removal answer is still an unobstructed result; the intermediate is a result under A-perform |
| `bra` neither derived nor refuted | the two models are loop-free | survives for loop-free assertings (`bra_not_derived`, `bra_not_refuted`); not a claim about states that assert `xrx` |

## 8. Alternatives kept

- A-replace and A-perform. Neither contains the other (section 5).
- M1 and M2. They coincide on loop-free states and differ off them, so
  neither is dropped.
- Both beginnings, `bra` asserted or not.
- Both readings of sameness.
- The unchosen beginnings that also assert `ara` or `brb`. They are results
  under A-perform and not under A-replace. No proof eliminates them.

## 9. Open

- **O2.** A closed form for the fewest A-perform changes. The base formula
  is refuted as a lower bound (section 4). No replacement is proved.
- **O3.** Whether an A-perform sequence that exceeds the term bound and
  returns can be shorter than the recorded round. The recorded round is the
  shortest sequence that stays inside the bound.
- **O4.** An independent count of the states that assert some `xrx`, against
  which the A-perform closure could be certified the way A-replace is
  certified by the loop-free listing. Not done. The frontier is exported
  instead.
- **O5.** The base cost at a writing where the names are not `a = 0` and
  `b ∈ {0, 1}`. `Step17.rename` carries the steps; `fewest_changes17_A` and
  `fewest_changes17_B` still assume that writing. The computation uses
  `xry.cost.cost` on the least writing, which is not that Lean statement.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Loopless directed graphs, and directed graphs that may have a loop.**
  The base's results are the loopless ones (1:D9). A-replace stays inside
  that class, by refusing the step that would add a loop. A-perform steps
  into the larger class: one identification produces a one-vertex graph
  with a loop. The struck sentence is the loopless restriction; the
  obstruction paragraph is the refusal, and the refusal is what does the
  work.
- **Graph edit distance.** The base formula (1:D8) is an edit distance from
  one fixed small graph, and it is a lower bound only while every step stays
  loopless. One loop-creating identification costs 1 and the formula returns
  3 or 4. That gap is the whole of `cost_not_lower_bound_A` and
  `cost_not_lower_bound_B`.
- **Identification of adjacent vertices.** Identifying two terms with
  nothing asserted between them is still the elementary homomorphism that
  the base used. Identifying two terms that do have an assertion between
  them is a homomorphism onto a graph with a loop. A-replace does not take
  that step; A-perform does, and then removing the loop ends at the same
  graph as removing the assertion first (`remove_first_eq_perform_first`).
  The two orders differ in the intermediate, which the ban had excluded and
  which is now a result.

What appears to be specific to this seed: the obstruction rule reconstructs
"no `xrx`" for the results only when the obstructed change is not entered;
once it is entered, a result asserts `xrx`, the base cost is not a lower
bound, and the two names can be one term with `ara` asserted.
