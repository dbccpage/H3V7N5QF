# Change log, seventh derivation

Each material change, and its reason. Newest last. Commits are on the branch
the run started on (`worktree-third-derivation`, the worktree of this
repository in which the third to sixth derivations were made; the branch was
brought to `origin/main` — which had merged the sixth derivation and
installed the seventh and eighth seeds — before any work of the seventh
derivation).

1. **`CLAUDE.md` gained the seventh derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/seventh/prompt.md`. The earlier plans above it are unchanged.

2. **The state model is the fourth derivation's `MState` with its names left
   out (`names = None`); `remove` and `identify` are the fifth's, imported
   unchanged; a state with no terms is the beginning.** Reason: the seed
   drops the given and with it the names; the model always allowed
   `names = None` (the FREE reading never carried them) and `n = 0` (the
   first derivation refuted the empty state as a result and kept it in the
   model), so nothing about the state or its operations changes in Python —
   only which state begins and which states are results. In Lean the sixth's
   `MSt` carries the names as fields and its well-formedness puts them among
   the terms, so a state without terms is not well formed there: a state
   without names, `NSt`, is defined, with the two maps `MSt.forget` and
   `NSt.name` between the models.

3. **Layout: a new package `code/seventh/` importing from the earlier
   packages only what the given and the names leave intact; no earlier
   module is modified.** Reason: the task allows changes to the earlier
   derivations' files only to correct a defect, and none was found in a file
   the seventh derivation uses as it stands. Imported: the counted state and
   its sameness under any rewriting, `support`, `of_state`, the cache of
   least writings, `remove`, `identify`, the change record, the four kinds,
   the list of changes and `perform`, the two-change cycle, the sixth's
   `count_free` (the count of all well-formed states by terms and total
   multiplicity, the diagonal pairs among the cycles), the unnamed
   statements tested, the fewest-classes count, the writers, the Lean report
   runner, and the sixth's exploration, cost, `attempt_counts`, `counts_upto`
   and reachability for the comparison. Not imported, being about the given
   or the names: `given`, `added` (written again as terms and total
   multiplicity), `names_one_term`, `named_xrx`, `lost`, `lost_free`,
   `merged_optimal`, `raises_by_one`, `count_named`, `counts_by_lost`,
   `layer_counts`, `two_term_round_count`, the named statements, and the
   sixth's `explore` (it required a start with a term). Defined afresh: the
   empty beginning, the attempt record, the exploration from an empty state,
   the cost as the size, the rule that exactly the additions raise it, the
   has-a-term criterion, the unconditional exactness of the shortest-sequence
   counts, the independent count with the empty state, the two-term closed
   form, the comparison with the sixth through forgetting the names.

4. **One beginning and one reading of sameness.** Reason: the seed gives
   nothing (no `bra` alternative), and with no names the rewritings keeping
   the names are all rewritings (D12), so the two readings coincide; every
   exploration is run once instead of the sixth's four times.

5. **The comparison with the sixth runs the sixth's explorations four rounds
   fewer than the seventh's, from both its beginnings under both its
   readings.** Reason: a sixth result's size is at most its sixth-seed cost
   plus four (its destroyed givens are at most three, its given size four),
   so every sixth result then lies within the seventh's rounds; the results
   with a term whose sixth-seed cost is within the sixth's rounds must be
   exactly the sixth's results, each at the round its cost formula gives, and
   the named results with their names forgotten must be the same states.
   Both halves are checked on every run and the census.

6. **The record of an attempt keeps the sixth's "makes some `xrx` asserted"
   flag.** Reason: it is a property of the outcome the sixth derivation
   counted (its former obstructed attempts), and the seventh's totals must
   equal the sixth's function on the results with a term
   (`xrx_making_equal_sixth_formula`); nothing in the seventh seed refers to
   it otherwise.

7. **`count_shortest_sequences` checks, on every change it follows, that a
   change raising the round is an addition.** Reason: D4(vi) says every
   shortest sequence is additions only; the dynamic programme over the
   round-raising changes is then a check of that theorem on every explored
   change, not only a count.

8. **Lean: a seventh library `Seventh` in the same Lake package, importing
   `Sixth`; the lakefile gained the target (recorded in
   `paper/change_log.md`, item 25).** The plan's targets 1–5 all closed on the
   first attempt, target 5 (rewriting, the every-writing statement) included;
   two proofs needed a second compile (a `simp` call that unfolded the empty
   state before rewriting its total, and the binder names of an induction
   alternative). Reused through the two maps: the sixth's well-formedness of
   a change, its size lemmas, its addition path (`reach6_of_contains`), its
   criterion (`reach6_of_names`), its two-change cycle, its cost potential
   (for the witness that it fails), and the fourth's and fifth's rewriting
   lemmas. Written afresh without names: the state, the empty state, the
   term case of every invariant (no naming reaches the empty state), the
   first change, the one-way exit from the empty state, and "every shortest
   sequence is additions only" (`AddReach7`).

9. **Bounds raised above the plan's targets after timing.** The plan named 5
   terms with 10 rounds, 3 terms with 12, 2 terms with 30 and a census at 6
   terms with 10 rounds; the independent count sizes the runs in advance
   (7 231 / 8 760 / 18 071 / 7 588 results), so they were raised to 11, 14,
   40 and 12 rounds (22 686 / 29 191 / 56 111 / 82 749 results; 20 MB of
   evidence; about eleven minutes in all, the sixth's comparison runs
   included). The seed's 100 rounds with two terms would hold about 2.1
   million results (D11) and are not run.

10. **Slips found by the tests during the run, all in the seventh's own test
    files, none in the derivation's code.** Numbers guessed before the
    evidence existed (the two-term results within 7 rounds, the attempts in
    the small log, the results of the small census and its awaiting results,
    the results per round within 3 terms beyond round 3 — which lack the
    states with more terms than the bound — and the number of statements
    tested) were corrected to the computed values; a least writing was
    guessed the other way round; one injection test drove a change that the
    empty state cannot write and was given a term instead; one test compared
    a summary value with an integer under `mypy --strict` and was given the
    exact value. No evidence had been written.

11. **Review pass over paper and ledger after the first draft.** The
    witnesses of N4 and N5 were rewritten with the least writings the
    evidence uses (`a b; bra`, not `a b; arb`, is the least writing of the
    two-term state with one assertion between its terms) and their sequence
    counts (2, 3, 8) read off `results_bound5_rounds11.csv`. No claim or
    status changed.

12. **Re-runs of the earlier derivations' checks.** After this work the six
    earlier `--check`s (`python code/generate.py --check`, `_second`,
    `_third`, `_fourth`, `_fifth`, `_sixth`) and the six earlier Lean
    reports were re-run; their outcomes are recorded here once known (item
    13).

13. **Outcome of the re-runs (item 12).** `python code/generate.py --check`,
    `python code/generate_second.py --check`, `python code/generate_third.py
    --check`, `python code/generate_fourth.py --check`, `python
    code/generate_fifth.py --check` and `python code/generate_sixth.py
    --check` each reported a match with a fresh regeneration (67, 270, 294,
    157, 521 and 913 seconds here); `python code/lean_report.py`, `_second`,
    `_third`, `_fourth`, `_fifth` and `_sixth` each built all seven libraries
    and rewrote their `lean_axioms.txt` and manifest byte-identically
    (`git status` shows no change under `evidence/`, `evidence/second/`,
    `evidence/third/`, `evidence/fourth/`, `evidence/fifth/` or
    `evidence/sixth/`). So the evidence of all six earlier derivations still
    regenerates. The seventh's own `python code/generate_seventh.py --check`
    matched (973 seconds, beside other runs), after `python
    code/generate_seventh.py` (654 seconds) and `python
    code/lean_report_seventh.py`.

## Whole-repo review repairs (2026-09-23)

- F013: filled the O4 carry-forward evidence cell with the fourth seed and existing D10 series/round files. No claim or status changed.
