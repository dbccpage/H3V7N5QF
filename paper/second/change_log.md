# Change log, second derivation

Each material change, and its reason. Newest last. Commits are on the branch
the run started on (`second-derivation`). Nothing was pushed during the run;
the branch was pushed afterwards at the user's request (item 12).

1. **`CLAUDE.md` gained the second derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/second/prompt.md`. The first derivation's plan above it is
   unchanged.

2. **Layout: a new package `code/second/` that imports from `code/xry/`; no
   first-derivation module is modified.** Reason: the task allows changes to
   the first derivation's files only to correct defects. What is reused is
   imported (states, sameness, the counts, the writers, the attempt records);
   what the seed changes is defined afresh (the list of changes, the answers,
   the exploration, the cost, the counts of results, reachability, the
   invariant). `second.changes.changes` builds the list directly and a test
   checks it equals the first derivation's list without its removals;
   `second.changes.perform` refuses a removal.

3. **Every obstructed attempt records "remove the obstruction: impossible: no
   change un-asserts an assertion".** Reason: the seed asks to declare and
   record the answer; under this seed that answer exists in name only (R3),
   and the record says so rather than silently omitting it.

4. **The exploration is also run with identifications left out, and the two
   are compared.** Reason: D10 claims that additions alone reach every result
   in the same round; the comparison is its computed check.

5. **Bounds: ANCHORED files exported at 4 terms, with a counts-only census at
   5 terms.** Reason: an ANCHORED run at 5 terms takes about a minute and
   passes every check, but its per-result and frontier files would have about
   90 000 rows per alternative; the census keeps the completeness certificate
   and the cost check at 5 terms without those files. Its frontier is counted,
   not exported; the paper says so (C8, §6).

6. **Lean: a second library `Second` in the same Lake package; the second
   seed's changes are a new inductive `Step3` with an embedding into the
   first's `Step`.** Reason: the embedding is the formal form of the task's
   rule 5 — every first-derivation theorem about changes that is cited is
   restricted through it, and the restriction is itself a theorem. The
   lakefile of the first derivation gained the library target and a default
   target; that edit is recorded in `paper/change_log.md` (item 20) as the
   task requires for a first-derivation file.

7. **Plan target 5 (rewriting) was reached**: `Step3.rename`, `Reach3.rename`,
   `size_rename`, and with them `result_iff_A/B` and
   `fewest_changes3_every_writing_A/B` for every writing. The first
   derivation's open item 1:O3 is thereby closed for the changes of this seed;
   the first derivation's files are not changed, so its ledger still lists it.

8. **The "if" direction of D12 for carrying maps that merge terms is proved on
   paper and left open in Lean (O3).** Reason: it needs, after the
   identifications along the map, the extension of a one-to-one map on a
   finite set of terms to a rewriting of all terms; the one-to-one case and the
   additions are in Lean, the merging step is not. Bounded effort as planned.

9. **Two test expectations written during the run were wrong and were
   corrected; one correction became a claim.** (a) Four terms each asserting
   the next around to the first have no carrying map onto three terms so
   arranged (the test now uses six terms so arranged, which have one). (b) With `bra` given, "passing on" holds in no result; the test
   had expected a witness. (b) was added to the paper as D15 and R7. Reason for
   recording: the second changed what the paper claims.

10. **Lean proof repairs without change of statement.** `cases` patterns must
    not name the index variable of `Step3`; `| refl s` must be `| refl`; a
    reverse `rw` whose pattern is a metavariable application was replaced by
    `show … from` rewrites; `simpa` was told to unfold `St.addTerm`; two `rw`
    closures were replaced by `omega` / `simp`. No statement changed.

11. **Two log files of the background runs (`.generate_second.log`,
    `.generate_second_check.log`) were deleted before the commit.** Reason:
    they are not evidence (they hold no numbers the summary lacks) and are not
    regenerable by a committed command.

12. **The branch `second-derivation` was pushed to `origin` after the run, at
    the user's request** (commits `31c0850` … `7d752e4`, then this entry).
    `CLAUDE.md`'s "nothing is pushed" describes the run itself and is left as
    written; no pull request was opened. Nothing else changed.

13. **Review fix: an illegal state is unreachable, so its cost is `None`
    (`code/second/cost.py`).** Found in a code review of this branch.
    `cost_anchored` and `cost_free` tested whether a state contains what is
    given (or, without names, asserts something) but not whether it is *legal*;
    an illegal state (some `xrx` asserted) is never a result, yet the tests
    admitted one and returned a finite — sometimes negative — size difference
    (`cost_free(State(1,1), True)` returned `-2`), disagreeing with
    `cost_free_by_placement`. Both now return `None` for an illegal state, the
    documented value for an unreachable one. No evidence changes: every
    explored result is legal and `check_free_cost` only ever compared legal
    states (`free_cost_closed_form_checked_on: 476` unchanged), so
    `--check` still matches byte for byte and no `evidence/second/` number
    moves. A regression test (`tests/test_second_cost.py::
    test_illegal_states_are_unreachable`) was added, and the launcher smoke
    test was strengthened to assert a launcher-specific flag (it had asserted
    only `--out`, which both launchers print, so it could not catch a launcher
    wired to the other's `main`). Test count in K10 / §6 accordingly 178 → 179;
    coverage (line 100.00 %, branch 99.24 %) unchanged.

14. **Review fix: the plan and notes were reworded to the seed's own words.**
    `paper.md` already honoured the rule that outside results are named only in
    its final section (§9); but a few forward-looking lines of the Phase-0 plan
    (`CLAUDE.md`, second-derivation section), the reading notes
    (`research/second/reading_the_seed.md`), and this log had named outside
    notions directly — for the shape of reachability between results, for the
    term-map reachability criterion and the sequence invariant, for how this
    exploration sits inside the first's, and for states made of several terms
    each asserting the next with the last asserting the first. Each was reworded
    to the repository's own words (reachability composes and is not one-way; the
    carrying-map criterion and invariant; the exploration is contained in the
    first's; such states written out by their assertions). Only wording changed;
    no prediction, notion, or result moved, and `paper.md` §9 is untouched. The
    exact edits are in the commit diff.

15. **Two verification gates were ported in from the genesis repository
    (`dbccpage/19L57G1`), after item 14 showed the outside-word rule had no
    mechanical guard.** (a) `ci/check_prose_watchlist.py` with
    `ci/prose_watchlist.json`: a digest-stored census of outside-theory terms
    that fails on any whole-word hit its per-file pin does not already record.
    The current tree is clean; all 35 pinned hits sit in the two papers' §9
    "nearest known results" sections, the one place the rule permits them.
    `tests/test_prose_watchlist.py` runs the census over the tracked tree, so
    `python -m pytest` enforces it (the repository has no hosted CI). (b)
    `tests/test_second_cost.py::test_cost_is_none_exactly_off_the_result_set`:
    a property that `cost` is `None` exactly off the result set, checked over
    every state — legal and illegal, both name readings, to three terms — so
    the item-13 legality guard cannot silently regress; it exercises the
    illegal states that `check_free_cost` skips. `pyproject.toml` now type-checks
    `ci/` too. Tests 179 → 193; coverage of `code/` unchanged (the gate lives in
    `ci/`, outside the measured source). No object-language notion or result
    changed.

## Whole-repo review repairs (2026-09-23)

- F003: printed seven cited base theorems in Second/Axioms.lean and regenerated the Lean report and manifest. No theorem statement changed.
