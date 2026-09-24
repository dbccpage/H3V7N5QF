# Change log, fourth derivation

Each material change, and its reason. Newest last. Commits are on the branch
the run started on (`worktree-third-derivation`, the worktree of this
repository in which the third derivation was made; the branch was brought to
`origin/main` before any work of the fourth derivation).

1. **`CLAUDE.md` gained the fourth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/fourth/prompt.md`. The earlier plans above it are unchanged.

2. **The state model is new (`code/fourth/state.py`, `lean4/Fourth/State.lean`):
   a state has a multiplicity for each ordered pair of terms.** Reason: the
   seed counts assertions, and the earlier model (asserted or not) cannot hold
   a multiplicity. The earlier model is kept as the *support* of a counted
   state and an earlier state is read as a counted state asserting everything
   once (the *indicator*); these two maps are how every earlier result is cited
   and re-checked (rule 5 of the task). Under the reading ANCHORED the least
   writing now puts the names first, so `a` is always written first (`terms a
   b …`); nothing mathematical depends on which writing is least.

3. **Layout: a new package `code/fourth/` importing from `code/xry/`,
   `code/second/` and `code/third/` only what the multiplicity leaves intact;
   no earlier module is modified.** Reason: the task allows changes to the
   earlier derivations' files only to correct a defect, and none was found.
   Imported: the sameness readings, the kinds of change and answer kinds, the
   CSV / JSON / manifest writers and `compare_evidence`, `given_size`, the
   cycle-length machinery of the orbit counts, the fewest-classes count and the
   earlier statements tested (both on the support), the Lean report runner, and
   the third derivation's exploration, sequence count and reachability for the
   comparison. Defined afresh: states, sameness, the list of changes (re-adding
   an asserted assertion is now a change: `1 + n²` changes per state), the
   answers, the exploration (bounded in terms and rounds), containment and
   reachability with multiplicities, the cost, the counts that never decrease,
   the independent count by series, the statements about multiplicity, the
   number of sequences per result.

4. **Every exploration is bounded in terms and in rounds, and three
   explorations are written per beginning and reading (5 or 4 terms with 8
   rounds; 3 terms with 12 rounds; 2 terms with all 100 rounds).** Reason:
   within any bound on terms the results are infinite (the multiplicity of
   `arb` alone can be anything), so the third derivation's bound on terms
   alone no longer makes a run finite. With the given terms only, the seed's
   100 rounds complete. The frontier has two parts: the attempts leaving the
   term bound (exported as before) and the results of the last round, whose
   changes await the next round (listed in the results file with their round
   and a `changes_attempted` flag).

5. **The independent count of results uses a series `1 / (1 − x^L)` per cycle
   of the rewriting's action on pairs instead of the earlier binomial
   `(1 + x^L)`, and counts by total multiplicity.** Reason: a rewriting fixes
   a counted state exactly when the multiplicity is constant along each
   cycle. The results asserting nothing twice are counted by the third's
   method beside it (`counts.csv`), and the two explorations are compared on
   them.

6. **Every obstructed attempt records "remove the obstruction: impossible:
   the obstruction is the assertion the change itself adds, raising its
   multiplicity from none to one; no change lowers a multiplicity, and not
   adding it is refusal".** Reason: the seed asks to declare and record the
   answer; the wording is the third derivation's restated for multiplicities
   (C7).

7. **The one-term builds answering "add `xrx`" are exactly two (`xrt`, `trx`),
   where the third derivation listed `3 · 2^d`.** Reason: with multiplicities
   counted, reading the added term as `x` adds up the multiplicities of the
   pairs that become one pair, so both directions together, or a copy of an
   assertion of `x`, would stand for more than the would-be outcome
   (`is_build_of`, `one_term_builds`; `tests/test_fourth_changes.py` checks
   every candidate with small multiplicities).

8. **The third derivation's exploration, sequence counts and reachability are
   run beside the fourth's in every run, census and reachability file, and
   compared on the results asserting nothing twice.** Reason: rule 5 of the
   task — the third's computed claims are cited, and their re-check is that
   the fourth's results asserting nothing twice, their rounds, their sequence
   counts and their reachability are exactly the third's.

9. **Lean: a fourth library `Fourth` in the same Lake package, with a counted
   state `MSt`, the changes `Step4`, and the two maps `ofSt` (indicator) and
   `toSt` (support) to and from the earlier states.** Reason: the state changes,
   so the earlier `Step2` cannot be reused as the fourth seed's change; the
   maps are the formal form of rule 5: every change of the third seed is a
   change of the fourth on indicator states (`Step2.toStep4`), and a change of
   the fourth whose outcome asserts nothing twice is a change of the third on
   the supports (`Step4.toStep2`). The lakefile of the first derivation gained
   the library target and a default target; that edit is recorded in
   `paper/change_log.md` (item 22).

10. **All six Lean targets of the plan closed**, including target 5
    (`rename4`, `Step4.rename`, `Reach4.rename`, the every-writing statements)
    and target 6 (`Fourth/Compare.lean`: reachability, cost, containment and
    one-way reachability coincide with the third's on states asserting
    nothing twice). Two name clashes were repaired during the build: the
    bridging theorems are declared in the third library's namespaces
    (`Seed.Third.Step2.toStep4`, `Seed.Third.Reach2.toReach4`,
    `Seed.Third.Contains.ofSt`) so that dot notation works on the third's
    relations, and a theorem first named `Contains4.of_toSt` made `toSt`
    resolve to `Contains4.toSt` inside its own statement and is named
    `contains4_of_toSt`. No statement changed.

11. **Two defects of the new code found by its tests during the run, both in
    the fourth's own files.** (a) The check that no count decreases compared a
    state with the least writing of its outcome, where the terms may be
    written differently; it now compares with the outcome as performed. (b)
    The two-term sequence check read the names of the beginning as `0`, `1`
    regardless of the writing; it now reads them from the state. No claim
    changed; no evidence had been written.

12. **The Lean build of this derivation was interrupted twice by a full
    disk.** Another session on the same machine was fetching a Mathlib cache
    for a different toolchain at the time; the build was retried once the
    space was back. No file outside the repository was touched and nothing was
    downloaded by this derivation; the pinned packages are still the local
    junction to the main checkout's `lean4/.lake/packages`.

13. **The re-runs of the earlier derivations' checks were cut short by the
    environment.** One background run regenerated `evidence/fourth/`, checked
    it against a fresh regeneration (matched), re-ran the first and second
    derivations' `--check` (both matched), and had started the third's
    `--check` when the session's tooling stopped it because the machine was
    low on memory (another session was running Lean at the time). The third's
    `--check` and the three earlier Lean reports (`python code/lean_report.py`,
    `python code/lean_report_second.py`, `python code/lean_report_third.py`)
    were therefore not repeated in this session, and the tooling asked that
    they not be restarted unasked. What stands instead: `git diff --stat`
    against the branch's starting point shows no change to `code/xry/`,
    `code/second/`, `code/third/`, `lean4/H3V7N5QF/`, `lean4/Second/`,
    `lean4/Third/`, their tests or `evidence/`, `evidence/second/`,
    `evidence/third/`, so those regenerations have the same inputs as when
    they last matched; and `python code/lean_report_fourth.py` built all four
    libraries. The four commands above complete the check (about ten
    minutes).

14. **The reachability file lists only the rows that carry information.** With
    3 terms and 6 rounds there are 490 results and 240 100 ordered pairs
    under ANCHORED; listing every pair made two files of 14 MB each. Every
    pair is still tested both ways and the totals are in `summary.json`; the
    file lists every reachable pair with its embedding and every pair of
    results asserting nothing twice with the third derivation's verdict, so a
    pair absent from it is unreachable with a multiplicity above one on one
    side (`rows_written` in the summary). Made before the first commit of the
    evidence; no number changed.

15. **Review fixes: a dropped negative test restored, and full coverage
    regained.** A review of the derivation's pull request found that the
    FREE-cost differential check (`check_free_cost`, which cross-checks the
    closed form `cost_free` against the best-placement form
    `cost_free_by_placement`) had no injection test, unlike the first and
    second derivations (`tests/test_evidence.py`, `tests/test_second_evidence.py`,
    each with `monkeypatch.setattr(evidence, "cost_free", ...)`): the two
    formulas always agree, so the mismatch-recording line was never executed
    and a regression making the check vacuous would have passed green. Added
    `test_free_cost_check_reports_a_disagreement`, which forces a disagreement
    and asserts every checked state is recorded, plus
    `test_independent_count_skips_terms_beyond_the_size_bound` and
    `test_free_count_of_no_terms_is_empty` for the two defensive guards
    (`_counted`'s `degree < 0` skip, `_free`'s zero-terms return), and
    `# pragma: no cover` on the `__main__` guard of `code/generate_fourth.py`
    and `code/lean_report_fourth.py` (as `fourth/__main__.py` already carries).
    Line coverage returns to 100%. No derivation code, evidence, claim, or
    claim status changed; the checks the tests exercise are unchanged.

## Whole-repo review repairs (2026-09-23)

- F005: printed four cited parent theorems and regenerated the Lean report and manifest. F013: filled O2 evidence with the existing D14/D17 series and generated round files; the claim and status are unchanged.
