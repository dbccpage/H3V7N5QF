# Change log

Each material change, and its reason. Newest last. Commits are on the branch
the run started on; nothing was pushed.

1. **`CLAUDE.md` written and committed before anything else.**
   Reason: required by `prompt/prompt.md`.

2. **`lean4/lakefile.toml`: added a `lean_lib` target and `defaultTargets`.**
   Reason: the file as found declared only the Mathlib requirement, so
   `lake build` had nothing of this repository to build.

3. **`lean4/.lake/packages` is a local junction to the packages fetched before
   the run in the main checkout.** Reason: no network; `.lake/` is ignored by
   git, so nothing of it is committed.

4. **`pyproject.toml` at the root (tool configuration only); the Python package
   is `code/xry`, not `code`.** Reason: a package named `code` would shadow the
   standard library module `code`, which the test runner imports.

5. **`.gitattributes`: `evidence/** -text`.** Reason: evidence files are hashed
   in `evidence/MANIFEST.sha256`; line-ending conversion would break the hashes.

6. **Reading of "build structure": two readings tried and dropped, a third
   kept (C7).** Dropped: "perform the change, then repair the state" — from a
   state with `xrx` only a removal restores legality (D5), so building could
   never replace removal. Dropped as the only reading: "build until the change
   is unobstructed" — never succeeds for adding `xrx` (D4), and for an
   identification only removal succeeds (D5). Kept: the build stands in for the
   obstructed change (identifying the added terms back gives its would-be
   outcome). Reason for tolerating a choice here: D10 shows the results do not
   depend on it.

7. **The exploration spreads along unobstructed changes and checks answers
   afterwards, instead of spreading along answers too.** Reason: an answer
   performs several changes; spreading along it would give rounds that mix two
   ways of counting. With D10 nothing is lost, and the check
   (`check_answers`) verifies that for every obstructed attempt.

8. **Two readings of sameness carried through every computation** (not one,
   as first drafted). Reason: the literal reading of G12 (any rewriting) makes
   `arb` alone and `bra` alone the same result, while G11 compares results with
   a given that names `a` and `b`; neither reading could be eliminated.

9. **Lean, `Cost.lean`: destroyed givens rewritten through a helper `miss` and
   case lemmas.** Reason: the first version (nested `if`, `split_ifs`, `omega`)
   did not close four goals. Statements unchanged.

10. **Lean target 6 of the plan (the upper bound) was reached**, so D8 is in
    Lean in both directions for states written with `a = 0`, `b ∈ {0, 1}`. The
    remaining gap (invariance under rewriting) is recorded as open O3 rather
    than hidden.

11. **Incident: wrong Lean toolchain.** `lake -d lean4 build` run from the
    repository root used elan's default toolchain (4.34.0), not the pinned
    4.33.1 (the `lean-toolchain` file is inside `lean4/`). Lake began
    rebuilding dependencies in the shared package folder with the wrong
    compiler and failed. Repair: rebuilt with
    `lake +leanprover/lean4:v4.33.1 -d lean4 build`; 304 dependency modules were
    rebuilt with the pinned compiler, Mathlib itself was not, and the build
    completed (3008 jobs). All later builds name the toolchain or run inside
    `lean4/`. Noted in `research/notes.md` §5.

12. **Launchers `code/generate.py`, `code/lean_report.py`; coverage measured on
    all of `code/`.** Reason: run the generators without setting
    `PYTHONPATH`; the task asks for coverage of `code/`, not of the package
    only. Coverage went from 100 % / 100 % on `code/xry` to 100.00 % line,
    99.28 % branch on `code/` (the two untaken branches are the launchers'
    "imported, not run" side).

13. **`evidence/given.json` gained `builds_answering_xrx_on_one_term`.**
    Reason: D11's remark (the one-term builds of `xrx` are, up to FREE
    sameness, the two beginnings) needed computed support.

14. **Paper, D3: "603 writings" corrected to "69 legal states".** Reason: the
    first number was wrong (1 + 4 + 64 = 69 legal states written on 1–3 terms).

15. **`CLAUDE.md`: a "How to run" section appended.** Reason: the commands
    changed (items 11, 12). The plan and stopping conditions are unchanged.

16. **Not in the repository:** `.claude/settings.local.json` (ignored by git)
    received an allow-list for the commands used here, at the user's request
    during the run. The checked-in `.claude/settings.json`, including its
    network denials, was not touched.

## Operator corrections at review (2026-09-18)

Made by the operator while reviewing the branch, after the run; not by the run.
Each corrects a statement, narrows a claim to its evidence, or makes a check
enforce what the paper already asserted. None adds a result, a proof, or a
reading of the seed.

17. **Records.** Item 16's last sentence does not hold for the branch: operator
    commit `b335f95` (00:55, between the plan commit and the first code commit)
    changed `.claude/settings.json` during the run, adding `defaultMode:
    bypassPermissions` and an allow-list of tools. The header's "nothing was
    pushed" held when written; the branch was pushed at the user's request after
    the run. `CLAUDE.md` "How to run" gains `--check` (item 19).

18. **Claims narrowed to their evidence** (paper and ledger):
    - N4: the first rounds differ by beginning (1, 2, 1, 1 without `bra`;
      1, 3, 1, 2 with it), as `evidence/follows_*.csv` records.
    - D5, R3: the Lean statements are for one change; the step to a sequence of
      changes is the paper's argument. New open item O6.
    - D7 and §0, §9: "the one thing that cannot be undone" / "the only
      irreversible event" withdrawn to "cannot be undone": nothing cited proves
      that every other change can be undone.
    - D9, D10: names in other places, and the removal answer when only `vru` is
      asserted, rest on the rewriting step (O3), not on Lean.
    - D10: the computed check covers the answers within the bound; those beyond
      it belong to the frontier and are not checked.
    - D11: `build_needs_term_and_assertion` shows a new assertion mentioning a
      term outside the old terms, not that the build has a new term; the test
      of `3 · 2^d` covers one state and not completeness.
    - D12 (iii), §6, K4: the frontier has `1 + N` leaving attempts and
      `1 + 2N` entries per state (57 648 / 105 688 FREE, 14 320 / 25 776
      ANCHORED); the numbers 105 688 and 25 776 had been called attempts.
    - C3: harmless for results and fewest changes; not claimed for answers.
    - C6, §6: the protocol as run — each result's changes attempted once, in
      the round after it is first reached, fewest additions first within the
      result. The results do not depend on this.
    - C7: "declare which" is stated as read (all answers recorded with their
      kind, all kept); the dropped readings cite D4, D5, not `research/`.
    - §7: "remove the obstruction" for `xrx` is eliminated under C7's reading;
      multiplicity is open, not eliminated. N7 given witnesses; its finiteness
      part is derived (D6), not "does not follow". §6: the count of results in
      which every identification is obstructed is of results with at least two
      terms. §2: "added to what is given" is counted against `a`, `b`, `arb`
      for both beginnings. D12, §6: the independent count is named by what it
      counts. §9: `research/notes.md` is marked as not evidence. Ledger:
      falsifiers for R1–R7.

19. **Checks made to enforce what was asserted** (`code/`, `tests/`):
    - `code/xry/leanreport.py` refuses the report when the build warns of
      `sorry` or a `#print axioms` line lists anything outside `propext`,
      `Classical.choice`, `Quot.sound`; its scan also sees `sorryAx` and axioms
      after attributes and modifiers; Lean's output is decoded as UTF-8 (the
      Windows default code page cannot decode it).
    - `python code/generate.py --check` compares `evidence/` with a fresh
      regeneration in both directions (K7).
    - The generator's pass line now also requires a non-empty comparison with
      the unbounded counts, the frontier's `1 + 2N` entries, no disagreement in
      the FREE closed form, and no listed build that is not a build; the last
      two were `assert` statements, skipped under `python -O`. `--rounds`
      below the bound no longer indexes past the run.
    - `summary.json` gains `frontier_entries`,
      `frontier_entries_are_1_plus_2N_per_state_with_N_terms`,
      `free_cost_closed_form_mismatches`, `listed_builds_that_are_not_builds`;
      `frontier_attempts` now counts attempts. No other evidence file changed.
    - `pytest` writes `coverage.json` for `code/xry/gate.py`, which checks the
      two rates separately (`--cov-fail-under` checks one combined figure).
    - A `lean-toolchain` at the repository root, a copy of
      `lean4/lean-toolchain`, so `lake` run from the root uses the pinned
      toolchain (item 11).

## Changes made during the second derivation (`prompt/second/`)

20. **`lean4/lakefile.toml`: a second library target `Second` and
    `defaultTargets = ["H3V7N5QF", "Second"]`.** Made by the second
    derivation. Not a defect correction: it is the build configuration of the
    shared Lake package, and the only first-derivation file the second
    derivation touched; recorded here as `prompt/second/prompt.md` requires
    for any change to a first-derivation file. Nothing in `lean4/H3V7N5QF/`,
    `code/xry/`, `tests/test_*.py` (first set), `paper/paper.md`,
    `paper/claim_ledger.md` or `evidence/` changed. After the edit
    `python code/generate.py --check` matched and `python code/lean_report.py`
    rewrote `evidence/lean_axioms.txt` byte-identically (its build now also
    compiles `lean4/Second/`; its report still prints the first library's
    axioms only). The second derivation's own changes are logged in
    `paper/second/change_log.md`.

## Changes made during the third derivation (`prompt/third/`)

21. **`lean4/lakefile.toml`: a third library target `Third` and
    `defaultTargets = ["H3V7N5QF", "Second", "Third"]`.** Made by the third
    derivation. Not a defect correction: it is the build configuration of the
    shared Lake package, and the only first-derivation file the third
    derivation touched; recorded here as `prompt/third/prompt.md` requires for
    any change to a first- or second-derivation file (no second-derivation
    file changed). Nothing in `lean4/H3V7N5QF/`, `lean4/Second/`, `code/xry/`,
    `code/second/`, the first or second test sets, the earlier papers,
    ledgers, `evidence/` or `evidence/second/` changed. After the edit
    `python code/generate.py --check` and `python code/generate_second.py
    --check` matched, and `python code/lean_report.py` and
    `python code/lean_report_second.py` rewrote their reports byte-identically
    (their builds now also compile `lean4/Third/`; each report still prints
    its own library's axioms only). The third derivation's own changes are
    logged in `paper/third/change_log.md`.

## Changes made during the fourth derivation (`prompt/fourth/`)

22. **`lean4/lakefile.toml`: a fourth library target `Fourth` and
    `defaultTargets = ["H3V7N5QF", "Second", "Third", "Fourth"]`.** Made by
    the fourth derivation. Not a defect correction: it is the build
    configuration of the shared Lake package, and the only earlier-derivation
    file the fourth derivation touched; recorded here as
    `prompt/fourth/prompt.md` requires for any change to an earlier
    derivation's file. Nothing in `lean4/H3V7N5QF/`, `lean4/Second/`,
    `lean4/Third/`, `code/xry/`, `code/second/`, `code/third/`, the earlier
    test sets, the earlier papers, ledgers, `evidence/`, `evidence/second/` or
    `evidence/third/` changed. The first and second derivations' `--check`
    were re-run after the edit and matched; the third's `--check` and the
    three earlier Lean reports were stopped by the environment before they
    finished and not repeated (`paper/fourth/change_log.md`, item 13); the
    fourth's Lean report built all four libraries. The fourth derivation's own
    changes are logged in `paper/fourth/change_log.md`.

## Changes made during the fifth derivation (`prompt/fifth/`)

23. **`lean4/lakefile.toml`: a fifth library target `Fifth` and
    `defaultTargets = ["H3V7N5QF", "Second", "Third", "Fourth", "Fifth"]`.**
    Made by the fifth derivation. Not a defect correction: it is the build
    configuration of the shared Lake package, and the only earlier-derivation
    file the fifth derivation touched; recorded here as
    `prompt/fifth/prompt.md` requires for any change to an earlier
    derivation's file. Nothing in `lean4/H3V7N5QF/`, `lean4/Second/`,
    `lean4/Third/`, `lean4/Fourth/`, `code/xry/`, `code/second/`,
    `code/third/`, `code/fourth/`, the earlier test sets, the earlier papers,
    ledgers, `evidence/`, `evidence/second/`, `evidence/third/` or
    `evidence/fourth/` changed. The four earlier `--check`s and the four
    earlier Lean reports were re-run after the edit (`paper/fifth/change_log.md`,
    items 12 and 15). The fifth derivation's own changes are logged in
    `paper/fifth/change_log.md`.

## Changes made during the sixth derivation (`prompt/sixth/`)

24. **`lean4/lakefile.toml`: a sixth library target `Sixth` and
    `defaultTargets = ["H3V7N5QF", "Second", "Third", "Fourth", "Fifth",
    "Sixth"]`.** Made by the sixth derivation. Not a defect correction: it is
    the build configuration of the shared Lake package, and the only
    earlier-derivation file the sixth derivation touched; recorded here as
    `prompt/sixth/prompt.md` requires for any change to an earlier
    derivation's file. Nothing in `lean4/H3V7N5QF/`, `lean4/Second/`,
    `lean4/Third/`, `lean4/Fourth/`, `lean4/Fifth/`, `code/xry/`,
    `code/second/`, `code/third/`, `code/fourth/`, `code/fifth/`, the earlier
    test sets, the earlier papers, ledgers, `evidence/`, `evidence/second/`,
    `evidence/third/`, `evidence/fourth/` or `evidence/fifth/` changed. The
    five earlier `--check`s and the five earlier Lean reports were re-run
    after the edit (`paper/sixth/change_log.md`, items 13 and 15). The sixth
    derivation's own changes are logged in `paper/sixth/change_log.md`.

## Changes made during the seventh derivation (`prompt/seventh/`)

25. **`lean4/lakefile.toml`: a seventh library target `Seventh` and
    `defaultTargets = ["H3V7N5QF", "Second", "Third", "Fourth", "Fifth",
    "Sixth", "Seventh"]`.** Made by the seventh derivation. Not a defect
    correction: it is the build configuration of the shared Lake package,
    and the only earlier-derivation file the seventh derivation touched;
    recorded here as `prompt/seventh/prompt.md` requires for any change to
    an earlier derivation's file. Nothing in `lean4/H3V7N5QF/`,
    `lean4/Second/`, `lean4/Third/`, `lean4/Fourth/`, `lean4/Fifth/`,
    `lean4/Sixth/`, `code/xry/`, `code/second/`, `code/third/`,
    `code/fourth/`, `code/fifth/`, `code/sixth/`, the earlier test sets, the
    earlier papers, ledgers, `evidence/`, `evidence/second/`,
    `evidence/third/`, `evidence/fourth/`, `evidence/fifth/` or
    `evidence/sixth/` changed. The six earlier `--check`s and the six earlier
    Lean reports were re-run after the edit (`paper/seventh/change_log.md`).
    The seventh derivation's own changes are logged in
    `paper/seventh/change_log.md`.

## Changes made during the eighth derivation (`prompt/eighth/`)

26. **`lean4/lakefile.toml`: an eighth library target `Eighth` and
    `defaultTargets = ["H3V7N5QF", "Second", "Third", "Fourth", "Fifth",
    "Sixth", "Seventh", "Eighth"]`.** Made by the eighth derivation. Not a
    defect correction: it is the build configuration of the shared Lake
    package, and the only earlier-derivation file the eighth derivation
    touched; recorded here as `prompt/eighth/prompt.md` requires for any
    change to an earlier derivation's file. Nothing in `lean4/H3V7N5QF/`,
    `lean4/Second/`, `lean4/Third/`, `lean4/Fourth/`, `lean4/Fifth/`,
    `lean4/Sixth/`, `lean4/Seventh/`, `code/xry/`, `code/second/`,
    `code/third/`, `code/fourth/`, `code/fifth/`, `code/sixth/`,
    `code/seventh/`, the earlier test sets, the earlier papers, ledgers,
    `evidence/`, `evidence/second/`, `evidence/third/`, `evidence/fourth/`,
    `evidence/fifth/`, `evidence/sixth/` or `evidence/seventh/` changed. The
    seven earlier `--check`s and the seven earlier Lean reports were re-run
    after the edit (`paper/eighth/change_log.md`). The eighth derivation's
    own changes are logged in `paper/eighth/change_log.md`.

## Changes made during the ninth derivation (`prompt/ninth/`)

27. **`lean4/lakefile.toml`: a ninth library target `Ninth` and
    `defaultTargets = ["H3V7N5QF", "Second", "Third", "Fourth", "Fifth",
    "Sixth", "Seventh", "Eighth", "Ninth"]`.** Made by the ninth derivation.
    Not a defect correction: it is the build configuration of the shared Lake
    package, and the only earlier-derivation file the ninth derivation
    touched; recorded here as `prompt/ninth/prompt.md` requires for any
    change to an earlier derivation's file. Nothing in `lean4/H3V7N5QF/`,
    `lean4/Second/`, `lean4/Third/`, `lean4/Fourth/`, `lean4/Fifth/`,
    `lean4/Sixth/`, `lean4/Seventh/`, `lean4/Eighth/`, `code/xry/`,
    `code/second/`, `code/third/`, `code/fourth/`, `code/fifth/`,
    `code/sixth/`, `code/seventh/`, `code/eighth/`, the earlier test sets, the
    earlier papers, ledgers, `evidence/`, `evidence/second/`,
    `evidence/third/`, `evidence/fourth/`, `evidence/fifth/`,
    `evidence/sixth/`, `evidence/seventh/` or `evidence/eighth/` changed.
    The eight earlier `--check`s (`python code/generate.py --check` through
    `python code/generate_eighth.py --check`) and the eight earlier Lean
    reports (`python code/lean_report.py` through
    `python code/lean_report_eighth.py`) were re-run after the ninth library
    was added; each `--check` matched a fresh regeneration and each Lean
    report rewrote its axiom file byte-identically. The ninth derivation's
    own changes are logged in `paper/ninth/change_log.md`.

## Changes made during the tenth derivation (`prompt/tenth/`)

28. **`lean4/lakefile.toml`: a tenth library target `Tenth` and
    `defaultTargets = ["H3V7N5QF", "Second", "Third", "Fourth", "Fifth",
    "Sixth", "Seventh", "Eighth", "Ninth", "Tenth"]`.** Made by the tenth
    derivation. Not a defect correction: it is the build configuration of
    the shared Lake package, and the only earlier-derivation file the tenth
    derivation touched; recorded here as `prompt/tenth/prompt.md` requires
    for any change to an earlier derivation's file. Nothing in
    `lean4/H3V7N5QF/` … `lean4/Ninth/`, `code/xry/` … `code/ninth/`, the
    earlier test sets, the earlier papers, ledgers, or `evidence/` through
    `evidence/ninth/` was modified. The tenth derivation's own changes are
    logged in `paper/tenth/change_log.md`.

## Changes made during the eleventh derivation (`prompt/eleventh/`)

29. **`lean4/lakefile.toml`: an eleventh library target `Eleventh` and
    `defaultTargets = [..., "Tenth", "Eleventh"]`.** Made by the eleventh
    derivation. Not a defect correction: it is the build configuration of
    the shared Lake package, and the only earlier-derivation file the
    eleventh derivation touched; recorded here as
    `prompt/eleventh/prompt.md` requires for any change to an earlier
    derivation's file. Nothing in `lean4/H3V7N5QF/` … `lean4/Tenth/`,
    `code/xry/` … `code/tenth/`, the earlier test sets, the earlier papers,
    ledgers, or `evidence/` through `evidence/tenth/` was modified. The
    eleventh derivation's own changes are logged in
    `paper/eleventh/change_log.md`.

## Changes made during the twelfth derivation (`prompt/twelfth/`)

30. **`lean4/lakefile.toml`: a twelfth library target `Twelfth` and
    `defaultTargets = [..., "Eleventh", "Twelfth"]`.** Made by the twelfth
    derivation. Not a defect correction: it is the build configuration of
    the shared Lake package, and the only earlier-derivation file the
    twelfth derivation touched; recorded here as
    `prompt/twelfth/prompt.md` requires for any change to an earlier
    derivation's file. Nothing in `lean4/H3V7N5QF/` … `lean4/Eleventh/`,
    `code/xry/` … `code/eleventh/`, the earlier test sets, the earlier papers,
    ledgers, or `evidence/` through `evidence/eleventh/` was modified. The
    twelfth derivation's own changes are logged in
    `paper/twelfth/change_log.md`.

## Changes made during the thirteenth derivation (`prompt/thirteenth/`)

31. **`lean4/lakefile.toml`: a thirteenth library target `Thirteenth` and
    `defaultTargets = [..., "Twelfth", "Thirteenth"]`.** Made by the thirteenth
    derivation. Not a defect correction: it is the build configuration of
    the shared Lake package, and the only earlier-derivation file the
    thirteenth derivation touched; recorded here as
    `prompt/thirteenth/prompt.md` requires for any change to an earlier
    derivation's file. Nothing in `lean4/H3V7N5QF/` … `lean4/Twelfth/`,
    `code/xry/` … `code/twelfth/`, the earlier test sets, the earlier papers,
    ledgers, or `evidence/` through `evidence/twelfth/` was modified. The
    thirteenth derivation's own changes are logged in
    `paper/thirteenth/change_log.md`.

## Changes made during the fourteenth derivation (`prompt/fourteenth/`)

32. **`lean4/lakefile.toml`: a fourteenth library target `Fourteenth` and
    `defaultTargets = [..., "Thirteenth", "Fourteenth"]`.** Made by the fourteenth
    derivation. Not a defect correction: it is the build configuration of
    the shared Lake package, and the only earlier-derivation file the
    fourteenth derivation touched; recorded here as
    `prompt/fourteenth/prompt.md` requires for any change to an earlier
    derivation's file. Nothing in `lean4/H3V7N5QF/` … `lean4/Thirteenth/`,
    `code/xry/` … `code/thirteenth/`, the earlier test sets, the earlier papers,
    ledgers, or `evidence/` through `evidence/thirteenth/` was modified. The
    fourteenth derivation's own changes are logged in
    `paper/fourteenth/change_log.md`.

## Changes made during the fifteenth derivation (`prompt/fifteenth/`)

33. **`lean4/lakefile.toml`: a fifteenth library target `Fifteenth` and
    `defaultTargets = [..., "Fourteenth", "Fifteenth"]`.** Made by the fifteenth
    derivation. Not a defect correction: it is the build configuration of
    the shared Lake package, and the only earlier-derivation file the
    fifteenth derivation touched; recorded here as
    `prompt/fifteenth/prompt.md` requires for any change to an earlier
    derivation's file. Nothing in `lean4/H3V7N5QF/` … `lean4/Fourteenth/`,
    `code/xry/` … `code/fourteenth/`, the earlier test sets, the earlier papers,
    ledgers, or `evidence/` through `evidence/fourteenth/` was modified. The
    fifteenth derivation's own changes are logged in
    `paper/fifteenth/change_log.md`.


## Changes made during the sixteenth derivation (`prompt/sixteenth/`)

34. **`lean4/lakefile.toml`: a sixteenth library target `Sixteenth` and
    `defaultTargets = [..., "Fifteenth", "Sixteenth"]`.** Made by the sixteenth
    derivation. Not a defect correction: it is the build configuration of
    the shared Lake package, and the only earlier-derivation file the
    sixteenth derivation touched; recorded here as
    `prompt/sixteenth/prompt.md` requires for any change to an earlier
    derivation's file. Nothing in `lean4/H3V7N5QF/` … `lean4/Fifteenth/`,
    `code/xry/` … `code/fifteenth/`, the earlier test sets, the earlier papers,
    ledgers, or `evidence/` through `evidence/fifteenth/` was modified. The
    shared `ci/` gates gained a sixteenth panel and record noun, logged in
    `paper/sixteenth/change_log.md`, as are the sixteenth derivation's own
    changes.

## Changes made during the seventeenth derivation (`prompt/seventeenth/`)

35. **`lean4/lakefile.toml`: a seventeenth library target `Seventeenth` and
    `defaultTargets = [..., "Sixteenth", "Seventeenth"]`.** Made by the
    seventeenth derivation. Not a defect correction: it is the build
    configuration of the shared Lake package, and the only earlier-derivation
    file this derivation touched; recorded here as
    `prompt/seventeenth/prompt.md` requires for any change to an earlier
    derivation's file. Nothing in `lean4/H3V7N5QF/` … `lean4/Sixteenth/`,
    `code/xry/` … `code/sixteenth/`, the earlier test sets, the earlier papers,
    ledgers, or `evidence/` through `evidence/sixteenth/` was modified.

## Changes made during the nineteenth, twentieth, and twenty-first derivations

36. **`lean4/lakefile.toml`: library targets `Nineteenth`, `Twentieth`, and
    `Twentyfirst`, and the same three names on `defaultTargets`.** Made by
    this run. Not a defect correction: it is the build configuration of the
    shared Lake package. Each library imports `H3V7N5QF` only. Nothing in
    `lean4/H3V7N5QF/` … `lean4/Sixteenth/`, `code/xry/` … `code/sixteenth/`,
    the earlier test sets, the earlier papers, or `evidence/` through
    `evidence/sixteenth/` was modified. `ci/check_mutation_bite.py` gained
    one panel per derivation, logged in each paper's `change_log.md`.

37. **`lean4/lakefile.toml`: library target `Eighteenth`, and the name on
    `defaultTargets`** (missing from item 36, which the eighteenth's run
    preceded). Made by the eighteenth derivation, which imports `H3V7N5QF`
    only. `ci/check_mutation_bite.py` gained an eighteenth panel, logged in
    `paper/eighteenth/change_log.md`.

38. **Review of the eighteenth through twenty-first derivations.** Repairs are
    logged in each derivation's `change_log.md`. Shared files touched:
    `ci/check_mutation_bite.py` (the eighteenth, twentieth and twenty-first
    panels gain or change bite cases for the repaired checks; the seventeenth
    to twenty-first panels are put in order, with the blank lines between
    them restored), `lean4/lakefile.toml` (a final newline), and `CLAUDE.md`
    (the eighteenth plan moved after the seventeenth's, where the merge had
    put it before). Nothing in `lean4/H3V7N5QF/` … `lean4/Seventeenth/`,
    `code/xry/` … `code/seventeenth/`, or `evidence/` through
    `evidence/seventeenth/` was modified.

39. **Whole-repo review citation detector (2026-09-23).** Findings F001–F010
    identified cited Lean names absent from ten derivations' own axiom
    reports. The shared `ci/check_axiom_citations.py` checks backticked
    theorem/lemma citations against each Lean-generated report. Its test
    removes and restores the second derivation's real `Reach.legal` report
    line, proving the missing-line defect fires. `ci/OEWAS_GATES.md` records
    the exact reach and limits. The individual `Axioms.lean`, regenerated
    report and manifest edits are logged in their derivations' change logs;
    no theorem statement or seed is changed.

40. **Fenced whole-repo review and proposal area (2026-09-23).** Added
    `meta/` for the 21-derivation audit, correspondence and Genesis
    comparisons, local receipts, and ten future seed proposals. Its
    categorical and biological vocabulary is outside the derivational seal:
    no `meta/` file is an input to a blind seed, paper, or theorem. Added
    ten digest entries to `ci/prose_watchlist.json` for that vocabulary
    and the external repository name, with deliberate pins for tracked
    review prose. The preexisting per-paper pins are checked unchanged by
    `meta/review/check_paper_pins.py`. The proposal changes themselves do
    not alter the repair branch's theorem, generator, or axiom-report files;
    this integration also carries the separately reviewed repair commit.
    `prompt/` remains untouched.

41. **Isolation restored for later derivations (2026-09-24).** Since
    2026-09-18 (commit `f255ba5`), `.claude/settings.json` allowed the web
    tools and outside servers and denied nothing, so the third through
    twenty-first derivations were isolated by instruction only. The deny
    list is restored (web fetch and search, `curl`, `git fetch`, `pull`,
    `push` and `remote`, `gh`, package installs, `lake update`, outside
    connectors and servers, edits to `.claude/`), and reads outside the
    working directory are blocked again. The review plan appended to
    `CLAUDE.md` for item 40 moved verbatim to
    `meta/review/plan_2026-09-23.md`, and the two closing design-note
    sections of `ci/OEWAS_GATES.md` moved verbatim to
    `meta/review/detector_design_notes.md`, so that no file a derivation
    loads or reads for its gates carries review or analogy vocabulary.
    `CLAUDE.md` gains a short operator note on isolation, the docstring of
    `ci/check_prose_watchlist.py` no longer names another repository, and a
    tracked `AGENTS.md` now only points to `CLAUDE.md` (an untracked stale
    copy of an older `CLAUDE.md` was removed from the main checkout). The
    watchlist pin is regenerated for these moves only; every per-paper pin
    is unchanged. The prompts of the sixteenth through twenty-first
    derivations also carry phrasing from outside this repository; `prompt/`
    is read-only, so they are left as they are and the finding is recorded
    in `meta/climbing/blindness.md`. Nothing under `prompt/`, `code/`,
    `lean4/`, `evidence/`, or any paper body changes.

42. **The twenty-second seed installed; the watchlist counts `prompt/`
    (2026-09-25).** By the author's rulings of 2026-09-25,
    `prompt/twentysecond/seed_prompt.md` (SHA-256
    `dd6ea130764ddc6336ba4e21adcac1493cfca11312574dabf25c9859cddefd04`) and
    `prompt/twentysecond/prompt.md` (SHA-256
    `a09505016125a4d53a653ebbfb53aef34cff86b846756f34b08e80197409fc3d`) are
    installed as LF bytes. The seed is the ninth seed
    (`7231e4280445abcc74f5fc22e5c741178cae507854d93af49878404fc1a9d135`)
    with one sentence replaced. `ci/check_prose_watchlist.py` no longer
    excludes `prompt/`: every prompt, the new one included, is counted
    under the pin. In a sparse checkout it sets aside the pins of files it
    does not hold, and it refuses to regenerate there.
    `ci/prose_watchlist.json` gains 16 watched digests, and the pin is
    regenerated. Tests in `tests/test_prose_watchlist.py` cover the new
    scope and the sparse case by injection. No earlier prompt, code, Lean,
    evidence, or paper file changes.

43. **The twenty-third seed installed; runs start from a clone
    (2026-09-26).** `prompt/twentythird/seed_prompt.md` (SHA-256
    `84eda21987126db16a43261ccc98d6fef23449c9c580a1bb5cf275b4f378578f`) and
    `prompt/twentythird/prompt.md` (SHA-256
    `b9d8c293dec647f6c03f7712e8253d0b8360379ff9585825bf00214f1388df8a`) are
    installed as LF bytes. The seed is the twenty-second seed
    (`dd6ea130764ddc6336ba4e21adcac1493cfca11312574dabf25c9859cddefd04`)
    with its sameness sentence extended and one sentence added. From this
    derivation on, a run starts in a clone of a one-commit snapshot of
    `main` that omits `meta/`, and the operator replays its commits onto
    `main`. `ci/check_prose_watchlist.py` therefore sets aside the pins
    under a tree that no tracked file lies in (`meta/`), and refuses to
    regenerate there; `tests/test_prose_watchlist.py` covers both sides by
    injection. `CLAUDE.md`'s operator note says the same. No earlier prompt,
    code, Lean, evidence, or paper file changes.

44. **The twenty-fourth and twenty-fifth seeds installed (2026-09-25).**
    `prompt/twentyfourth/seed_prompt.md` (SHA-256
    `ebbf2fb621125898aa28ef13f7c9a12f1ddac81f52b15d6ea4cf004e805cf89a`),
    `prompt/twentyfourth/prompt.md` (SHA-256
    `835a1074af291750c63ea95e014bc0b368e1d67a196318c1a5dc4474890f7ee5`),
    `prompt/twentyfifth/seed_prompt.md` (SHA-256
    `79a757575547a15ab29fce9d83efa081d04c75f76034ca15a5533449b324507b`) and
    `prompt/twentyfifth/prompt.md` (SHA-256
    `57dbecc1a88896072cfee9a2d98fb009cd3fe4fdfb0f31253cfd60579df7b3d5`) are
    installed as LF bytes. Each seed is the twenty-third seed
    (`84eda21987126db16a43261ccc98d6fef23449c9c580a1bb5cf275b4f378578f`)
    with one kind of change added to its list and one sentence added; the
    two seeds differ only in that kind and that sentence. The two
    derivations are siblings: each run starts from the same snapshot, and
    their commits land on one branch. No earlier prompt, code, Lean,
    evidence, or paper file changes.
