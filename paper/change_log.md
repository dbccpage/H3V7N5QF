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
