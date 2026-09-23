# [opaque repository name]

## Task

This is a proposed blind derivation of `prompt/sixteenth/seed_prompt.md`. Begin from this package's `seed_prompt.md`, which changes only the sentences shown in `diff.patch`. The question is: Does the order of unadmitted leftovers affect which one can be admitted? Determine what follows and what does not. Do not assume the hypothesis in `why.md` is true.

Throughout:

1. record for every notion whether it was given, chosen, derived, computed, refuted, or left open;
2. state what does not follow, with two legal witnesses or an independence proof;
3. prove each necessity and impossibility by Lean or exhaustive enumeration over a declared finite space;
4. keep every non-isomorphic alternative unless a proof eliminates it, including readings of ambiguous sentences;
5. cite and re-check every earlier result used through a valid state/step map or a fresh computation.

Do not steer toward a known theory. Only the final section of the paper may name nearest known results. Keep `ci/check_prose_watchlist.py` clean. Use only this repository, with no network, other files, or questions. Do not modify `prompt/`. First append a plan and stopping conditions to `CLAUDE.md` and commit that plan alone if this proposal is later installed as a derivation.

## Folders

If installed, follow the five-file pattern in `docs/index/topics.md`: `code/<ordinal>/` (typed Python), `code/run_<ordinal>.py`, `tests/`, `lean4/<Ordinal>/`, `evidence/<ordinal>/` with byte-identical `--check`, and `paper/<ordinal>/` with `paper.md`, `claim_ledger.md`, and `change_log.md`. This numbered meta package is a proposal; it does not write into those folders.

## Gates

Every existing `ci/` gate and stopping check must pass: `python -m pytest -n auto`, `python code/xry/gate.py coverage.json` (at least 95 percent line and branch and full coverage of each evidence module), `python -m mypy`, the prose watchlist, the vacuous-check, definitional-citation, mutation-bite, and axiom-citation gates, `lake +leanprover/lean4:v4.33.1 -d lean4 build`, no `sorry`, `admit`, or declared `axiom`, `#print axioms` for every cited Lean theorem, and byte-identical evidence regeneration. Read each command's real exit code; do not infer a pass from piped output or a committed receipt.

## Done

Every notion and claim has its status and evidence or is open; alternatives are retained or excluded by proof; inherited results are re-checked; the exact bounded frontier and independent completeness count are recorded; all gates pass; `prompt/` is unchanged; and all intended files are committed. State the strongest defensible result, including a failed hypothesis if that is what the evidence shows.
