# [opaque repository name]

## Task

This repository holds a family of blind derivations of a change calculus over assertions written `xry`: a base (`prompt/seed_prompt.md`, `paper/paper.md`, package `code/xry`) and sixteen further derivations, each striking or rewording exactly one sentence of a parent seed and deriving what follows.

Begin now from `prompt/nineteenth/seed_prompt.md`. It is the **base** seed with exactly one sentence changed: the identify semantics "Identifying two terms replaces both by one term in every assertion" is reworded to "…in one chosen assertion". Identifying `x` and `y` now merges them in a single chosen assertion and leaves the two terms distinct elsewhere. Determine what follows and what does not.

Determine first whether "one chosen assertion" is a well-defined change at all: what object results when a term is merged in one assertion and not in others, and does the change require the two terms to already co-occur in the chosen assertion? When several assertions qualify, what is "chosen", and are the alternatives distinct results? Is the base derivation's global identification recovered by iterating the partial one over every assertion, and if so at what cost? Which minimalities and isomorphisms of the base survive when identify no longer acts globally.

Throughout:

1. record for every notion whether it was given, chosen, derived, computed, refuted, or left open;
2. state what does not follow;
3. prove every claimed necessity and every claimed impossibility by exhaustive enumeration over a declared finite candidate space or by a Lean theorem — never by prose;
4. keep every non-isomorphic alternative unless a proof eliminates it; quotient only under an implemented isomorphism;
5. where you reuse a result of the base derivation (`code/xry`), cite it and check that its proof still holds under this seed — a claim that held under the base's rule must be re-proved or downgraded once that rule is changed.

Do not steer toward a known theory. The final section of the paper names the nearest known results and how the findings differ; keep the prose watchlist (`ci/check_prose_watchlist.py`) clean.

Use only this repository. No network, other files, or questions. Do not modify `prompt/`. First add your plan and stopping conditions to `CLAUDE.md`, and commit them.

## Folders

Follow the repository's five-file pattern (`docs/index/topics.md`): `code/nineteenth/` (typed, importing `code/xry` where a result still applies), `code/run_nineteenth.py`, `tests/`, `lean4/Nineteenth/`, `evidence/nineteenth/` (regenerable byte-for-byte, `--check`), and `paper/nineteenth/` (`paper.md`, `change_log.md`, `claim_ledger.md`). `prompt/nineteenth/` is read-only.

## Gates

Every `ci/` gate and stopping check must pass — they are the verifier (there is no hosted CI): coverage (>=95% line and branch, every `code/**/evidence.py` fully covered), `mypy --strict`, the prose watchlist, `lake build` (no `sorry`/`admit`/user-declared `axiom`, a `#print axioms` per cited theorem), and the three discipline gates `ci/check_vacuous_checks.py`, `ci/check_definitional_citations.py`, `ci/check_mutation_bite.py` (add a `nineteenth` panel of the same shape as the others). Verify each gate's real exit code directly; never read `lake build` through a shell pipe — a pipe returns the exit code of its last filter, not of the build, and a failing Lean library can look green. Read `$LASTEXITCODE` (or `echo EXIT=$?` on its own line) after the build.

## Done

Every notion has a recorded source; every claim has Lean/Python evidence or is marked open; every non-isomorphic alternative is kept or eliminated by proof; all gates pass; the base derivation's evidence still regenerates; everything intended is committed; and the paper states the strongest defensible terminal result — whether it terminates, and which base results survive the change — with no targeting of a predetermined conclusion.
