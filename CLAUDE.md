# CLAUDE.md — plan and stopping conditions

This file was written before any other work, as `prompt/prompt.md` requires.
It is the working contract for the run. Later edits are logged in
`paper/change_log.md`.

## Inputs and constraints

- Inputs: `prompt/prompt.md` (the task) and `prompt/seed_prompt.md` (the seed).
  Nothing else is an input.
- Only this repository is used. No network, no files outside it, no questions.
- `prompt/` is never modified (checked with `git diff --stat -- prompt/` before
  every commit).
- `.lake/` is never committed. The pinned Lean dependencies were fetched before
  the run into the main checkout's `lean4/.lake/packages`; this worktree links
  to that directory (a local junction, ignored by git). No download happens.
- No steering toward a known theory. The body of the paper uses the seed's own
  words (term, assertion, change, obstruction, answer, result). Known results
  are named only in the paper's final section.

## Bookkeeping rules (from the task, applied everywhere)

1. Every notion carries exactly one source status:
   **given** (stated in the seed), **chosen** (a reading I fixed where the seed
   is silent or ambiguous; the unchosen readings are listed), **derived**
   (proved from given + chosen), **computed** (output of `code/`, regenerable),
   **refuted** (proved impossible), **open** (neither proved nor refuted).
2. "What does not follow" is stated explicitly, each item with two legal
   witnesses (one where it holds, one where it fails) or a proof of
   independence.
3. Every claimed necessity and impossibility has a proof: in Lean where the
   statement fits the Lean model, otherwise a written proof in the paper, plus
   a computed check where a finite check is meaningful.
4. Every non-isomorphic alternative is kept unless a proof eliminates it. This
   applies to results (states) and to readings of the seed: where two readings
   give different results, both are computed.

## Plan

### Phase 0 — this file, committed alone.

### Phase 1 — reading the seed (`research/`, then `paper/`)
Sentence-by-sentence reading of the seed. Output: the notion table with source
statuses; the list of ambiguities with the readings kept. Expected points:
what "the same result" preserves (any rewriting of terms vs. rewritings that
keep `a`, `b`); whether `bra` is asserted (two initial alternatives, both
kept); what counts toward "100 changes"; what "remove the obstruction" and
"build structure" can mean; whether the supply of letters is bounded.

### Phase 2 — `code/` (typed Python, stdlib only) and `tests/`
Package `code/xry/`:
- states, sameness (canonical forms under both readings of sameness);
- the four kinds of change, the obstruction test, the dispositions of an
  obstructed change (refuse / remove the obstruction / build structure);
- breadth-first exploration: every change attempted on every alternative,
  round by round, fewest additions first, up to 100 rounds, under a declared
  finite bound on the number of terms; per-result record of terms and
  assertions added to what is given; exact frontier export;
- an independent count of all legal states within the bound (orbit counting),
  used as the completeness certificate for the exploration;
- closed-form cost of a result (if Phase 3 proves one) checked against the
  explored depths;
- property witnesses for "what does not follow";
- deterministic evidence writer (`python -m xry`), and a Lean axiom-report
  writer.
`tests/`: pytest, `--cov-branch`, fail under 95% line or 95% branch.
`mypy --strict` must pass.

### Phase 3 — `lean4/`
Lean 4 + Mathlib, no `sorry`, `admit`, or `axiom`. Targets, in order:
1. `a ≠ b`; independence of `bra` (two models); exactly two legal states on
   the given terms that contain the given assertion.
2. Obstruction characterised: which changes can make some `xrx` asserted.
3. Persistence: what can and cannot remove an obstruction.
4. Invariants of changes (at least one term always; legality preserved).
5. A potential that rises by at most one per change (lower bound on the
   number of changes to any result).
6. If time allows: the matching upper bound (explicit paths).
`#print axioms` for every theorem the paper cites, captured into `evidence/`.

### Phase 4 — `evidence/`
All files written by `python -m xry` (and the Lean axiom report). Regeneration
is checked by running the generator twice and comparing hashes
(`evidence/MANIFEST.sha256`).

### Phase 5 — `paper/`
`paper.md` (findings; final section: nearest known results and differences),
`claim_ledger.md` (ID, statement, status, evidence, axiom report, falsifier),
`change_log.md` (each material change and its reason).

### Phase 6 — audit against "Done", commit.

## Stopping conditions

The run stops when all of S1–S7 hold, or when a blocker below is hit.

- S1 Every notion in the paper has one recorded source status.
- S2 Every claim in `paper/claim_ledger.md` has evidence, or is marked open.
- S3 Every alternative is kept, or eliminated by a cited proof.
- S4 `pytest` passes with ≥95% line and ≥95% branch coverage; `mypy --strict`
  passes on `code/` and `tests/`.
- S5 `lake build` passes; grep finds no `sorry`, `admit`, or `axiom`
  declaration in `lean4/`; the axiom report is regenerated and committed.
- S6 Evidence regenerates byte-identically.
- S7 `git status` is clean, `prompt/` is unchanged, `.lake/` is untracked.

Bounded effort:
- Exploration bound: the largest term bound that completes in minutes on this
  machine (expected: 4 terms under both readings of sameness, 5 under the
  coarser one if it completes). The bound is declared in the paper; the
  frontier is exported exactly; completeness within the bound is certified by
  the independent count.
- Rounds: at most 100, as the seed says. No change is invented to reach 100;
  when a round yields no new result within the bound, that is recorded as
  such.
- Lean: targets 1–5 are required; target 6 is attempted once and, if it does
  not close, its claim is proved in the paper and marked "not in Lean" in the
  ledger rather than weakened silently.
- At most two full review passes over paper and ledger after the first
  complete draft.

Blockers (stop and report instead of working around):
- Lean dependencies unavailable offline → Lean claims are marked open, the
  rest is delivered, the ledger says so.
- Any step that would need the network, a file outside the repository, a
  change to `prompt/`, or a question.

## How to run (appended after the plan; see `paper/change_log.md` item 15)

All from the repository root, one plain command each:

- tests, coverage, types: `python -m pytest`, then
  `python code/xry/gate.py <coverage.json>` for the two rates separately
  (`python -m pytest --cov-report=json:<coverage.json>` writes the report),
  and `python -m mypy`;
- evidence: `python code/generate.py` (about 40 s);
- Lean build and axiom report: `python code/lean_report.py` (runs `lake`
  inside `lean4/`, where the pinned toolchain applies);
- Lean build alone: `lake +leanprover/lean4:v4.33.1 -d lean4 build`. Never run
  `lake` from the root without naming the toolchain: elan's default toolchain
  would start rebuilding the shared dependencies.

## Commit discipline

Small commits per phase on the current branch. Nothing is pushed.
