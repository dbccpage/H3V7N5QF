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
- evidence: `python code/generate.py` (about 40 s); `python code/generate.py
  --check` compares `evidence/` with a fresh regeneration (added at review, see
  `paper/change_log.md` item 17);
- Lean build and axiom report: `python code/lean_report.py` (runs `lake`
  inside `lean4/`, where the pinned toolchain applies);
- Lean build alone: `lake +leanprover/lean4:v4.33.1 -d lean4 build`. Never run
  `lake` from the root without naming the toolchain: elan's default toolchain
  would start rebuilding the shared dependencies.

## Commit discipline

Small commits per phase on the current branch. Nothing is pushed.

---

# Second derivation (`prompt/second/`) — plan and stopping conditions

Written before any other work of the second derivation, as
`prompt/second/prompt.md` requires. Inputs: `prompt/second/prompt.md` and
`prompt/second/seed_prompt.md`; the first derivation (`paper/`, `code/`,
`lean4/`, `evidence/`) is cited where used, never assumed. Everything above
stays in force (isolation, no network, `prompt/` untouched, `.lake/` never
committed, bookkeeping rules 1–4). Rule 5 of the second task: every result of
the first derivation that is used is cited and its proof re-checked from the
second seed — in Lean by an explicit embedding of the second seed's changes
into the first's where the statement is about changes, or by observing that the
statement mentions no change at all.

## What differs in the seed

One sentence: "removing an assertion" is no longer a kind of change. The three
kinds are identifying two terms, adding a term, adding an assertion. Every
other sentence is identical to the first seed.

## Layout

- `research/second/` — reading notes (not evidence).
- `code/second/` — typed Python package for the second seed; it imports from
  `code/xry/` what still applies (states, sameness, the counts, the writers)
  and defines afresh what the seed changes (the list of changes, the answers,
  the exploration, the cost, the reachability test). First-derivation files
  under `code/xry/` are not modified except to correct a defect.
- `tests/test_second_*.py` — tests of `code/second/`; the whole of `code/`
  stays at ≥ 95 % line and ≥ 95 % branch coverage; `mypy --strict` passes.
- `lean4/Second/` — a second Lean library in the same Lake package (the
  lakefile gains a library target and a default target; recorded in
  `paper/change_log.md` since it is a first-derivation file). It imports
  `H3V7N5QF` and reuses its state model; the second seed's changes are a new
  inductive `Step3` with three constructors and an embedding into the first's
  `Step`.
- `evidence/second/` — written by `python code/generate_second.py`; the axiom
  report by `python code/lean_report_second.py`; `--check` regenerates into a
  temporary folder and compares.
- `paper/second/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the second seed (`research/second/`)
Sentence-by-sentence diff against the first seed; the notion table with source
statuses; the readings inherited (C1–C9 of the first paper) and which of them
change meaning; the expected consequences to be proved or refuted: nothing is
ever un-asserted; `arb` persists; `a`, `b` are never identified; "remove the
obstruction" is never available; the results are the legal states that
contain what is given; fewest changes is the size difference; reachability
between results is a preorder with cycles.

### Phase 2 — `code/second/` and `tests/`
- changes (three kinds), obstruction (reused), answers (refuse, build; no
  removal), exploration (same protocol, three kinds), full logs at bound 3;
- cost in closed form (size difference; unreachable states marked), checked
  against explored rounds; FREE closed form checked against best placement;
- independent count of the results within the bound (orbit counts restricted
  to states containing what is given) as the completeness certificate;
- a reachability test by term maps (homomorphism criterion), checked against
  breadth-first search between every pair of results within a small bound;
- property witnesses for "what does not follow";
- deterministic evidence writer with `--check`; Lean axiom-report writer for
  `lean4/Second/Axioms.lean`.

### Phase 3 — `lean4/Second/`
Targets, in order:
1. `Step3` (three kinds), embedding into `Step`; legality, well-formedness,
   at least one term, inherited through the embedding (cited, re-checked).
2. The homomorphism invariant: every sequence of changes induces a map of
   terms carrying assertions to assertions and names to names. Consequences:
   `a`, `b` stay two terms; `arb` (and `bra` if given) stays asserted; an
   obstruction is never cleared; the fewest classes of a split with no two
   related terms in a class never decreases.
3. Size rises by at most one per change (lower bound); additions alone reach
   every legal state containing what is given (upper bound); fewest changes
   is exactly the size difference; states not containing what is given are
   unreachable (`reachable_iff`).
4. Answers: builds are sequences of additions (reused theorems re-checked);
   "remove the obstruction" is impossible for every obstructed change.
5. Changes commute with one-to-one rewriting (`rename`), carrying the
   `a = 0`, `b = 1` statements to every writing (the analogue of the first
   derivation's open item O3). Attempted once; if it does not close, the step
   is proved in the paper and marked "not in Lean".
`#print axioms` for every theorem the second paper cites, into
`evidence/second/lean_axioms.txt`.

### Phase 4 — `evidence/second/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The first derivation's `python code/generate.py --check` and
`python code/lean_report.py` are re-run to confirm its evidence still
regenerates.

### Phase 5 — `paper/second/`
`paper.md` (findings; every use of the first derivation cited with the
re-check; final section: nearest known results and differences),
`claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit.

## Stopping conditions (second derivation)

The run stops when T1–T8 hold, or when a blocker is hit.

- T1 Every notion in `paper/second/paper.md` has one recorded source status.
- T2 Every claim in `paper/second/claim_ledger.md` has evidence, or is open.
- T3 Every alternative is kept, or eliminated by a cited proof.
- T4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/`; `python -m mypy`
  passes.
- T5 `lake build` (pinned toolchain, inside `lean4/`) passes for both
  libraries; no `sorry`, `admit`, or declared axiom in `lean4/`; both axiom
  reports regenerated and committed.
- T6 `evidence/second/` regenerates byte-identically (`--check`); the first
  derivation's `evidence/` still regenerates byte-identically.
- T7 Every use of a first-derivation result in the second paper is cited and
  re-checked (ledger column "re-check").
- T8 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: FREE at most 5 terms; ANCHORED 4 terms, raised to 5 if a run
  completes in a few minutes here. Declared in the paper; the frontier is
  exported exactly; completeness within the bound is certified by the
  independent count.
- Rounds: at most 100; no change is invented.
- Lean targets 1–4 required; target 5 attempted once.
- At most two review passes over paper and ledger after the first draft.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question.

## How to run (second derivation)

From the repository root:
- `python -m pytest` (all tests, both derivations), then
  `python code/xry/gate.py coverage.json`, and `python -m mypy`;
- `python code/generate_second.py` writes `evidence/second/`;
  `python code/generate_second.py --check` compares with a fresh regeneration;
- `python code/lean_report_second.py` builds `lean4/` and writes
  `evidence/second/lean_axioms.txt`;
- the first derivation's commands are unchanged (see above).
