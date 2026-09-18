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
between results composes, each result reaches itself, and two different
results can reach each other.

### Phase 2 — `code/second/` and `tests/`
- changes (three kinds), obstruction (reused), answers (refuse, build; no
  removal), exploration (same protocol, three kinds), full logs at bound 3;
- cost in closed form (size difference; unreachable states marked), checked
  against explored rounds; FREE closed form checked against best placement;
- independent count of the results within the bound (orbit counts restricted
  to states containing what is given) as the completeness certificate;
- a reachability test by term maps (the carrying-map criterion), checked against
  breadth-first search between every pair of results within a small bound;
- property witnesses for "what does not follow";
- deterministic evidence writer with `--check`; Lean axiom-report writer for
  `lean4/Second/Axioms.lean`.

### Phase 3 — `lean4/Second/`
Targets, in order:
1. `Step3` (three kinds), embedding into `Step`; legality, well-formedness,
   at least one term, inherited through the embedding (cited, re-checked).
2. The carrying-map invariant: every sequence of changes induces a map of
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

---

# Third derivation (`prompt/third/`) — plan and stopping conditions

Written before any other work of the third derivation, as
`prompt/third/prompt.md` requires. Inputs: `prompt/third/prompt.md` and
`prompt/third/seed_prompt.md`; the first derivation (`paper/`, `code/xry/`,
`lean4/H3V7N5QF/`, `evidence/`) and the second (`paper/second/`,
`code/second/`, `lean4/Second/`, `evidence/second/`) are cited where used,
never assumed. Everything above stays in force (isolation, no network,
`prompt/` untouched, `.lake/` never committed, bookkeeping rules 1–4). Rule 5
of the third task: every result of the first or second derivation that is used
is cited and its proof re-checked from the third seed — in Lean by an explicit
embedding of the third seed's changes into the second's (and through it into
the first's) where the statement is about changes, or by observing that the
statement mentions no change at all, or by computing it again from the third
seed's own exploration.

## What differs in the seed

One sentence: "identifying two terms" is no longer a kind of change, and the
sentence saying what identifying does is gone with it. The two kinds are adding
a term and adding an assertion. Every other sentence is identical to the second
seed (`diff`), and so to the first seed except for removal.

## Layout

- `research/third/` — reading notes (not evidence).
- `code/third/` — typed Python package for the third seed; it imports from
  `code/xry/` and `code/second/` what still applies (states, sameness, the
  counts of results, the cost in closed form, the statements tested, the
  fewest classes, the writers, the attempt records) and defines afresh what
  the seed changes (the list of changes, the answers, the exploration,
  reachability between results, the counts that never decrease, the number of
  sequences reaching a result). First- and second-derivation files are not
  modified except to correct a defect, recorded in the relevant change log.
- `tests/test_third_*.py` — tests of `code/third/`; all of `code/` stays at
  ≥ 95 % line and ≥ 95 % branch coverage; `mypy --strict` passes; the prose
  watchlist (`ci/check_prose_watchlist.py`) stays clean.
- `lean4/Third/` — a third Lean library in the same Lake package (the lakefile
  gains the library target and a default target; recorded in
  `paper/change_log.md` since it is a first-derivation file). It imports
  `Second` and reuses the state model; the third seed's changes are a new
  inductive `Step2` with two constructors, embedded into the second's `Step3`
  and through it into the first's `Step`.
- `evidence/third/` — written by `python code/generate_third.py`; the axiom
  report by `python code/lean_report_third.py`; `--check` regenerates into a
  temporary folder and compares.
- `paper/third/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the third seed (`research/third/`)
Sentence-by-sentence diff against the second seed; the notion table with
source statuses; the readings inherited (C1–C9 of the earlier papers) and which
of them change meaning (C5 loses its clause on identifying a term with itself;
C7: the only obstructed change is adding some `xrx`, and its obstruction is the
assertion the change itself adds, so "remove the obstruction" is either
impossible or coincides with refusal — both readings kept). Expected
consequences to be proved or refuted: every change leaves every term, every
assertion and both names in place (the state is contained in its outcome);
the second derivation's carrying map is the identity; nothing is ever
un-asserted and no term ever disappears; the numbers of terms and of
assertions never decrease; size rises by exactly one per change, so every
sequence of changes from what is given to a result has the same length, the
size difference; the results are the same set as under the second seed (the
legal states containing what is given), in the same rounds; reachability
between results is containment (up to rewriting under FREE) and is one-way: a
result once left is never returned to, and only what is given reaches what is
given; refuse or build are the only answers.

### Phase 2 — `code/third/` and `tests/`
- changes (two kinds), obstruction (reused), answers (refuse, build; removal
  impossible), exploration (same protocol, two kinds), full logs at bound 3;
- cost in closed form reused from the second derivation and re-checked against
  the explored rounds; every sequence within bound 3 enumerated and its length
  compared with the size difference; the number of sequences reaching each
  result (exact within the bound, since a sequence never has more terms than
  its target);
- independent count of the results (reused, re-checked) as the completeness
  certificate; the third exploration compared result by result and round by
  round with the second derivation's exploration run without identifications
  (the computed form of the citation);
- reachability by containment (an embedding of the terms carrying assertions
  and names), checked against breadth-first search between every pair of
  results within a small bound, and compared with the second derivation's
  carrying-map reachability (which pairs the second reaches and the third does
  not; no pair reachable both ways);
- the counts that never decrease, checked on every change within the bound;
  the number of attempts per result (`1 + n² − m`, `n` of them obstructed)
  checked against the exploration;
- property witnesses for "what does not follow";
- deterministic evidence writer with `--check`; Lean axiom-report writer for
  `lean4/Third/Axioms.lean`.

### Phase 3 — `lean4/Third/`
Targets, in order:
1. `Step2` (two kinds), embeddings into `Step3` and `Step`; legality,
   well-formedness, at least one term, inherited through the embedding (cited,
   re-checked); conversely every change of the second seed is an
   identification or a change of the third; no change of the third has the
   outcome of an identification or of a removal.
2. The containment invariant: every sequence of changes leaves terms,
   assertions and names in place; this is a carrying map (the second
   derivation's invariant, re-checked by the embedding). Consequences: `a`,
   `b` stay two terms; `arb` (and `bra` if given) stays asserted; an
   obstruction is never cleared; the numbers of terms and of assertions never
   decrease; the fewest classes of a split never decreases (embedding).
3. Size rises by exactly one per change; every sequence between two states has
   the same length; lower and upper bounds; fewest changes is exactly the size
   difference; a result is reachable from a result exactly when it contains it
   (both directions in Lean); mutual reachability only in zero changes; a
   result once left is never returned to; the same for every writing (rename).
4. Answers: an attempt is obstructed exactly when it adds some `xrx`; builds
   are two additions; "remove the obstruction" is impossible for every
   obstructed change (adding `xrx` stays obstructed after every sequence of
   changes); a result reached by two different sequences (witness).
5. `Step2.rename`, `Reach2.rename` and the every-writing forms of the results
   above. Attempted once; if a step does not close it is proved in the paper
   and marked "not in Lean".
`#print axioms` for every theorem the third paper cites, into
`evidence/third/lean_axioms.txt`.

### Phase 4 — `evidence/third/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The first and second derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/third/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check; final section: nearest known results and differences — the only
place where outside names appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit.

## Stopping conditions (third derivation)

The run stops when U1–U9 hold, or when a blocker is hit.

- U1 Every notion in `paper/third/paper.md` has one recorded source status.
- U2 Every claim in `paper/third/claim_ledger.md` has evidence, or is open.
- U3 Every alternative is kept, or eliminated by a cited proof.
- U4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/`; `python -m mypy`
  passes.
- U5 `lake build` (pinned toolchain, inside `lean4/`) passes for all three
  libraries; no `sorry`, `admit`, or declared axiom in `lean4/`; all three
  axiom reports regenerated and committed.
- U6 `evidence/third/` regenerates byte-identically (`--check`); the first and
  second derivations' evidence still regenerates byte-identically.
- U7 Every use of a first- or second-derivation result in the third paper is
  cited and re-checked (ledger column "re-check").
- U8 The prose watchlist passes on the tracked tree; every pinned hit of the
  third paper is in its final section.
- U9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: FREE at most 5 terms; ANCHORED 4 terms with a counts-only census at
  5, as in the second derivation (the third exploration attempts fewer changes
  per result, so the same bounds complete faster). Declared in the paper; the
  frontier is exported exactly; completeness within the bound is certified by
  the independent count. Full logs and reachability at bound 3.
- Rounds: at most 100; no change is invented.
- Lean targets 1–4 required; target 5 attempted once.
- At most two review passes over paper and ledger after the first draft.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The worktree has
no `lean4/.lake`; the pinned packages are in the main checkout of this same
repository at `lean4/.lake/packages`, at exactly the revisions of the
committed manifest (checked before Phase 0), so a local junction to that
directory (ignored by git) is made and no download happens. Should `lake`
still try to fetch, the build is stopped and the Lean claims are marked open.

## How to run (third derivation)

From the repository root:
- `python -m pytest` (all tests, three derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_third.py` writes `evidence/third/`;
  `python code/generate_third.py --check` compares with a fresh regeneration;
- `python code/lean_report_third.py` builds `lean4/` and writes
  `evidence/third/lean_axioms.txt`;
- the first and second derivations' commands are unchanged (see above).
