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
`python code/xry/gate.py coverage.json` checks the two rates separately and,
on top of the 95% floor, requires every `code/**/evidence.py` to be *fully*
covered. Each `evidence.py` holds families of differential checks (a computed
value against a closed form, a criterion against a search, one derivation
against the last); each has a branch that records a disagreement, dead on
correct code. The discipline is that every such check carries an injection
test that forces the disagreement and proves the branch fires — it lapsed in
three successive derivations, so the gate now makes a dead (uncovered) branch
a hard failure. Drive it with an injection test, or, if a line is genuinely
unreachable, mark it `# pragma: no cover`; never leave it silently uncovered.
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

---

# Fourth derivation (`prompt/fourth/`) — plan and stopping conditions

Written before any other work of the fourth derivation, as
`prompt/fourth/prompt.md` requires. Inputs: `prompt/fourth/prompt.md` and
`prompt/fourth/seed_prompt.md`; the first derivation (`paper/`, `code/xry/`,
`lean4/H3V7N5QF/`, `evidence/`), the second (`paper/second/`, `code/second/`,
`lean4/Second/`, `evidence/second/`) and the third (`paper/third/`,
`code/third/`, `lean4/Third/`, `evidence/third/`) are cited where used, never
assumed. Everything above stays in force (isolation, no network, `prompt/`
untouched, `.lake/` never committed, bookkeeping rules 1–4). Rule 5 of the
fourth task: every result of an earlier derivation that is used is cited and
its proof re-checked from the fourth seed, and the re-check says whether the
result survives the assertion being counted — in Lean by an explicit map
between the counted states and the earlier states (the earlier changes embed
into the fourth seed's, and a change of the fourth seed whose outcome asserts
nothing twice is a change of the third), or by observing that the statement
mentions no multiplicity, or by computing it again from the fourth seed's own
exploration and comparing with the third's on the results that assert nothing
twice.

## What differs in the seed

Two sentences: "An assertion is written `xry` … ; it is asserted a number of
times, its multiplicity. Adding an assertion raises its multiplicity by one."
and "`arb` is asserted with multiplicity one." Every other sentence is
identical to the third seed (`diff`). So the earlier derivations' reading C1
(asserted is yes or no; multiplicity left open as O1) is replaced by the seed,
and the state itself changes: what a state asserts is a number for each `xry`,
not a yes or no.

## Layout

- `research/fourth/` — reading notes (not evidence).
- `code/fourth/` — typed Python package for the fourth seed. The state model
  is new (`code/fourth/state.py`: terms, a multiplicity for each ordered pair,
  names; sameness under both readings). Imported from the earlier packages
  only what the multiplicity leaves intact: the sameness readings (`Sameness`),
  the kinds of change and the answer kinds (`Kind`, `AnswerKind`), the CSV /
  JSON / manifest writers, `compare_evidence`, the cycle-length machinery of
  the orbit counts (`partitions`, `class_size`, `pair_cycles`), the
  fewest-classes count and the earlier statements tested (both applied to the
  state's *support*: the state that asserts `xry` exactly when its multiplicity
  is positive), the Lean report runner, and the third derivation's exploration,
  reachability and sequence counts for the comparison. Defined afresh: the
  list of changes (re-adding what is asserted is now a change), the answers,
  the exploration (bounded in terms and in rounds), containment and
  reachability with multiplicities compared one by one, the cost, the counts
  that never decrease, the independent count of results, the statements about
  multiplicity, the number of sequences per result. First-, second- and
  third-derivation files are not modified except to correct a defect,
  recorded in the relevant change log.
- `tests/test_fourth_*.py` — tests of `code/fourth/`; all of `code/` stays at
  ≥ 95 % line and ≥ 95 % branch coverage; `mypy --strict` passes; the prose
  watchlist stays clean.
- `lean4/Fourth/` — a fourth Lean library in the same Lake package (the
  lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). A new state structure with a multiplicity function
  (`MSt`), the two kinds of change as an inductive `Step4`, and the two maps
  to and from the third derivation's states: the indicator map (`ofSt`, a
  state of the earlier seeds read as asserting everything once) and the
  support map (`toSt`). It imports `Third`.
- `evidence/fourth/` — written by `python code/generate_fourth.py`; the axiom
  report by `python code/lean_report_fourth.py`; `--check` regenerates into a
  temporary folder and compares.
- `paper/fourth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the fourth seed (`research/fourth/`)
Sentence-by-sentence diff against the third seed; the notion table with
source statuses; which of the readings C1–C9 change meaning: C1 is replaced
by the seed (multiplicity is given); C5 loses "adding what is asserted is not a
change" (it now raises the multiplicity, so it is a change with a new
outcome); C2 gains a clause: the beginning with `bra` asserts it with
multiplicity one (chosen; a beginning asserting `bra` `k` times is a result of
it, so the unchosen readings add no result); C6, C7 unchanged in wording.
Expected consequences to be proved or refuted: every change leaves its state
contained in its outcome, containment now comparing multiplicities one by one
(no multiplicity ever decreases, and one rises by exactly one per assertion
added); size = terms + sum of multiplicities rises by exactly one per change,
so every sequence between two states has the same length; the results are
the legal states containing what is given, now an infinite set even with the
terms bounded (the multiplicity of `arb` alone can be anything ≥ 1); the
results that assert nothing twice are exactly the third seed's results, in
the same rounds, reached by the same sequences; reachability is containment
(up to rewriting under FREE) and is one-way; a result has `1 + n²` changes,
`n` of them obstructed, whatever it asserts; the multiplicity of `arb` is not
kept at one (adding `arb` again is an unobstructed change); refuse or build
are the only answers, and "remove the obstruction" is impossible or refusal
as under the third seed.

### Phase 2 — `code/fourth/` and `tests/`
- states with multiplicities, sameness under both readings, the support map
  to the earlier state model and the indicator map back;
- changes (two kinds; `1 + n²` per state), obstruction, answers (refuse, build;
  removal impossible), exploration bounded in terms and in rounds, full logs
  at a small bound;
- cost in closed form (size difference with multiplicities counted), checked
  against the explored rounds; FREE closed form checked against the best
  placement; every change within the bound checked to raise the round by one
  and to lower no count; the number of sequences reaching each result (exact
  within the bound: a sequence never leaves the bound its target is within),
  with the closed form for two-term results checked;
- an independent count of the results by terms and total multiplicity (the
  orbit method with a series for each cycle instead of a binomial), as the
  completeness certificate within the bound; the results asserting nothing
  twice counted separately and compared with the third derivation's counts;
- the fourth exploration compared with the third's: the results asserting
  nothing twice, their rounds and their sequence counts must be the third's
  (the computed form of the citation);
- reachability by containment (an embedding of the terms carrying names and
  every multiplicity to one at least as large), checked against breadth-first
  search between every pair of results within a small bound, and compared
  with the third derivation's reachability on the pairs of results asserting
  nothing twice (they must agree);
- property witnesses for "what does not follow", including the new
  multiplicity statements;
- deterministic evidence writer with `--check`; Lean axiom-report writer for
  `lean4/Fourth/Axioms.lean`.

### Phase 3 — `lean4/Fourth/`
Targets, in order:
1. `MSt` (terms, a multiplicity function, names), `Legal`, `WF`, `size`,
   `Simple` (nothing asserted twice), `ofSt`, `toSt`, the two beginnings;
   `Step4` (two kinds), `Reach4`; legality, well-formedness, at least one term
   preserved; every change of the third seed is a change of the fourth on the
   indicator states (`Step2.toStep4`, `Reach2.toReach4`), and a change of the
   fourth whose outcome asserts nothing twice is a change of the third on the
   supports (`Step4.toStep2`, `Reach4.toReach2`).
2. Containment with multiplicities (`Contains4`): every sequence leaves terms,
   names and every multiplicity in place or higher. Consequences: `a`, `b`
   stay two terms; `arb` (and `bra` if given) stays asserted; no multiplicity
   ever decreases; the multiplicity of `arb` can rise (witness); an
   obstruction is never cleared; terms, total multiplicity and the fewest
   classes of a split (through the support) never decrease.
3. Size rises by exactly one per change; every sequence between two states
   has the same length; additions reach every legal state containing a state
   (induction on the missing terms, then on the total missing multiplicity);
   fewest changes is exactly the size difference; reachability is containment
   (both directions); one-way reachability; a result once left is never
   returned to; from the two beginnings.
4. Answers: an attempt is obstructed exactly when it adds some `xrx`; adding
   an asserted `xry` (`x ≠ y`) is unobstructed; builds are two additions;
   "remove the obstruction" is impossible; a result reached by two different
   sequences (witness).
5. `rename` for counted states; changes commute with rewriting; the
   every-writing forms of the results above. Attempted once; if a step does
   not close it is proved in the paper and marked "not in Lean".
6. What survives: on states asserting nothing twice, reachability, cost and
   one-way reachability of the fourth seed coincide with the third's through
   `toSt` / `ofSt` (the formal form of rule 5).
`#print axioms` for every theorem the fourth paper cites, into
`evidence/fourth/lean_axioms.txt`.

### Phase 4 — `evidence/fourth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The first, second and third derivations' `--check` and Lean
reports are re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/fourth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives the counting; a section answering the task's
question for the results, the reachability criterion, the cost and one-way
reachability; final section: nearest known results and differences — the only
place where outside names appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit.

## Stopping conditions (fourth derivation)

The run stops when V1–V9 hold, or when a blocker is hit.

- V1 Every notion in `paper/fourth/paper.md` has one recorded source status.
- V2 Every claim in `paper/fourth/claim_ledger.md` has evidence, or is open.
- V3 Every alternative is kept, or eliminated by a cited proof.
- V4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/`; `python -m mypy`
  passes.
- V5 `lake build` (pinned toolchain, inside `lean4/`) passes for all four
  libraries; no `sorry`, `admit`, or declared axiom in `lean4/`; all four
  axiom reports regenerated and committed.
- V6 `evidence/fourth/` regenerates byte-identically (`--check`); the first,
  second and third derivations' evidence still regenerates byte-identically.
- V7 Every use of an earlier result in the fourth paper is cited and
  re-checked, with the re-check saying whether it survives the counting
  (ledger column "re-check").
- V8 The prose watchlist passes on the tracked tree; every pinned hit of the
  fourth paper is in its final section.
- V9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: the results within any bound on terms are infinite, so the bound is
  on terms and on rounds together. Planned: 2 terms with all 100 rounds (the
  only setting in which the seed's 100 rounds complete: about 5 000 results
  per run); 3 terms with 12 rounds; 5 terms (any rewriting) and 4 terms
  (names kept) with 8 rounds; a counts-only census at 5 terms (names kept)
  with 8 rounds. Full attempt logs at 2 terms; reachability at 3 terms with 6
  rounds (which holds every result of the third seed within 3 terms). Declared
  in the paper; the frontier is exported exactly (the attempts leaving the
  term bound, and the results of the last round, whose changes await the next
  round); completeness within the bound is certified by the independent
  count. Bounds are lowered if a run does not complete in minutes here.
- Rounds: at most 100; no change is invented.
- Lean targets 1–4 and 6 required; target 5 attempted once.
- At most two review passes over paper and ledger after the first draft.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The worktree's
`lean4/.lake/packages` is still the local junction to the main checkout's
pinned packages (checked before Phase 0; no download happens).

## How to run (fourth derivation)

From the repository root:
- `python -m pytest` (all tests, four derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_fourth.py` writes `evidence/fourth/`;
  `python code/generate_fourth.py --check` compares with a fresh regeneration;
- `python code/lean_report_fourth.py` builds `lean4/` and writes
  `evidence/fourth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Fifth derivation (`prompt/fifth/`) — plan and stopping conditions

Written before any other work of the fifth derivation, as
`prompt/fifth/prompt.md` requires. Inputs: `prompt/fifth/prompt.md` and
`prompt/fifth/seed_prompt.md`; the first derivation (`paper/`, `code/xry/`,
`lean4/H3V7N5QF/`, `evidence/`), the second (`paper/second/`, `code/second/`,
`lean4/Second/`, `evidence/second/`), the third (`paper/third/`,
`code/third/`, `lean4/Third/`, `evidence/third/`) and the fourth
(`paper/fourth/`, `code/fourth/`, `lean4/Fourth/`, `evidence/fourth/`) are
cited where used, never assumed. Everything above stays in force (isolation,
no network, `prompt/` untouched, `.lake/` never committed, bookkeeping rules
1–4). Rule 5 of the fifth task: every result of an earlier derivation that is
used is cited and its proof re-checked from the fifth seed, and the re-check
says whether the result survives removal lowering a multiplicity and
identification merging terms — in Lean by an explicit embedding of the
fourth seed's changes into the fifth's (every addition is still a change) and
a case split the other way (a change of the fifth is a removal, an
identification, or a change of the fourth), by the support map to the first
seed's states where the statement is about states asserting nothing twice,
by observing that the statement mentions no change at all, or by computing it
again from the fifth seed's own exploration and comparing with the fourth's
on the results that contain what is given.

## What differs in the seed

Two sentences: "Adding an assertion raises its multiplicity by one; removing
an assertion lowers it by one." and "A change is exactly one of: identifying
two terms; removing an assertion; adding a term; adding an assertion. Nothing
else is a change. Identifying two terms replaces both by one term in every
assertion." Every other sentence is identical to the fourth seed (`diff`). So
the state stays the fourth's (terms, a multiplicity per ordered pair, names),
and the changes are the first seed's four kinds on it. What the fourth
derivation argued from "a change only adds" — containment, one-way
reachability, cost as the size difference, every sequence of the same length,
the carrying map, no multiplicity ever decreasing — is exactly what must be
re-examined; what it argued from the state alone (sameness, the two maps to
the earlier states, the counts by series) carries over.

## Layout

- `research/fifth/` — reading notes (not evidence).
- `code/fifth/` — typed Python package for the fifth seed. Imported from the
  earlier packages what removal and identification leave intact: the counted
  state and its sameness, support and indicator (`fourth.state`, unchanged:
  the state does not change), the kinds of change and the answer kinds
  (`xry.changes.Kind`, `AnswerKind`), the identification map on written terms
  (`xry.changes.identification_map`), the reading of a build through a map
  with multiplicities adding up (`fourth.changes.image`, `is_build_of` for an
  obstructed addition, `one_term_builds`), the size of what is given
  (`xry.cost.given_size`), `has_two_way`, the cycle machinery of the orbit
  counts and the series per cycle (`xry.orbits`, `fourth.orbits.series`),
  the statements tested (`fourth.follows`, all of them, plus new ones), the
  fewest-classes count (`fourth.invariants.fewest_classes`, kept only to
  show it can now decrease), the writers, `compare_evidence`, the Lean
  report runner, and the fourth derivation's exploration, sequence counts and
  reachability for the comparison. Defined afresh: the four kinds of change
  on counted states (identification with the multiplicities of the pairs that
  become one pair adding up; removal lowering one multiplicity by one;
  removing what is not asserted is not a change), obstruction (adding `xrx`;
  identifying two related terms), the answers (refuse; remove the obstruction
  — now a sequence of removals then the identification; build), the
  exploration (four kinds, bounded in terms and rounds), the cost in closed
  form (size difference plus twice the destroyed givens, size counting
  multiplicities — the first derivation's formula on counted states),
  reachability (the names-merged criterion; total under FREE), the counts
  of shortest sequences with their exactness, the independent count by
  series split by how the named terms stand (the first derivation's five
  kinds), the property witnesses. Earlier derivations' files are not modified
  except to correct a defect, recorded in the relevant change log.
- `tests/test_fifth_*.py` — tests of `code/fifth/`; all of `code/` stays at
  ≥ 95 % line and ≥ 95 % branch coverage; `mypy --strict` passes; the prose
  watchlist stays clean.
- `lean4/Fifth/` — a fifth Lean library in the same Lake package (the
  lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Fourth` and reuses `MSt`; new are
  `MSt.remove`, `MSt.identify` (the multiplicity of a pair of the outcome is
  the sum over the pairs that become it), the four kinds as an inductive
  `Step5`, `Reach5`, the embedding `Step4.toStep5`, the case split
  `Step5.cases4`, the map to the first seed's `Step` on the supports of
  states asserting nothing twice, and the potential `costA5`, `costB5`.
- `evidence/fifth/` — written by `python code/generate_fifth.py`; the axiom
  report by `python code/lean_report_fifth.py`; `--check` regenerates into a
  temporary folder and compares.
- `paper/fifth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the fifth seed (`research/fifth/`)
Sentence-by-sentence diff against the fourth seed and against the first; the
notion table with source statuses; which readings change: C5 (adding what is
asserted is a change, as in the fourth; removing what is not asserted is not;
identifying a term with itself is not; new: the multiplicities of the pairs an
identification merges add up — chosen; the unchosen "the larger of the two"
reading is shown to give the same results and the same cost, since every
proof identifies terms only in states with nothing asserted between the
merged pairs or asserts only that a merged multiplicity is at least each
part); C7 (the obstruction of an identification is the assertions between
the two terms with their multiplicities; removing it is `M(u,v) + M(v,u)`
removals then the identification; for adding `xrx` removing the obstruction
is not adding it, which is refusal — as the first derivation had it); C8
(bound on terms and on rounds, as the fourth). Expected consequences to be
proved or refuted: a multiplicity can go down (removing `arb`) and up again;
containment, the carrying map, "no multiplicity decreases", "every sequence
has the same length" and one-way reachability are refuted by witnesses; the
cost rises by at most one per change with the first derivation's potential
(size plus twice the destroyed givens, size counting multiplicities) and is
attained, so the fewest changes is that formula and the round of a result is
its cost; every legal state with at least one term is a result (the results
extend from "containing what is given" to everything); a result is reachable
from a result exactly when the names, once one term, stay one term (ANCHORED)
and always (FREE) — reachability is mutual within these classes; every result
with `a ≠ b` reaches what is given; every result reaches itself in two
changes, so infinitely many sequences reach every result; the fourth
derivation's results are exactly the results containing what is given, at the
same rounds, with the same shortest sequences; the fourth's cost survives on
those results only; the number of changes of a result is
`C(n, 2) + d + 1 + n²` (`d` the number of asserted pairs), `n` plus the
number of related unordered pairs of them obstructed; the one-term builds for
adding `xrx` are the fourth's two; the answer "remove the obstruction" is
available for every obstructed identification and reaches nothing new.

### Phase 2 — `code/fifth/` and `tests/`
- changes (four kinds), obstruction, answers, exploration (same protocol:
  identifications and removals first — no addition — then a term, then the
  assertions), full logs at a small bound;
- cost in closed form checked against the explored rounds; FREE closed form
  checked against the best placement; every change within the bound checked
  to raise the cost by at most one; the changes that raise it by exactly one
  characterised (a term, an assertion that restores no given, the removal of
  a given, the identification of `a` with `b`) and checked;
- the number of shortest sequences reaching each result by dynamic
  programming over the cost-raising changes, with a per-result exactness
  flag (exact when the result has fewer terms than the bound or `a ≠ b`);
  the two-term closed form where it still holds; a witness that every result
  is reached by sequences of unbounded length;
- an independent count of the results by terms, total multiplicity and how
  the named terms stand (the first derivation's five kinds, counted by the
  fourth's series), restricted to cost within the rounds, as the completeness
  certificate; the FREE count with the one-way split;
- the fifth exploration compared with the fourth's at the same bound and
  rounds: the fourth's results must be exactly the fifth's results containing
  what is given, at the same rounds, with the same shortest-sequence counts
  (the computed form of the citation);
- reachability by the names criterion checked against breadth-first search
  between every pair of results within a small bound, and compared with the
  fourth's containment on the fourth's results (containment must imply
  reachability; the pairs reachable now and not before are counted; mutual
  pairs counted);
- property witnesses for "what does not follow", including the fourth's
  invariants that now fail;
- deterministic evidence writer with `--check`; Lean axiom-report writer for
  `lean4/Fifth/Axioms.lean`.

### Phase 3 — `lean4/Fifth/`
Targets, in order:
1. `MSt.remove`, `MSt.identify`; `Step5` (four kinds), `Reach5`; legality,
   well-formedness, at least one term preserved; `Step4.toStep5`,
   `Reach4.toReach5`; the case split of a `Step5` into a removal, an
   identification or a `Step4`; on states asserting nothing twice a `Step5`
   is a `Step` of the first seed on the supports; names once one term stay
   one term, and `arb` is then never asserted again (the first derivation's
   `Reach.names_stay_merged`, `Reach.arb_gone_for_good`, re-proved).
2. Obstruction: an attempt is obstructed exactly when it adds some `xrx` or
   identifies two related terms; removal and adding a term are never
   obstructed; adding an asserted `xry` (`x ≠ y`) is unobstructed; an
   obstruction of an identification persists through every change but a
   removal of it (the first's `obstruction_persists` with multiplicities).
   Refutations by witness: a multiplicity can decrease (`arb` removed);
   containment, the carrying map and one-way reachability fail; two
   sequences of different lengths reach one result.
3. Cost: the potential `size + 2·lost` rises by at most one per change
   (`Step5.costA_le`, `Step5.costB_le`; total multiplicity is preserved by an
   identification and lowered by one by a removal); the lower bound; the
   upper bound by removing the missing givens (and identifying `a`, `b` where
   the target has them one term) then the fourth's additions
   (`reach4_by_additions` through the embedding); fewest changes exactly
   (`fewest_changes5_A`, `_B`); every legal well-formed state is a result
   (`result5_iff`); on results containing what is given the cost is the size
   difference (the fourth's cost survives there and only there).
4. Reachability: a legal well-formed state is reachable from a well-formed
   state exactly when the names, if one term at the start, are one term at
   the end (`reach5_iff`); reachability is mutual on states with the names
   apart and on states with them one term, one-way between the two classes;
   every result with `a ≠ b` reaches what is given; every state reaches
   itself in two changes, so the lengths of the sequences to a result are
   unbounded.
5. Answers: the removal of an obstruction is a sequence of performed changes
   (`M(u,v) + M(v,u)` removals then the identification); removing first or
   removing the `uru` that results last gives the same state; builds are
   the fourth's two additions through the embedding; every answer is a
   sequence of unobstructed changes.
6. `rename` for the four kinds (`rename4_remove`, `rename4_identify`,
   `Step5.rename`, `Reach5.rename`); the cost is the same in every writing.
   Attempted once; if a step does not close it is proved in the paper and
   marked "not in Lean".
7. What survives: on the fourth's results (states containing what is
   given), `Reach4` implies `Reach5` in the same number of changes and the
   fewest changes agree; the reachability criterion, one-way reachability and
   uniform sequence length are refuted on those very results (witnesses).
`#print axioms` for every theorem the fifth paper cites, into
`evidence/fifth/lean_axioms.txt`.

### Phase 4 — `evidence/fifth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The first, second, third and fourth derivations' `--check` and
Lean reports are re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/fifth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives removal and identification; a section
answering the task's question for the results, the reachability criterion,
the cost and one-way reachability; final section: nearest known results and
differences — the only place where outside names appear), `claim_ledger.md`,
`change_log.md`.

### Phase 6 — audit against "Done", commit.

## Stopping conditions (fifth derivation)

The run stops when W1–W9 hold, or when a blocker is hit.

- W1 Every notion in `paper/fifth/paper.md` has one recorded source status.
- W2 Every claim in `paper/fifth/claim_ledger.md` has evidence, or is open.
- W3 Every alternative is kept, or eliminated by a cited proof.
- W4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/`; `python -m mypy`
  passes.
- W5 `lake build` (pinned toolchain, inside `lean4/`) passes for all five
  libraries; no `sorry`, `admit`, or declared axiom in `lean4/`; all five
  axiom reports regenerated and committed.
- W6 `evidence/fifth/` regenerates byte-identically (`--check`); the earlier
  derivations' evidence still regenerates byte-identically.
- W7 Every use of an earlier result in the fifth paper is cited and
  re-checked, with the re-check saying whether it survives removal and
  identification (ledger column "re-check").
- W8 The prose watchlist passes on the tracked tree; every pinned hit of the
  fifth paper is in its final section.
- W9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: as the fourth's, on terms and rounds together — 5 terms (FREE) and
  4 terms (ANCHORED) with 8 rounds; 3 terms with 12 rounds; 2 terms with all
  100 rounds (the results per round stay finite: about `2r` at round `r`
  with names kept); an ANCHORED counts-only census at 5 terms; full attempt
  logs at 2 terms; reachability at 3 terms. A result now has about twice as
  many changes as under the fourth seed, so any run that does not complete
  in minutes here has its rounds lowered first, then its terms; the bounds
  used are declared in the paper.
- Rounds: at most 100; no change is invented.
- Lean targets 1–5 and 7 required; target 6 attempted once.
- At most two review passes over paper and ledger after the first draft.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The worktree's
`lean4/.lake/packages` is still the local junction to the main checkout's
pinned packages (checked before Phase 0; no download happens).

## How to run (fifth derivation)

From the repository root:
- `python -m pytest` (all tests, five derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_fifth.py` writes `evidence/fifth/`;
  `python code/generate_fifth.py --check` compares with a fresh regeneration;
- `python code/lean_report_fifth.py` builds `lean4/` and writes
  `evidence/fifth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Sixth derivation (`prompt/sixth/`) — plan and stopping conditions

Written before any other work of the sixth derivation, as
`prompt/sixth/prompt.md` requires. Inputs: `prompt/sixth/prompt.md` and
`prompt/sixth/seed_prompt.md`; the first derivation (`paper/`, `code/xry/`,
`lean4/H3V7N5QF/`, `evidence/`), the second (`paper/second/`, `code/second/`,
`lean4/Second/`, `evidence/second/`), the third (`paper/third/`,
`code/third/`, `lean4/Third/`, `evidence/third/`), the fourth
(`paper/fourth/`, `code/fourth/`, `lean4/Fourth/`, `evidence/fourth/`) and
the fifth (`paper/fifth/`, `code/fifth/`, `lean4/Fifth/`, `evidence/fifth/`)
are cited where used, never assumed. Everything above stays in force
(isolation, no network, `prompt/` untouched, `.lake/` never committed,
bookkeeping rules 1–4, the evidence-module coverage gate). Rule 5 of the
sixth task: every result of an earlier derivation that is used is cited and
its proof re-checked from the sixth seed, and the re-check says whether the
result survives once `xrx` is allowed — in Lean by the embedding of the
fifth seed's changes into the sixth's (every performed change of the fifth
is a change of the sixth, and every *attempt* of the fifth is now a
performed change) and a case split the other way (a change of the sixth
whose outcome asserts no `xrx` is a change of the fifth), by observing that
the statement mentions no legality and no change, or by computing it again
from the sixth seed's own exploration and comparing with the fifth's on the
results that assert no `xrx`.

## What differs in the seed

Two sentences are gone (`diff`): "For no term `x` may `xrx` be asserted."
and the paragraph on obstruction ("A change that makes some `xrx` asserted
is obstructed. An obstructed change must be answered … A refused change is
recorded and changes nothing."). Every other sentence is identical to the
fifth seed. So the state is the fifth's (terms, a multiplicity per ordered
pair, names) with the diagonal pairs `xrx` now just pairs like any other;
the changes are the fifth's four kinds with nothing forbidden: adding `xrx`
and identifying two related terms are performed like every other change;
there is no obstruction, no answer, no refusal and no build. Everything the
fifth derivation argued *from legality* — which attempts are obstructed, the
answers, the builds, the lower bound of the cost (whose identification case
used that nothing is asserted between the merged terms), the destroyed
givens of a state with the names one term, `arb` never asserted again after
the names merge, the exactness of the shortest-sequence counts, the
completeness certificate by legal states — is exactly what must be
re-examined; what it argued from the state alone (sameness, the two maps to
the earlier states) or from the changes without legality (the names once one
term stay one term, the moves of the names, parity of the size, rewriting)
carries over.

## Layout

- `research/sixth/` — reading notes (not evidence).
- `code/sixth/` — typed Python package for the sixth seed. Imported from the
  earlier packages what legality leaves intact: the counted state and its
  sameness, support and indicator (`fourth.state`; a state with some `xrx`
  is a state like any other now), the kinds of change (`xry.changes.Kind`),
  the change record, the list of changes of a state, `perform`, `remove`,
  `identify` and the two-change cycle (`fifth.changes`, `fifth.state`,
  `fifth.explore.cycle`: none of them looks at legality), the size of what
  is given, `has_two_way`, `contains_given`, the cycle machinery and the
  series of the orbit counts (`xry.orbits`, `fourth.orbits.series`), the
  statements tested (`fourth.follows`, `fifth.follows`, all of them, plus
  "no `xrx`" now independent and "some `xrx`"), the fewest-classes count on
  states with no `xrx` (kept only for the comparison), the writers,
  `compare_evidence`, the Lean report runner, and the fifth derivation's
  exploration, sequence counts, cost and reachability for the comparison.
  Defined afresh: the attempt (every change performed; the record says
  whether the outcome asserts some `xrx`, which is what the fifth seed would
  have obstructed), the exploration (four kinds, nothing refused, bounded in
  terms and rounds), the cost in closed form (the destroyed givens of a state
  with the names one term now depend on how often `xrx` is asserted at the
  named term), the changes that raise the cost by exactly one, the
  reachability criterion (the names, re-derived without legality), the
  shortest-sequence counts with their exactness (a new rule under FREE), the
  independent count of the results by terms, total multiplicity and destroyed
  givens with the diagonal pairs counted, the two-term closed forms (round
  counts and multinomial sequence counts), the property witnesses. Earlier
  derivations' files are not modified except to correct a defect, recorded in
  the relevant change log.
- `tests/test_sixth_*.py` — tests of `code/sixth/`; all of `code/` stays at
  ≥ 95 % line and ≥ 95 % branch coverage, every `code/**/evidence.py` fully
  covered (an injection test for every differential check); `mypy --strict`
  passes; the prose watchlist stays clean.
- `lean4/Sixth/` — a sixth Lean library in the same Lake package (the
  lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Fifth` and reuses `MSt`, `MSt.remove`,
  `MSt.identify`, `Contains4`, `rename4` and the fifth's rewriting lemmas;
  new are the four kinds without legality conditions as an inductive
  `Step6`, `Reach6`, the embeddings `Step5.toStep6`, `Reach5.toReach6`,
  `Try5.toStep6` (nothing is obstructed), the case split `Step6.toStep5` on
  legal outcomes, the potential `costA6`, `costB6` with the new destroyed
  givens, and the addition path without legality (`reach6_by_additions`).
- `evidence/sixth/` — written by `python code/generate_sixth.py`; the axiom
  report by `python code/lean_report_sixth.py`; `--check` regenerates into a
  temporary folder and compares.
- `paper/sixth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the sixth seed (`research/sixth/`)
Sentence-by-sentence diff against the fifth seed; the notion table with
source statuses; which readings change: C5″ (identifying two related terms
is a change; adding `xrx` is a change; the multiplicities of the pairs an
identification merges add up, `urv`, `vru`, `uru`, `vrv` all becoming
`uru`), C7 dropped (no obstruction, no answer), C6 (every attempt is
performed; no refusal), C8′ unchanged in kind. Expected consequences to be
proved or refuted: nothing is obstructed (every attempt of the fifth seed is
a performed change); the results are every well-formed state with at least
one term, names anywhere, and the fifth's results are exactly those with no
`xrx`, at the same rounds; the reachability criterion survives (the names,
re-proved without legality) and so do mutual reachability within the two
classes, the two-change cycle, and the parity of the size; the fifth's cost
does not survive as stated — identifying `a` and `b` in what is given is one
change, where the fifth's potential rises by three — and the fewest changes
is `size − size(given) + 2·lost` with `lost` the number of missing givens
when the names are apart and `m0 + 1 − min(M(a,a), m0)` when they are one
term; this agrees with the fifth's formula on every result with no `xrx` and
on every result with the names apart, and differs exactly on results with
the names one term and `xrx` asserted at the named term; the shortest
sequences to the fifth's results with the names apart are the fifth's, and a
result with the names one term has more (identify first, then remove
`ara`); `arb` after the names merge is `ara`, and it can be asserted
(the fifth's `arb_gone_for_good` fails); a result with `n` terms and `d`
asserted pairs (diagonal included) has `C(n, 2) + d + 1 + n²` changes, none
obstructed, and on a result with no `xrx` exactly `n` plus the number of
related pairs of them make some `xrx` asserted; the frontier has one entry
per result at the bound (the term), no builds; with the given terms only the
results of round `r` grow as `r³`, so the seed's 100 rounds do not complete
within minutes and a lower bound on rounds is declared, with the closed form
proved for every round; the removal answer of the fifth (lower `urv`, `vru`
to zero, then identify) and the direct identification reach different
states, both results now.

### Phase 2 — `code/sixth/` and `tests/`
- changes (four kinds, every one performed), the attempt record (outcome;
  whether it asserts some `xrx`), exploration (same protocol; no answers),
  full logs at a small bound;
- cost in closed form checked against the explored rounds; FREE closed form
  checked against the best placement (with `xrx` multiplicities); every
  change within the bound checked to raise the cost by at most one; the
  changes that raise it by exactly one characterised and checked; parity
  checked (no change keeps the round);
- shortest sequences by dynamic programming over the cost-raising changes
  with the exactness flag (ANCHORED: fewer terms than the bound or the names
  apart; FREE: fewer terms than the bound or no optimal placement with the
  names one term); the two-term multinomial closed form (names apart)
  checked; the two-term round counts checked;
- an independent count of the results by terms, total multiplicity and
  destroyed givens, the diagonal pairs counted as cycles of the rewriting,
  the states with the names one term split by how often `xrx` is asserted at
  the named term, the FREE count split by the best placement; restricted to
  cost within the rounds, as the completeness certificate; its part with no
  `xrx` must be the fifth's count;
- the sixth exploration compared with the fifth's at the same bound and
  rounds: the fifth's results must be exactly the results with no `xrx`, at
  the same rounds; the shortest-sequence counts must agree on those with the
  names apart (FREE: with two or more terms) and be larger on the others;
- reachability by the names criterion checked against breadth-first search
  along the changes among the results within a small bound, and compared
  with the fifth's criterion on the fifth's results (they must agree pair by
  pair);
- per result the count of changes whose outcome asserts some `xrx` (what the
  fifth would have obstructed), checked against `n` plus the related pairs
  on results with no `xrx`;
- property witnesses for "what does not follow", including the fifth's
  invariants that now fail;
- deterministic evidence writer with `--check`; Lean axiom-report writer for
  `lean4/Sixth/Axioms.lean`.

### Phase 3 — `lean4/Sixth/`
Targets, in order:
1. `Step6` (four kinds, no legality conditions), `Reach6`; well-formedness
   and at least one term preserved; `Step5.toStep6`, `Reach5.toReach6`,
   `Try5.toStep6` (every attempt of the fifth is a change of the sixth:
   nothing is obstructed); `Step6.toStep5` when the state and the outcome
   are legal; `Step6.legal_iff` (a change makes some `xrx` asserted exactly
   when it adds some `xrx` or identifies two related terms — the fifth's
   obstruction characterisation restated as a fact about legality, no longer
   a bar); the names once one term stay one term; `arb_gone_for_good`
   refuted by witness (identify `a`, `b` in what is given: `ara` asserted).
2. Cost: `lost6A`, `lost6B` (the names one term: `m0 + 1 − min(M(a,a), m0)`),
   `cost6A`, `cost6B`; the potential rises by at most one per change
   (`Step6.costA_le`, `_B`; the identification case no longer assumes nothing
   between the merged terms); the lower bounds; `reach6_by_additions` (the
   fourth's proof without legality, `xrx` added like any pair); the upper
   bounds — names apart: the missing givens removed, then additions; names
   one term: `m0 − min(M(a,a), m0)` givens removed, the identification, then
   additions from the one-term state asserting `ara` `min(M(a,a), m0)`
   times; `fewest_changes6_A`, `_B`; on legal states `lost6 = lost5`, so the
   fifth's fewest changes survive there (`fewest_changes6_of_legal_A`, `_B`)
   and fail off them (witness); on states containing what is given the size
   difference (the fourth's) still; `Step6.size_step`, `Reach6.size_parity`.
3. Reachability: `reach6_clear`, `reach6_collapse` (identifications now
   unconditional), the moves of the names (the fifth's, re-proved or cited
   where they mention no legality), `reach6_iff` (a well-formed state is
   reachable from a well-formed state exactly when the names, if one term at
   the start, are one term at the end), `result6_iff_A`, `_B` (every
   well-formed state is a result of either beginning), `reach6_symm`,
   `reach6_total`, `merged_never_apart`, `cycle2`, `Reach6.unbounded`; the
   failures of one-way reachability through the embedding.
4. What survives (`Sixth/Compare.lean`): every result of the fifth is a
   result of the sixth at the same round (embedding); the sixth has results
   the fifth has not (`ara` added to what is given); the criterion survives
   (same statement, no legality); the cost survives on legal states and on
   states with the names apart, and fails with a witness; the obstruction
   notion: every attempt is a change (`Try5.toStep6`); the answer notion: the
   fifth's removal answer and the direct identification reach different
   states, both results (`remove_answer_differs`); the fifth's
   `remove_obstruction_first_or_last5` does not survive without legality
   (witness: `uru` asserted before the identification).
5. `Step6.rename`, `Reach6.rename`, the cost in every writing, the
   every-writing forms of the fewest changes. Attempted once; if a step does
   not close it is proved in the paper and marked "not in Lean".
`#print axioms` for every theorem the sixth paper cites, into
`evidence/sixth/lean_axioms.txt`.

### Phase 4 — `evidence/sixth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The five earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/sixth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives `xrx` being allowed; a section answering
the task's question for the results, the reachability criterion, the cost,
and the obstruction and answer notions; final section: nearest known results
and differences — the only place where outside names appear),
`claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit.

## Stopping conditions (sixth derivation)

The run stops when X1–X9 hold, or when a blocker is hit.

- X1 Every notion in `paper/sixth/paper.md` has one recorded source status.
- X2 Every claim in `paper/sixth/claim_ledger.md` has evidence, or is open.
- X3 Every alternative is kept, or eliminated by a cited proof.
- X4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- X5 `lake build` (pinned toolchain, inside `lean4/`) passes for all six
  libraries; no `sorry`, `admit`, or declared axiom in `lean4/`; all six
  axiom reports regenerated and committed.
- X6 `evidence/sixth/` regenerates byte-identically (`--check`); the earlier
  derivations' evidence still regenerates byte-identically.
- X7 Every use of an earlier result in the sixth paper is cited and
  re-checked, with the re-check saying whether it survives `xrx` being
  allowed (ledger column "re-check").
- X8 The prose watchlist passes on the tracked tree; every pinned hit of the
  sixth paper is in its final section.
- X9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and rounds together, as the fourth's and fifth's. A
  result now has `n²` pairs instead of `n² − n`, so the results per round
  grow faster; the targets are 4 terms (FREE) and 3 terms (ANCHORED) with 6
  rounds, 3 terms with 8 rounds, 2 terms with as many rounds as complete in
  a few minutes (planned 40; the seed's 100 do not complete, since the
  results with the given terms only grow as `r³`), an ANCHORED counts-only
  census one term higher, full attempt logs at 2 terms, reachability at 3
  terms with 4 rounds. Any run that does not complete in minutes here has
  its rounds lowered first, then its terms; the bounds used are declared in
  the paper; the frontier is exported exactly; completeness within the bound
  is certified by the independent count; the two-term round counts are
  proved in closed form for every round.
- Rounds: at most 100; no change is invented.
- Lean targets 1–4 required; target 5 attempted once.
- At most two review passes over paper and ledger after the first draft.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The worktree's
`lean4/.lake/packages` is still the local junction to the main checkout's
pinned packages (checked before Phase 0; no download happens).

## How to run (sixth derivation)

From the repository root:
- `python -m pytest` (all tests, six derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_sixth.py` writes `evidence/sixth/`;
  `python code/generate_sixth.py --check` compares with a fresh regeneration;
- `python code/lean_report_sixth.py` builds `lean4/` and writes
  `evidence/sixth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Seventh derivation (`prompt/seventh/`) — plan and stopping conditions

Written before any other work of the seventh derivation, as
`prompt/seventh/prompt.md` requires. Inputs: `prompt/seventh/prompt.md` and
`prompt/seventh/seed_prompt.md`; the six earlier derivations (`paper/`,
`paper/second/` … `paper/sixth/`, `code/xry/` … `code/sixth/`,
`lean4/H3V7N5QF/` … `lean4/Sixth/`, `evidence/` … `evidence/sixth/`) are
cited where used, never assumed. Everything above stays in force (isolation,
no network, `prompt/` untouched, `.lake/` never committed, bookkeeping rules
1–4, the evidence-module coverage gate). Rule 5 of the seventh task: every
result of an earlier derivation that is used is cited and its proof
re-checked from the seventh seed, and the re-check says whether the result
survives once there is no given datum and no names — in Lean by the two maps
between the sixth's states and the seventh's (*forgetting* the names of a
sixth state gives a seventh state, and every change of the sixth is a change
of the seventh on the forgotten states; *naming* a seventh state with a term
— both names on one of its terms — gives a sixth state, and every change of
the seventh on a state with a term is a change of the sixth on the named
states, the names following the merge), by observing that the statement
mentions neither the given nor the names, or by computing it again from the
seventh seed's own exploration and comparing with the sixth's on the results
with at least one term (names forgotten).

## What differs in the seed

One passage (`diff`): "Given: `arb` is asserted with multiplicity one.
Whether `bra` is asserted is not given." becomes "Nothing is given: to begin
with there are no terms and nothing is asserted." Every other sentence is
identical to the sixth seed. So the state loses its names (there is no `a`,
no `b`, nothing given to anchor a rewriting to), the beginning is the empty
state (no terms, nothing asserted), and there is one beginning and one
reading of sameness: with no names, the rewritings "keeping the names" are
all rewritings, so ANCHORED and FREE coincide. Everything the sixth argued
*from the given* — the destroyed givens and the cost measured from what is
given, containment of the given, the names criterion for reachability, the
one-way merge of the names, `bra` as an alternative — must be re-derived from
the empty beginning or dropped; what it argued from the state and the changes
alone (the four kinds, the size moving by one, the addition path, the
two-change cycle, the counts by series with the diagonal pairs, rewriting)
carries over through the two maps.

## Layout

- `research/seventh/` — reading notes (not evidence).
- `code/seventh/` — typed Python package for the seventh seed. Imported from
  the earlier packages what the given and the names leave intact: the
  counted state with its names left out (`fourth.state.MState` with
  `names = None`, its sameness under any rewriting, `support`, `of_state`,
  `rewrite`, the cache of least writings), `remove` and `identify`
  (`fifth.state`), the change record, the four kinds, the list of changes
  and `perform` (`fifth.changes`; on the empty state the list is "add a
  term" alone), the two-change cycle (`fifth.explore.cycle`; none on the
  empty state), the count of all well-formed states by terms and total
  multiplicity with the diagonal pairs among the cycles
  (`sixth.orbits.count_free`), the cycle machinery (`xry.orbits`), the
  statements tested that mention no name (`fourth.follows` UNNAMED and
  COUNTED, `fifth.follows` EXTRA_UNNAMED, `sixth.follows.some_xrx`), the
  fewest-classes count on states with no `xrx`, the writers,
  `compare_evidence`, the Lean report runner, and the sixth derivation's
  exploration, cost and reachability for the comparison. Defined afresh: the
  empty beginning; what a result adds to what is given (its terms and its
  total multiplicity, nothing being given); the attempt record; the
  exploration from an empty state; the cost in closed form (the size:
  terms plus the sum of the multiplicities); the changes that raise the cost
  by exactly one (the two additions, and nothing else); reachability (a
  result reaches another exactly when the other has a term or the first is
  empty); the shortest-sequence counts (exact for every result within any
  bound holding it: a shortest sequence is additions only); the independent
  count of the results by terms and total multiplicity, the empty state
  included, restricted to size within the rounds; the two-term closed form
  (`(C(t+3, 3) + [t even](t/2 + 1)) / 2` results with two terms and total
  `t`); the comparison with the sixth by forgetting the names; the property
  witnesses. Earlier derivations' files are not modified except to correct a
  defect, recorded in the relevant change log.
- `tests/test_seventh_*.py` — tests of `code/seventh/`; all of `code/` stays
  at ≥ 95 % line and ≥ 95 % branch coverage, every `code/**/evidence.py`
  fully covered (an injection test for every differential check);
  `mypy --strict` passes; the prose watchlist stays clean.
- `lean4/Seventh/` — a seventh Lean library in the same Lake package (the
  lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Sixth`. New: a state without names
  `NSt` (terms, a multiplicity for each ordered pair), `WF`, `size`, the
  empty state, the four operations (the sixth's definitions with the names
  left out); the two maps `MSt.forget : MSt → NSt` and `NSt.name : NSt → ℕ →
  MSt` (both names on one term); `Step7` (four kinds, no names), `Reach7`;
  `Step6.forget`, `Reach6.forget`, `Step7.name`, `Reach7.name`; the cost
  (the size), the addition path through `name`, the has-a-term criterion.
- `evidence/seventh/` — written by `python code/generate_seventh.py`; the
  axiom report by `python code/lean_report_seventh.py`; `--check`
  regenerates into a temporary folder and compares.
- `paper/seventh/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the seventh seed (`research/seventh/`)
Sentence-by-sentence diff against the sixth seed; the notion table with
source statuses; which readings change: C2 (what is given) is replaced by
the seed (nothing; the empty state, one beginning); C4 (sameness) collapses
to one reading (no names to keep; derived, not chosen); C5‴ unchanged;
C6 unchanged (round 0 is the empty state; round 1 the one-term state
asserting nothing — the first change can only add a term); C8′ (bound on
terms and rounds) unchanged in kind. Expected consequences to be proved or
refuted: the first change adds a term and nothing else is a change on the
empty state; once a state has a term every later state has a term, so the
empty state is a result (round 0) that is never returned to — the seventh's
one irreversible change, in place of the sixth's merge of the names; the size
moves by exactly one per change and additions alone reach every well-formed
state from the empty one, so the fewest changes to a result is its size, with
no destroyed givens (nothing is given to destroy), and every shortest
sequence is additions only; the results are every well-formed state, the
empty one included — the sixth's results (any rewriting) are exactly the
results with at least one term, and every sixth result with the names kept is
a seventh result once the names are forgotten; reachability: a result reaches
another exactly when the other has a term or the first is empty; mutual
among the results with a term, one-way out of the empty state; the sixth's
FREE criterion ("always") survives on states with a term; the two-change
cycle at every state with a term, none at the empty state; the cost of the
sixth measured from what is given does not survive (the one-term state
asserting nothing costs one change here and two there), the fourth's size
difference survives with `size(given) = 0`; the names and the given have no
referent, and "separability" — read as telling the two named terms apart, the
sixth's one-way property — has nothing to apply to and is replaced by
"having a term"; no tested statement about the asserting holds in every
result (the empty state fails "at least one term"; every other statement
fails somewhere): nothing about the asserting is forced from nothing, and
what is forced is the first change, the cost of every result and the one-way
exit from the empty state; a result with `n` terms and `d` asserted pairs has
`C(n, 2) + d + 1 + n²` changes; the results of round `r` with at most two
terms are `[r = 0] + [r ≥ 1] + [r ≥ 2]·(C(r+1, 3) + [r even]·r/2) / 2`, so the
seed's 100 rounds with two terms hold about two million results and a lower
bound on rounds is declared with the closed form proved for every round.

### Phase 2 — `code/seventh/` and `tests/`
- the empty beginning; changes (the fifth's four kinds, every one performed;
  the attempt record with the outcome and whether it asserts some `xrx`);
  the exploration from the empty state, bounded in terms and rounds; full
  attempt logs at a small bound;
- cost in closed form (the size) checked against the explored rounds; every
  change within the bound checked to move the size by exactly one; the
  changes that raise the cost by one characterised (the additions) and
  checked; parity checked (no change keeps the round);
- shortest sequences by dynamic programming over the additions, exact for
  every explored result; the one-term closed form (one sequence) checked;
- an independent count of the results by terms and total multiplicity (the
  sixth's `count_free`, the empty state added), restricted to size within
  the rounds, as the completeness certificate; the two-term closed form
  checked against it and against the two-term run;
- the seventh exploration compared with the sixth's (any rewriting, both
  `bra` alternatives, run at the same bound on terms and enough rounds): the
  results with at least one term must be exactly the sixth's results whose
  sixth-seed cost is within the sixth's rounds, and the sixth's round of each
  must be its sixth-seed cost formula; the sixth's ANCHORED results with the
  names forgotten must be exactly the seventh's results with a term (the
  computed form of the citation);
- reachability by the has-a-term criterion checked against breadth-first
  search along the changes among the results within a small bound, and
  compared with the sixth's FREE criterion on the results with a term;
- property witnesses for "what does not follow", including the sixth's
  everywhere-true "at least one term", which now fails at the empty state;
- deterministic evidence writer with `--check`; Lean axiom-report writer for
  `lean4/Seventh/Axioms.lean`.

### Phase 3 — `lean4/Seventh/`
Targets, in order:
1. `NSt`, `WF`, `size`, `total`, `empty`, the four operations; `forget`,
   `name`, `forget_name`, `name_wf`; `Step7` (four kinds), `Reach7`;
   `Step6.forget`, `Reach6.forget` (every change of the sixth is a change of
   the seventh on the forgotten states); `Step7.name`, `Reach7.name` (every
   change of the seventh on a state with a term is a change of the sixth on
   the named states, the names following the merge); well-formedness kept;
   the outcome of every change on a well-formed state has a term
   (`Step7.nonempty_out`), so `Reach7.nonempty`; the first change from the
   empty state adds a term (`first_change_adds_term`); the empty state is
   reached from a well-formed state only from itself in zero changes
   (`reach7_empty_iff`).
2. Cost: `Step7.size_step` (the size moves by exactly one either way),
   `Reach7.size_le` (lower bound), `reach7_addTerms`, `reach7_of_contains`
   (the sixth's addition path through `name` once a term is there),
   `reach7_by_additions` (upper bound: from the empty state, every
   well-formed state in exactly its size), `fewest_changes7` (both bounds),
   `Reach7.size_parity`, `shortest_are_additions` (a sequence from the empty
   state of length the size uses additions only), `cost_oneTerm`.
3. Reachability: `reach7_of_nonempty` (the sixth's `reach6_of_names` through
   `name`), `reach7_iff` (a well-formed state is reachable from a well-formed
   state exactly when it has a term or the start is empty), `result7_iff`
   (every well-formed state is a result), `empty_is_a_result`,
   `reach7_symm` (mutual among states with a term), `reach7_total`,
   `empty_never_returned`, `cycle2_7` (the sixth's through `name`),
   `Reach7.unbounded`, `no_cycle_at_empty`.
4. What survives (`Seventh/Compare.lean`): every result of the sixth (either
   beginning) is a result of the seventh with its names forgotten; every
   result of the seventh with a term is a result of the sixth once named;
   the seventh has a result no earlier seed has (the empty state:
   `Reach6.nonempty`); the sixth's criterion survives on states with a term
   as "always" and gains the empty-state clause; the sixth's cost does not
   survive (witness: the one-term state, `costA6 (name oneTerm) − 3 = 2`
   against 1); the size difference survives with nothing given; the one-way
   merge of the names becomes trivial through `name` (`c = c`) and is
   replaced by the one-way exit from the empty state.
5. `rename7`, `Step7.rename`, `Reach7.rename`, `size_rename7`,
   `fewest_changes7_every_writing`. Attempted once; if a step does not close
   it is proved in the paper and marked "not in Lean".
`#print axioms` for every theorem the seventh paper cites, into
`evidence/seventh/lean_axioms.txt`.

### Phase 4 — `evidence/seventh/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The six earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/seventh/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives with nothing given; a section answering the
task's question for the results, the reachability criterion, the cost, and
the notions of names, given and separability; final section: nearest known
results and differences — the only place where outside names appear),
`claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, push, pull request.

## Stopping conditions (seventh derivation)

The run stops when Y1–Y9 hold, or when a blocker is hit.

- Y1 Every notion in `paper/seventh/paper.md` has one recorded source status.
- Y2 Every claim in `paper/seventh/claim_ledger.md` has evidence, or is open.
- Y3 Every alternative is kept, or eliminated by a cited proof.
- Y4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- Y5 `lake build` (pinned toolchain, inside `lean4/`) passes for all seven
  libraries; no `sorry`, `admit`, or declared axiom in `lean4/`; all seven
  axiom reports regenerated and committed.
- Y6 `evidence/seventh/` regenerates byte-identically (`--check`); the
  earlier derivations' evidence still regenerates byte-identically.
- Y7 Every use of an earlier result in the seventh paper is cited and
  re-checked, with the re-check saying whether it survives with nothing
  given and no names (ledger column "re-check").
- Y8 The prose watchlist passes on the tracked tree; every pinned hit of the
  seventh paper is in its final section.
- Y9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and rounds together, as the fourth's to sixth's. One
  beginning and one reading, so fewer runs than the sixth: the targets are
  5 terms with 10 rounds (the results of round `r` are the well-formed
  states of size `r`), 3 terms with 12 rounds, 2 terms with 30 rounds (the
  seed's 100 do not complete for size: about two million results), a
  counts-only census at 6 terms with 10 rounds, full attempt logs at 2
  terms and 4 rounds, reachability among the results of 3 terms and 6
  rounds. Any run that does not complete in minutes here has its rounds
  lowered first, then its terms; the bounds used are declared in the paper;
  the frontier is exported exactly; completeness within the bound is
  certified by the independent count; the two-term round counts are proved
  in closed form for every round.
- Rounds: at most 100; no change is invented.
- Lean targets 1–4 required; target 5 attempted once.
- At most two review passes over paper and ledger after the first draft.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The worktree's
`lean4/.lake/packages` is still the local junction to the main checkout's
pinned packages (checked before Phase 0: `lake build` of the six libraries
completes with nothing to do; no download happens).

## How to run (seventh derivation)

From the repository root:
- `python -m pytest` (all tests, seven derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_seventh.py` writes `evidence/seventh/`;
  `python code/generate_seventh.py --check` compares with a fresh
  regeneration;
- `python code/lean_report_seventh.py` builds `lean4/` and writes
  `evidence/seventh/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Eighth derivation (`prompt/eighth/`) — plan and stopping conditions

Written before any other work of the eighth derivation, as
`prompt/eighth/prompt.md` requires. Inputs: `prompt/eighth/prompt.md` and
`prompt/eighth/seed_prompt.md`; the seven earlier derivations (`paper/`,
`paper/second/` … `paper/seventh/`, `code/xry/` … `code/seventh/`,
`lean4/H3V7N5QF/` … `lean4/Seventh/`, `evidence/` … `evidence/seventh/`) are
cited where used, never assumed. Everything above stays in force (isolation,
no network, `prompt/` untouched, `.lake/` never committed, bookkeeping rules
1–4, the evidence-module coverage gate). Rule 5 of the eighth task: every
result of an earlier derivation that is used is cited and its proof
re-checked from the eighth seed, and the re-check says whether the result
survives the second relation — in Lean by the two projections of a
two-relation state onto its `r` part and its `s` part (each a state of the
sixth seed: the same terms and names, one multiplicity function), by the
embedding of the sixth's states and changes as two-relation states asserting
nothing with `s` (every change of the sixth is a change of the eighth on
them), and by the fact that every change of the eighth is a change of the
sixth on one projection and leaves the other as it is (a term or an
identification acts on both); by observing that the statement mentions no
relation at all; or by computing it again from the eighth seed's own
exploration and comparing with the sixth's on the results asserting nothing
with `s`.

## What differs in the seed

Two passages (`diff` against the sixth seed): "An assertion is written `xry`
or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations"
and "Whether `bra`, or anything written with `s`, is asserted is not given."
Every other sentence is identical to the sixth seed's. So the state gains a
second multiplicity function: terms, a multiplicity for each ordered pair in
`r` and one in `s`, the names `a`, `b`; the given lives in `r` alone (`arb`
once), and `s` begins used by nothing (chosen: C2″, the unchosen beginnings
asserting something with `s` being results of it with the same results); the
four kinds of change range over both relations (removing or adding an
assertion of either; identifying two terms merges them in every assertion of
both); sameness rewrites both at once. Everything the sixth argued from one
multiplicity function — the size, the destroyed givens, the potential, the
addition path, the reachability path, the counts by series, rewriting — must
be re-examined with the second function alongside; what it argued from the
terms and the names alone (the names once one term stay one term, the moves
of the names, the two-change cycle) carries over.

## Layout

- `research/eighth/` — reading notes (not evidence).
- `code/eighth/` — typed Python package for the eighth seed. New state
  `DState` (terms, a multiplicity per ordered pair in `r` and in `s`, optional
  names) with sameness under both readings (the rewriting acting on both
  relations), the two projections `r_part`, `s_part` (each a `fourth.state.
  MState`), the embedding `of_r` (an `MState` read as a two-relation state
  with nothing in `s`), the size (terms plus both totals). Imported from the
  earlier packages what one relation leaves intact: `Sameness`, the kinds of
  change (`xry.changes.Kind`), the identification map, the cycle machinery
  and the series of the orbit counts (`xry.orbits`, `fourth.orbits.series`,
  `sixth.orbits` helpers), the sixth's cost, destroyed givens, FREE closed
  form and cost-raising rule *applied to the `r` projection*, the sixth's
  exactness rule for the shortest-sequence counts on the `r` projection, the
  sixth's reachability criterion on the `r` projection, the statements
  tested (on either projection), the fewest-classes count, the writers,
  `compare_evidence`, the Lean report runner, and the sixth's exploration,
  cost, sequence counts and reachability for the comparison. Defined afresh:
  the change record with a relation (`Change8`), the list of changes of a
  state (`C(n, 2) + d_r + d_s + 1 + 2n²`), `perform` on both relations, the
  exploration, the cost in closed form (the sixth's on the `r` part plus the
  total multiplicity of `s`), the cost-raising rule (an `s` addition always;
  an `s` removal never; the rest the sixth's on the `r` part), reachability
  (the names on the `r` part; the `s` part free), the independent count with
  every cycle of the rewriting carrying two multiplicities (the `r` factor
  as the sixth's by destroyed givens, the `s` factor free), the two-term
  closed forms (round counts; the multinomial with the four `s` items
  added), the joint statements (nothing in `s`; some pair asserted in both
  relations; `r` and `s` agree everywhere; …), the comparison with the sixth
  on the results asserting nothing with `s`, and the count of results
  against the product of the single-relation counts (the computed sense in
  which `s` is not an independent copy). Earlier derivations' files are not
  modified except to correct a defect, recorded in the relevant change log.
- `tests/test_eighth_*.py` — tests of `code/eighth/`; all of `code/` stays
  at ≥ 95 % line and ≥ 95 % branch coverage, every `code/**/evidence.py`
  fully covered (an injection test for every differential check);
  `mypy --strict` passes; the prose watchlist stays clean.
- `lean4/Eighth/` — an eighth Lean library in the same Lake package (the
  lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Seventh`. New: `DSt` (terms, a
  multiplicity function for each of the two relations — a function from a
  relation tag to a multiplicity function — and the names), `WF` (both
  projections well formed), `size8`, the projections `DSt.proj rel : MSt`,
  the embedding `MSt.ofR : DSt` (nothing in `s`), the four kinds with a
  relation tag as an inductive `Step8`, `Reach8`; `Step6.ofR`, `Reach6.ofR`;
  `Step8.proj` (a change is a `Step6` on one projection and leaves the other
  unchanged, or is a `Step6` on both); the potential `costA8`, `costB8`
  (the sixth's on the `r` projection plus the `s` total); the raising path
  for either relation; the reachability path (clear `s`, the sixth's path on
  `r` through `ofR`, raise `s`).
- `evidence/eighth/` — written by `python code/generate_eighth.py`; the
  axiom report by `python code/lean_report_eighth.py`; `--check`
  regenerates into a temporary folder and compares.
- `paper/eighth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the eighth seed (`research/eighth/`)
Sentence-by-sentence diff against the sixth seed (and the seventh's); the
notion table with source statuses; which readings change: C2″ (what is
given: `a`, `b`, `arb` once, `bra` once or not at all, nothing with `s` —
chosen; a beginning asserting something with `s` is a result of it and
reaches the same results, and its cost is the chosen beginning's formula
with the given `s` assertions counted among the givens, proved in the paper);
C5⁗ (what is a change: the sixth's, in either relation; an identification
adds up the multiplicities of the merged pairs in each relation separately);
C6 (fewest additions first: identifications, removals in `r`, removals in
`s`, a term, additions in `r`, additions in `s`); C8′ unchanged in kind.
Expected consequences to be proved or refuted: the results are every
well-formed two-relation state with a term (from either beginning), so for
every well-formed `r` state and every well-formed `s` state on the same terms
and names the pair is a result — the results are jointly free; the sixth's
results are exactly the results asserting nothing with `s`, at the same
rounds and with the same shortest-sequence counts; the fewest changes to a
result is the sixth's fewest changes to its `r` part plus the total
multiplicity of its `s` part (the potential `size + 2·lost` with the size
counting both relations and the destroyed givens read on `r`; per relation
the cost is additive, and the `s` part costs exactly its total, as under the
seventh seed); the reachability criterion is the sixth's on the `r` part
(the names) and the `s` part imposes nothing — reachability holds jointly
exactly when it holds for the `r` parts; mutual reachability, comparability,
the one-way merge of the names and the two-change cycle survive; the number
of results with `n` terms up to rewriting is not the product of the
single-relation counts (the rewriting acts on both at once: 8 against 4 with
two terms and one assertion in each) — the sense in which `s` is not an
independent copy — while every statement about `s` alone that fails in some
`s` state fails in some result and no statement about `r` constrains `s`;
which statements hold in every result: at least one term only; a result with
`n` terms and `d_r + d_s` asserted pairs has `C(n, 2) + d_r + d_s + 1 + 2n²`
changes, `n` plus the related pairs in `r` of them making some `xrx`
asserted on a result asserting none (the sixth's count on the `r` part) and
likewise for `s`; the two-term round counts are the sixth's convolved with
the `s` counts; the results per round grow faster than the sixth's, so lower
bounds on rounds are declared.

### Phase 2 — `code/eighth/` and `tests/`
- the two-relation state, its sameness, projections and embedding; changes
  (four kinds over two relations), the attempt record (outcome; whether it
  asserts some `xrx`, some `xsx`); exploration bounded in terms and rounds;
  full logs at a small bound;
- cost in closed form (the sixth's on the `r` part plus the `s` total)
  checked against the explored rounds; the FREE closed form checked against
  the best placement; every change within the bound checked to raise the
  cost by at most one; the cost-raising rule checked; parity checked;
- shortest sequences by dynamic programming with the sixth's exactness rule
  on the `r` part; the two-term multinomial (names apart, eight items);
- an independent count of the results by terms, total multiplicity and
  destroyed givens, every cycle of the rewriting carrying two multiplicities
  (the `r` factor split by destroyed givens as the sixth's, the `s` factor
  free), as the completeness certificate; its part with nothing in `s` must
  be the sixth's count; the count of results against the product of the
  single-relation counts;
- the eighth exploration compared with the sixth's at the same bound and
  rounds: the sixth's results must be exactly the results asserting nothing
  with `s`, at the same rounds, with the same shortest-sequence counts; the
  reachability criterion compared with the sixth's on those results;
- reachability by the names criterion on the `r` part checked against
  breadth-first search among the results within a small bound;
- per result the counts of changes making some `xrx` or some `xsx` asserted,
  checked against the sixth's formula on each projection;
- property witnesses for "what does not follow", the joint statements
  included;
- deterministic evidence writer with `--check`; Lean axiom-report writer for
  `lean4/Eighth/Axioms.lean`.

### Phase 3 — `lean4/Eighth/`
Targets, in order:
1. `DSt`, `WF`, `size8`, `proj`, `ofR`, the two beginnings (`givenA8`,
   `givenB8`), the operations (a term; an assertion in a relation; a removal
   in a relation; an identification of both); `Step8`, `Reach8`; `proj` of
   every operation (`proj_addTerm`, `proj_addAssertion_same`,
   `proj_addAssertion_other`, …, `proj_identify`); `Step6.ofR`,
   `Reach6.ofR` (every change of the sixth is a change of the eighth with
   nothing in `s`); `Step8.proj` (a change of the eighth is a change of the
   sixth on one projection and leaves the other as it is, or is a change of
   the sixth on both); `Reach8.proj` (a sequence of the eighth projects to a
   sequence of the sixth on either relation, no longer); well-formedness, at
   least one term, the names once one term stay one term (through the `r`
   projection).
2. Cost: `lostA8`, `lostB8` (the sixth's on the `r` projection), `costA8`,
   `costB8` (the size counting both relations plus twice the destroyed
   givens); the potential rises by at most one per change
   (`Step8.costA_le`, `_B`: the sixth's lemmas on the `r` projection for the
   `r` changes and the identification; the `s` total moves by one for the
   `s` changes and is kept by an identification, `total_identify` on the `s`
   projection); the lower bounds; `reach8_raise` (raising the multiplicities
   of one relation, the sixth's `reach6_raise` with a relation tag);
   `reach8_of_contains`; the upper bound: the sixth's sequence to the `r`
   part lifted through `ofR` (nothing in `s` along it: the identification of
   two terms keeps an empty relation empty, `identify_zero`), then the `s`
   additions (`fewest_changes8_A`, `_B`); on results with nothing in `s` the
   sixth's fewest changes survive (`fewest_changes8_of_r_A`, `_B`); parity
   (`Step8.size_step`, `Reach8.size_parity`).
3. Reachability: `reach8_clear` (removing every `s` assertion), then the
   sixth's `reach6_of_names` on the `r` projection through `ofR`, then the
   `s` additions: `reach8_of_names`, `reach8_iff` (the names on the `r`
   part decide; the `s` part imposes nothing), `result8_iff_A`, `_B` (every
   well-formed two-relation state), `results_pair` (any well-formed `r` and
   `s` parts on the same terms and names make a result), `reach8_symm`,
   `reach8_total`, `merged_never_apart8`, `cycle2_8`, `Reach8.unbounded`;
   the failures of one-way reachability through `ofR`.
4. What survives (`Eighth/Compare.lean`): every result of the sixth is a
   result of the eighth with nothing in `s` at the same round (`ofR`), and
   the results of the eighth asserting nothing with `s` are the sixth's
   (`results_r_iff`); the `r` projection of every result is a sixth result
   and so is the `s` projection (`proj_results`); the cost is additive per
   relation (`cost8_eq`: definitional) and the fewest changes to a result is
   the sixth's fewest changes to its `r` part plus its `s` total; the
   criterion survives as a statement about the `r` part's names
   (`criterion_survives`); the `s` relation adds a term to the cost and
   nothing to the criterion — the one interaction is through the terms and
   the names (an identification merges both; a rewriting rewrites both).
5. `rename8`, `Step8.rename`, `Reach8.rename`, the cost in every writing,
   the every-writing fewest changes. Attempted once; if a step does not close
   it is proved in the paper and marked "not in Lean".
`#print axioms` for every theorem the eighth paper cites, into
`evidence/eighth/lean_axioms.txt`.

### Phase 4 — `evidence/eighth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The seven earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/eighth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives the second relation; a section answering
the task's question for the results, the reachability criterion, the cost
and separability — per relation, jointly, or not — and how the two relations
interact; final section: nearest known results and differences — the only
place where outside names appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, push, pull request.

## Stopping conditions (eighth derivation)

The run stops when Z1–Z9 hold, or when a blocker is hit.

- Z1 Every notion in `paper/eighth/paper.md` has one recorded source status.
- Z2 Every claim in `paper/eighth/claim_ledger.md` has evidence, or is open.
- Z3 Every alternative is kept, or eliminated by a cited proof.
- Z4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- Z5 `lake build` (pinned toolchain, inside `lean4/`) passes for all eight
  libraries; no `sorry`, `admit`, or declared axiom in `lean4/`; all eight
  axiom reports regenerated and committed.
- Z6 `evidence/eighth/` regenerates byte-identically (`--check`); the
  earlier derivations' evidence still regenerates byte-identically.
- Z7 Every use of an earlier result in the eighth paper is cited and
  re-checked, with the re-check saying whether it survives the second
  relation (ledger column "re-check").
- Z8 The prose watchlist passes on the tracked tree; every pinned hit of the
  eighth paper is in its final section.
- Z9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and rounds together, as the fourth's to seventh's. A
  result now has `2n²` pairs to assert, so the results per round grow faster
  than the sixth's; the independent count sizes every run in advance, and
  the targets are 4 terms (FREE) and 3 terms (ANCHORED) with 7 rounds, 3
  terms with 8 rounds under FREE, 2 terms with 20 rounds, an ANCHORED census
  one term higher, full attempt logs at 2 terms and 3 rounds, reachability at
  2 terms with 5 rounds or 3 terms with 3 rounds, whichever holds under a
  million ordered pairs. Any run that does not complete in minutes here has
  its rounds lowered first, then its terms; the bounds used are declared in
  the paper; the frontier is exported exactly; completeness within the bound
  is certified by the independent count; the two-term round counts are
  proved in closed form for every round.
- Rounds: at most 100; no change is invented.
- Lean targets 1–4 required; target 5 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: the seventh derivation's pull request stays open on
  `worktree-third-derivation`, so the eighth's work goes on a branch
  `worktree-eighth-derivation` made from the seventh's last commit, and its
  pull request is opened against the seventh's branch.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The worktree's
`lean4/.lake/packages` is still the local junction to the main checkout's
pinned packages (checked before Phase 0; no download happens).

## How to run (eighth derivation)

From the repository root:
- `python -m pytest` (all tests, eight derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_eighth.py` writes `evidence/eighth/`;
  `python code/generate_eighth.py --check` compares with a fresh
  regeneration;
- `python code/lean_report_eighth.py` builds `lean4/` and writes
  `evidence/eighth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Ninth derivation (`prompt/ninth/`) — plan and stopping conditions

Written before any other work of the ninth derivation, as
`prompt/ninth/prompt.md` requires. Inputs: `prompt/ninth/prompt.md` and
`prompt/ninth/seed_prompt.md`; the eight earlier derivations (`paper/`,
`paper/second/` … `paper/eighth/`, `code/xry/` … `code/eighth/`,
`lean4/H3V7N5QF/` … `lean4/Eighth/`, `evidence/` … `evidence/eighth/`) are
cited where used, never assumed. Everything above stays in force (isolation,
no network, `prompt/` untouched, `.lake/` never committed, bookkeeping rules
1–4, the evidence-module coverage gate). Rule 5 of the ninth task: every
result of an earlier derivation that is used is cited and its proof
re-checked from the ninth seed, and the re-check says whether the result
survives with nothing given *and* two relations — in particular whether the
seventh's collapses (cost = size, reachability = has a term, one sameness)
and the eighth's independence (results a product, cost a sum, count not a
product) survive together, and where they interfere. In Lean the re-check is
by two pairs of maps: *forgetting* the names of an eighth state gives a
ninth state and every change of the eighth is a change of the ninth on the
forgotten states; *naming* a ninth state with a term (both names on one of
its terms) gives an eighth state and every change of the ninth on a state
with a term is a change of the eighth on the named states; the two
*projections* of a ninth state onto its `r` part and its `s` part are each a
state of the seventh seed, every change of the ninth is a change of the
seventh on a part and leaves the other part as it is, or is a change of the
seventh on both; and *embedding* a seventh state as a ninth state asserting
nothing with `s` turns every change of the seventh into one of the ninth. Or
by observing that the statement mentions neither the given, nor the names,
nor a second relation; or by computing it again from the ninth seed's own
exploration and comparing with the seventh's on the results asserting
nothing with `s` and with the eighth's on the results with a term.

## What differs in the seed

One passage (`diff` against the eighth seed): "Given: `arb` is asserted with
multiplicity one. Whether `bra`, or anything written with `s`, is asserted
is not given." becomes "Nothing is given: to begin with there are no terms
and nothing is asserted." Against the seventh seed one sentence differs: an
assertion is written `xry` or `xsy`, `r` and `s` being the two relations.
Every other sentence is the sixth seed's word for word. So the state is the
eighth's with its names left out (terms, a multiplicity for each ordered
pair in `r` and one in `s`), the beginning is the empty state, there is one
beginning and one reading of sameness (no names to keep, so ANCHORED and
FREE coincide, as under the seventh), and the four kinds of change range
over both relations as under the eighth. Everything the eighth argued *from
the given* (the destroyed givens on the `r` part, the cost measured from
`arb`, the names criterion, the one-way merge, `bra`, the asymmetry between
`r` and `s`) must be re-derived from the empty beginning or dropped;
everything the seventh argued *from one relation* (the size as the cost
with one total, the count by series with one multiplicity per cycle, the
one-term states having one shortest sequence) must be re-examined with the
second relation alongside; what both argued from the terms and the changes
alone (the size moving by one, the addition path, the two-change cycle, the
first change adding a term, rewriting) carries over through the maps.

## Layout

- `research/ninth/` — reading notes (not evidence).
- `code/ninth/` — typed Python package for the ninth seed. Imported from the
  earlier packages what the empty beginning and the second relation leave
  intact: the two-relation state with its names left out (`eighth.state.
  DState` with `names = None`, its sameness under any rewriting acting on
  both relations, `canonical`, `rewrite`, `pair`, `of_r`, `remove`,
  `identify`, the cache of least writings), the change record with a
  relation, the four kinds, the list of changes and `perform`
  (`eighth.changes`; on the empty state the list is "add a term" alone),
  the count of changes making some `xrx` or `xsx` asserted per part
  (`eighth.changes.attempt_counts`), the two-change cycle
  (`eighth.explore.cycle`; none on the empty state), the count of all
  well-formed two-relation states by terms and total multiplicity with two
  multiplicities on every cycle (`eighth.orbits.count_free`) and the product
  of the single-relation counts (`eighth.orbits.product_count`), the
  seventh's single-relation count (`seventh.orbits.count_results`), the
  statements tested that mention no name (`eighth.follows.on_part`, the
  unnamed and counted statements of the fourth to sixth, the eighth's joint
  statements), the counts a change can lower (`eighth.invariants.lowered`),
  the seventh's cost and criterion on a part and the eighth's cost and
  criterion for the comparison, the writers, `compare_evidence`, the Lean
  report runner, and the seventh's and eighth's explorations and sequence
  counts for the comparison. Defined afresh: the empty beginning; what a
  result adds to what is given (its terms and both totals); the exchange of
  the two relations (`swap`); the attempt record; the exploration from an
  empty state with two relations; the cost in closed form (the size: terms
  plus both totals, which is the seventh's cost of the `r` part plus the `s`
  total and *not* the sum of the seventh's costs of the two parts, which
  counts the terms twice); the changes that raise the cost by exactly one
  (the additions of either relation); reachability (has a term, or the
  start is empty); the shortest-sequence counts (exact for every result;
  the one-term closed form `C(p + q, p)` for `ara` `p` times and `asa` `q`
  times, where the seventh had one sequence); the independent count of the
  results by terms and total multiplicity, the empty state included,
  restricted to size within the rounds; the two-term closed form
  `(C(t + 7, 7) + [t even]·C(t/2 + 3, 3)) / 2`; the count of results left
  unchanged by exchanging the relations (the seventh's count at half the
  total); the comparison with the seventh (nothing in `s`, and by the
  exchange nothing in `r`) and with the eighth (names forgotten); the
  property witnesses. Earlier derivations' files are not modified except to
  correct a defect, recorded in the relevant change log.
- `tests/test_ninth_*.py` — tests of `code/ninth/`; all of `code/` stays at
  ≥ 95 % line and ≥ 95 % branch coverage, every `code/**/evidence.py` fully
  covered (an injection test for every differential check); `mypy --strict`
  passes; the prose watchlist stays clean.
- `lean4/Ninth/` — a ninth Lean library in the same Lake package (the
  lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Eighth`. New: a two-relation state
  without names `NDSt` (terms, a multiplicity function for each relation),
  `WF`, `size`, the empty state, the four operations (the eighth's with the
  names left out), the exchange of the relations `swap`; the maps
  `DSt.forget : DSt → NDSt`, `NDSt.name : NDSt → ℕ → DSt`, `NDSt.proj : NDSt
  → Rel → NSt` and `NSt.ofR : NSt → NDSt`; `Step9` (four kinds over two
  relations, no names), `Reach9`; `Step8.forget`, `Reach8.forget`,
  `Step9.name`, `Reach9.name`, `Step9.proj`, `Reach9.proj`, `Step7.ofR`,
  `Reach7.ofR`; the cost (the size), the addition path through `name`, the
  has-a-term criterion, the comparison with the seventh and the eighth.
- `evidence/ninth/` — written by `python code/generate_ninth.py`; the axiom
  report by `python code/lean_report_ninth.py`; `--check` regenerates into a
  temporary folder and compares.
- `paper/ninth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the ninth seed (`research/ninth/`)
Sentence-by-sentence diff against the eighth seed and the seventh's; the
notion table with source statuses; which readings change: C2 (what is
given) is replaced by the seed (nothing; the empty state; one beginning);
C4 (sameness) collapses to one reading (no names; derived as under the
seventh) acting on both relations at once (as under the eighth); C5⁗ (what
is a change: the eighth's, in either relation, an identification adding up
the multiplicities of the merged pairs in each relation separately)
unchanged; C6 (round 0 the empty state; round 1 the one-term state alone;
the order of changes: identifications, removals in `r`, in `s`, a term,
additions in `r`, in `s`) unchanged in kind; C8′ (bound on terms and
rounds) unchanged in kind. Expected consequences to be proved or refuted:
the first change adds a term and nothing else is a change on the empty
state; a term once there stays, so the empty state is a result (round 0)
never returned to; the size (terms plus both totals) moves by exactly one
per change and additions alone reach every well-formed state, so the fewest
changes to a result is its size — the seventh's collapse survives — and it
is the seventh's cost of the `r` part plus the `s` total — the eighth's
additivity survives — while the sum of the seventh's costs of the two parts
overcounts the terms, which the two relations share: the cost is a sum of
the two relations' totals and one count of terms, not of two per-relation
costs; the results are every well-formed two-relation state, the empty one
included, and they are jointly free (any two well-formed parts on the same
terms make a result: the eighth's product survives); the seventh's results
are exactly the results asserting nothing with `s`, and, by the exchange of
the relations, exactly those asserting nothing with `r`; the eighth's
results (any rewriting, either beginning) are exactly the results with a
term, and its results with the names kept, once forgotten, are results;
reachability is "has a term, or the start is empty" — the seventh's
criterion on the shared terms, which is the eighth's "the `s` part imposes
nothing" with nothing left for the `r` part to impose either; mutual among
the results with a term, one-way out of the empty state; the count of
results with `n ≥ 2` terms is not the product of the seventh's
single-relation counts — the eighth's non-product survives verbatim, since
the eighth's count under any rewriting is this seed's count — and equals it
for `n ≤ 1`; the exchange of the two relations is a symmetry of the results,
the cost and reachability (new: the eighth's given broke it); the seventh's
"one-term results have one shortest sequence" fails: the additions of the
two relations interleave, `C(p + q, p)` sequences; no tested statement holds
in every result; a result with `n` terms and `d_r + d_s` asserted pairs has
`C(n, 2) + d_r + d_s + 1 + 2n²` changes and the empty state one; the results
of round `r` with at most two terms are `[r = 0] + [r ≥ 1]·r + [r ≥ 2]·(C(r
+ 5, 7) + [r even]·C(r/2 + 2, 3)) / 2`, so the seed's 100 rounds with two
terms hold about 10^11 results and a lower bound on rounds is declared with
the closed form proved for every round.

### Phase 2 — `code/ninth/` and `tests/`
- the empty beginning; changes (the eighth's four kinds over two relations,
  every one performed; the attempt record with the outcome and whether it
  asserts some `xrx`, some `xsx`); the exploration from the empty state,
  bounded in terms and rounds; full attempt logs at a small bound;
- cost in closed form (the size) checked against the explored rounds; every
  change within the bound checked to move the size by exactly one; the
  changes that raise the cost by one characterised (the additions) and
  checked; parity checked (no change keeps the round); the cost compared
  with the seventh's on each part (the `r` cost plus the `s` total equals
  it; the sum of both parts' costs exceeds it by the terms);
- shortest sequences by dynamic programming over the additions, exact for
  every explored result; the one-term closed form `C(p + q, p)` checked;
- an independent count of the results by terms and total multiplicity (the
  eighth's `count_free`, the empty state added), restricted to size within
  the rounds, as the completeness certificate; the two-term closed form
  checked against it and against the two-term run; the product of the
  seventh's counts recorded beside it (equal for `n ≤ 1`, exceeded for
  `n ≥ 2`); the results unchanged by the exchange of the relations counted
  and checked against the seventh's count at half the total;
- the ninth exploration compared with the seventh's at the same bound and
  rounds: the results asserting nothing with `s`, read as their `r` parts,
  with their rounds and their shortest-sequence counts, must be the
  seventh's; likewise the results asserting nothing with `r` read as their
  `s` parts; every result's exchange must be a result at the same round with
  the same sequence count;
- the ninth exploration compared with the eighth's (any rewriting, both
  `bra` alternatives, at the same bound on terms and four rounds fewer): the
  results with a term whose eighth-seed cost is within the eighth's rounds
  must be exactly the eighth's results, each at the round its eighth-seed
  cost gives; the eighth's results with the names kept, once forgotten, must
  be results (the computed form of the citation);
- reachability by the has-a-term criterion checked against breadth-first
  search along the changes among the results within a small bound, and
  compared with the seventh's criterion on each part and with the eighth's
  criterion on the results with a term;
- per result the counts of changes making some `xrx` or some `xsx`
  asserted, checked against the eighth's function on each part;
- property witnesses for "what does not follow", the joint statements and
  the exchange included;
- deterministic evidence writer with `--check`; Lean axiom-report writer for
  `lean4/Ninth/Axioms.lean`.

### Phase 3 — `lean4/Ninth/`
Targets, in order:
1. `NDSt`, `WF`, `size`, `empty`, the four operations, `swap`; `forget`,
   `name`, `proj`, `ofR` and their commutations with the operations
   (definitional where possible); `Step9` (four kinds), `Reach9`;
   `Step8.forget`, `Reach8.forget`; `Step9.name`, `Reach9.name`;
   `Step9.proj`, `Reach9.proj`; `Step7.ofR`, `Reach7.ofR`; `Step9.swap`,
   `Reach9.swap`; well-formedness kept; the outcome of every change on a
   well-formed state has a term, so a term stays (`Step9.nonempty`,
   `Reach9.nonempty`); the first change adds a term
   (`first_change_adds_term9`); the empty state is reached only from itself
   in zero changes (`reach9_empty_iff`).
2. Cost: `Step9.size_step` (the size moves by exactly one), `Reach9.size_le`,
   `fewest_changes9_lower`, `reach9_addTerms` (the terms one by one),
   `reach9_raise` (one relation's multiplicities, the eighth's `reach8_raise`
   through `name`), `reach9_by_additions` (from the empty state every
   well-formed state in exactly its size), `fewest_changes9`,
   `Reach9.size_parity`, `shortest_are_additions9`, `cost_oneTerm9`;
   `size9_eq` (the size is the seventh's size of the `r` part plus the `s`
   total: the eighth's additivity with the seventh's cost) and
   `size9_add_card` (the sum of the two parts' sizes is the size plus the
   terms: the per-relation costs do not add up, the terms being shared),
   with the one-term witness; `size9_swap`.
3. Reachability: `reach9_of_nonempty` (the eighth's `reach8_of_names`
   through `name`), `reach9_iff`, `result9_iff`, `results_pair9` (jointly
   free), `empty_is_a_result9`, `reach9_symm`, `reach9_total`,
   `empty_never_returned9`, `no_cycle_at_empty9`, `cycle2_9`,
   `Reach9.unbounded`, the failures of one-way reachability among states
   with a term (`no_return_fails9`, `antisymm_fails9`,
   `length_not_unique9`), `reach9_swap`.
4. What survives (`Ninth/Compare.lean`): from the seventh — every result of
   the seventh is a result of the ninth with nothing in `s` at the same
   round (`results_ofR7`), the results asserting nothing with `s` are the
   seventh's (`results_r_iff9`) and by the exchange so are those asserting
   nothing with `r` (`results_s_iff9`), both parts of every result are
   seventh results (`proj_results9`), the cost survives as the size and adds
   up with the terms counted once (`cost_survives7`), the criterion survives
   on each part (`criterion_survives7`); from the eighth — every result of
   the eighth (either beginning, either reading) is a result of the ninth
   with its names forgotten (`results_forget8_A`, `_B`), every result of the
   ninth with a term is a result of the eighth once named
   (`results_name8`), the empty state is new (`empty_is_new9`), the
   criterion survives on states with a term as "always"
   (`criterion_survives8`), the eighth's cost does not survive
   (`eighth_cost_fails`: the one-term state, one change here, two there),
   the size difference survives with nothing given
   (`size_difference_survives9`), the non-product count is the eighth's own
   (paper), the names and the one-way merge are vacuous
   (`names_merged_vacuous9`), the interaction of the relations is still
   through the terms alone (`interaction9`).
5. `rename9`, `Step9.rename`, `Reach9.rename`, `size_rename9`,
   `rename9_empty`, `fewest_changes9_every_writing`. Attempted once; if a
   step does not close it is proved in the paper and marked "not in Lean".
`#print axioms` for every theorem the ninth paper cites, into
`evidence/ninth/lean_axioms.txt`.

### Phase 4 — `evidence/ninth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The eight earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/ninth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives with nothing given and two relations; a
section answering the task's question: whether the seventh's collapses and
the eighth's independence hold together, and where they do not — the
shared terms in the cost, the shared rewriting in the count, the
interleaving in the shortest sequences, the exchange symmetry; final
section: nearest known results and differences — the only place where
outside names appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, push, pull request.

## Stopping conditions (ninth derivation)

The run stops when AA1–AA9 hold, or when a blocker is hit.

- AA1 Every notion in `paper/ninth/paper.md` has one recorded source status.
- AA2 Every claim in `paper/ninth/claim_ledger.md` has evidence, or is open.
- AA3 Every alternative is kept, or eliminated by a cited proof.
- AA4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- AA5 `lake build` (pinned toolchain, inside `lean4/`) passes for all nine
  libraries; no `sorry`, `admit`, or declared axiom in `lean4/`; all nine
  axiom reports regenerated and committed.
- AA6 `evidence/ninth/` regenerates byte-identically (`--check`); the
  earlier derivations' evidence still regenerates byte-identically.
- AA7 Every use of an earlier result in the ninth paper is cited and
  re-checked, with the re-check saying whether it survives with nothing
  given and two relations (ledger column "re-check").
- AA8 The prose watchlist passes on the tracked tree; every pinned hit of
  the ninth paper is in its final section.
- AA9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and rounds together, as the fourth's to eighth's. One
  beginning and one reading, so three explorations as the seventh's; the
  results of round `r` are the well-formed two-relation states of size `r`,
  which the independent count gives in advance (1, 1, 3, 8, 29, 104, 420,
  1 783, 8 115, 38 813, 194 888, … without any bound on terms). Targets: 5
  terms with 8 rounds (10 416 results), 3 terms with 9 rounds, 2 terms with
  12 rounds (22 021 results; the seed's 100 rounds with two terms hold
  about 10^11), a counts-only census at 6 terms with 8 rounds, full attempt
  logs at 2 terms and 3 rounds, reachability among the results of 3 terms
  and 5 rounds along the changes among those of 3 terms and 7 rounds. The
  eighth's explorations for the comparison run at the same bound on terms
  with four rounds fewer (every eighth result of cost `c` has size at most
  `c + 4`), under both readings and from both beginnings. Any run that does
  not complete in minutes here has its rounds lowered first, then its terms;
  the bounds used are declared in the paper; the frontier is exported
  exactly; completeness within the bound is certified by the independent
  count; the two-term round counts are proved in closed form for every
  round.
- Rounds: at most 100; no change is invented.
- Lean targets 1–4 required; target 5 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `worktree-ninth-derivation`, made from `main` after the eighth's
  pull request was merged; the pull request is opened against `main`.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The worktree's
`lean4/.lake/packages` is still the local junction to the main checkout's
pinned packages (checked before Phase 0: `lake build` of the eight
libraries completes with nothing to do; no download happens).

## How to run (ninth derivation)

From the repository root:
- `python -m pytest` (all tests, nine derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_ninth.py` writes `evidence/ninth/`;
  `python code/generate_ninth.py --check` compares with a fresh
  regeneration;
- `python code/lean_report_ninth.py` builds `lean4/` and writes
  `evidence/ninth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Tenth derivation (`prompt/tenth/`) — plan and stopping conditions

Written before any other work of the tenth derivation, as
`prompt/tenth/prompt.md` requires. Inputs: `prompt/tenth/prompt.md` and
`prompt/tenth/seed_prompt.md`; the nine earlier derivations (`paper/`,
`paper/second/` … `paper/ninth/`, `code/xry/` … `code/ninth/`,
`lean4/H3V7N5QF/` … `lean4/Ninth/`, `evidence/` … `evidence/ninth/`) are
cited where used, never assumed. Everything above stays in force (isolation,
no network, `prompt/` untouched, `.lake/` never committed, bookkeeping rules
1–4, the evidence-module coverage gate). Rule 5 of the tenth task: every
result of an earlier derivation that is used is cited and its proof
re-checked from the tenth seed, and the re-check says whether the result
survives once every change carries a leftover outcome — in particular
whether the ninth's collapses (cost is the size, reachability is having a
term, one sameness) and independence (results jointly free, cost a sum of
the two totals with the terms counted once, count not a product) survive
once the seed records what each change leaves. In Lean the re-check is by
the identity on the ninth's states (`NDSt`) and the identity on the ninth's
changes (`Step9` as `Step10`): leftover is recorded on the change, not as a
third multiplicity beside `r` and `s`; every change of the ninth is a
change of the tenth and conversely. The unchosen reading that puts leftover
status into the result is kept and computed separately. Or by observing
that the statement mentions no leftover; or by computing it again from the
tenth seed's own exploration and comparing with the ninth's on every
result.

## What differs in the seed

One passage (`diff` against the ninth seed) is added after the four kinds:

"After every change, record what that change leaves. A leftover is not an
assertion. Nothing left, a leftover that a later change of the four kinds
can clear, and a leftover that none of them can, are three outcomes.
Declare which, for every change."

Every other sentence is identical to the ninth seed (`diff`), and so to the
eighth with the seventh's empty beginning. The state stays the ninth's
(terms, a multiplicity for each ordered pair in `r` and in `s`, no names);
the beginning stays empty; the four kinds are the ninth's; nothing is
forbidden. What the ninth argued from the state and the four kinds alone
(the size as the cost, the has-a-term criterion, jointly free results, the
count by series, the exchange) must be re-examined with a leftover outcome
on every change; what it argued from terms and multiplicities without
mentioning the attempt record carries over through the identity on states.

The first seed had a forbidden `xrx` and a binary obstruction; the sixth
dropped both. This seed records, after every change, a three-way leftover
that is not an assertion. The task's question is whether that leftover is a
third kind of record beside the two relations, whether the three outcomes
split the ninth's changes, whether a leftover of one relation constrains
the other, and which of the ninth's results survive.

## Layout

- `research/tenth/` — reading notes (not evidence).
- `code/tenth/` — typed Python package for the tenth seed. Imported from
  the earlier packages what leftover leaves intact: the two-relation state
  without names (`eighth.state.DState` with `names = None`, the ninth's
  empty beginning, `swap`, sameness, `canonical`), the four kinds, the list
  of changes and `perform` (`eighth.changes` / `ninth.changes`), the
  two-change cycle, the ninth's cost (the size), reachability (has a term),
  independent count (`ninth.orbits`), the ninth's exploration, sequence
  counts and comparisons with the seventh and the eighth, the statements
  tested (`ninth.follows`), the writers, `compare_evidence`, the Lean
  report runner. Defined afresh: the leftover outcome of a change (three
  values); the attempt record carrying that outcome; the classification of
  every change of the ninth (additions leave nothing; a removal leaves a
  leftover that adding that assertion clears; an identification leaves a
  leftover that none of the four kinds can clear); whether a leftover of
  one relation constrains the other; the unchosen reading that tags a
  result with leftover status, and the witnesses that it yields results the
  ninth does not; the comparison with the ninth (same results, rounds,
  shortest-sequence counts under the chosen reading). Earlier derivations'
  files are not modified except to correct a defect, recorded in the
  relevant change log.
- `tests/test_tenth_*.py` — tests of `code/tenth/`; all of `code/` stays
  at ≥ 95 % line and ≥ 95 % branch coverage, every `code/**/evidence.py`
  fully covered (an injection test for every differential check);
  `mypy --strict` passes; the prose watchlist stays clean.
- `lean4/Tenth/` — a tenth Lean library in the same Lake package (the
  lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Ninth`. New: the three leftover
  outcomes `LeftOver`; `Step9.leftOver` (which outcome a change has);
  `clears` (a later change that restores what a removal took); `Step10`
  as `Step9` with the leftover recorded; `Reach10`; the identity maps
  `Step9.toStep10`, `Step10.toStep9`; the comparison with the ninth; the
  unchosen tagged state `Tagged` and the witnesses that its results are
  not the ninth's.
- `evidence/tenth/` — written by `python code/generate_tenth.py`; the axiom
  report by `python code/lean_report_tenth.py`; `--check` regenerates into
  a temporary folder and compares.
- `paper/tenth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the tenth seed (`research/tenth/`)
Sentence-by-sentence diff against the ninth seed; the notion table with
source statuses; which readings change: C6 gains a clause (every attempt
records a leftover outcome; the leftover is not an assertion and is not
counted among terms or assertions added); C5⁗ unchanged (the four kinds);
C2, C4, C8′ unchanged in kind. New chosen reading C-L1: leftover is
recorded on the change, not as a field of the result; a result remains a
two-relation state up to sameness; the three outcomes are declared by
kind, with "a later change of the four kinds can clear" read as: there is
one change of the four kinds on the outcome that restores what the leftover
records (the removed assertion), and "none of them can" read as: no one
change of the four kinds restores the two terms that were identified. New
unchosen reading C-L2, kept: leftover status is part of the result (a
three-valued tag, Uncleared absorbing). Expected consequences to be proved
or refuted: leftover is not a third multiplicity beside `r` and `s` under
C-L1 (it is a classification of the ninth's changes); the three outcomes
split the ninth's four kinds (additions / removals / identifications);
a leftover of a removal in one relation is cleared only by adding that
assertion in the same relation, so it does not constrain the other
relation's later changes; an identification leftover is not of one
relation (identification acts on both); under C-L1 the ninth's cost, the
has-a-term criterion, jointly free results and the non-product count
survive (the states and the changes are the ninth's); under C-L2 they do
not (witnesses: the one-term state asserting nothing, reached with three
tags at three costs).

### Phase 2 — `code/tenth/` and `tests/`
- leftover outcomes; the classification of every change of the ninth;
  the attempt record carrying the outcome; exploration reusing the ninth's
  with the leftover field filled; full logs at a small bound;
- every change within the bound checked to have exactly one of the three
  outcomes, by kind; a removal leftover cleared by adding that assertion
  and not by a change of the other relation; an identification leftover
  not cleared by any one later change of the four kinds; additions leaving
  nothing;
- the tenth exploration compared with the ninth's at the same bound and
  rounds: the results, rounds and shortest-sequence counts must be the
  ninth's (the computed form of the citation under C-L1);
- the unchosen tagged reading explored at a small bound: more results than
  the ninth's, cost not the size, jointly free parts with a shared tag;
- reachability, independent count, two-term closed form reused from the
  ninth and re-checked;
- property witnesses for "what does not follow", including leftover
  statements;
- deterministic evidence writer with `--check`; Lean axiom-report writer
  for `lean4/Tenth/Axioms.lean`.

### Phase 3 — `lean4/Tenth/`
Targets, in order:
1. `LeftOver` (three constructors); `Step9.leftOver`; additions have
   `nothingLeft`; a removal has `clearable`; an identification has
   `uncleared`; `Step10` as `Step9`; `Reach10` as `Reach9`;
   `Step9.toStep10`, `Step10.toStep9` (every change of the ninth is a
   change of the tenth and conversely); well-formedness, at least one
   term, the empty state, the first change, inherited through the
   identity (cited, re-checked).
2. Clearing: a removal of `q` at `(x, y)` is cleared by adding that
   assertion in `q` (`clears_remove`); a change of the other relation
   does not clear it (`other_rel_not_clear`); no one `Step9` after an
   identification restores the two identified terms
   (`identify_not_cleared`); leftover is not an assertion
   (`leftover_not_assertion`: the outcome is `LeftOver`, not a
   multiplicity).
3. What survives (`Tenth/Compare.lean`): the ninth's results, cost
   (`fewest_changes10`), reachability (`reach10_iff`), jointly free
   results (`results_pair10`) and the identity on states (`toNDSt`);
   leftover is not a third relation (`no_third_rel`); the three outcomes
   split the kinds (`split_kinds`); a leftover of one relation does not
   constrain the other (`no_cross_constraint`); the unchosen tag
   (`Tagged`) has results the ninth has not (`tagged_extra`) and a cost
   that is not the size (`tagged_cost_fails`).
4. `Step10.swap`, `leftOver_swap` (exchange carries leftovers with the
   relations). Attempted once; if a step does not close it is proved in
   the paper and marked "not in Lean".
`#print axioms` for every theorem the tenth paper cites, into
`evidence/tenth/lean_axioms.txt`.

### Phase 4 — `evidence/tenth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The nine earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/tenth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives leftover outcomes; a section answering
the task's question: whether leftover is a third record beside the two
relations, whether the three outcomes split the ninth's changes, whether
a leftover of one relation constrains the other, and which of the ninth's
cost, reachability, results and count survive; final section: nearest
known results and differences — the only place where outside names
appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, push, pull request.

## Stopping conditions (tenth derivation)

The run stops when AB1–AB9 hold, or when a blocker is hit.

- AB1 Every notion in `paper/tenth/paper.md` has one recorded source status.
- AB2 Every claim in `paper/tenth/claim_ledger.md` has evidence, or is open.
- AB3 Every alternative is kept, or eliminated by a cited proof.
- AB4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- AB5 `lake build` (pinned toolchain, inside `lean4/`) passes for all ten
  libraries; no `sorry`, `admit`, or declared axiom in `lean4/`; all ten
  axiom reports regenerated and committed.
- AB6 `evidence/tenth/` regenerates byte-identically (`--check`); the
  earlier derivations' evidence still regenerates byte-identically.
- AB7 Every use of an earlier result in the tenth paper is cited and
  re-checked, with the re-check saying whether it survives leftover
  outcomes on every change (ledger column "re-check").
- AB8 The prose watchlist passes on the tracked tree; every pinned hit of
  the tenth paper is in its final section.
- AB9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and on rounds together, as the ninth's, since under
  C-L1 the results of round `r` are the ninth's. Targets: 5 terms with 8
  rounds, 3 terms with 9, 2 terms with 12, a counts-only census at 6 terms
  with 8 rounds, full attempt logs at 2 terms and 3 rounds, reachability
  among the results of 3 terms and 5 rounds along the changes among those
  of 3 terms and 7 rounds. The ninth's exploration for the comparison runs
  at the same bounds. The unchosen tagged reading is explored at 2 terms
  with 4 rounds (three tags on the ninth's states). Any run that does not
  complete in minutes here has its rounds lowered first, then its terms;
  the bounds used are declared in the paper; the frontier is exported
  exactly; completeness within the bound is certified by the ninth's
  independent count (C-L1) and by a tagged count (C-L2).
- Rounds: at most 100; no change is invented.
- Lean targets 1–3 required; target 4 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `worktree-tenth-derivation`, made from the ninth's last commit
  with the tenth-through-fifteenth seeds merged; the pull request is
  opened against `worktree-ninth-derivation` if that branch is not yet on
  `main`, otherwise against `main`.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The
checkout's `lean4/.lake/packages` is the pinned packages of this same
repository (checked before Phase 0; no download happens).

## How to run (tenth derivation)

From the repository root:
- `python -m pytest` (all tests, ten derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_tenth.py` writes `evidence/tenth/`;
  `python code/generate_tenth.py --check` compares with a fresh
  regeneration;
- `python code/lean_report_tenth.py` builds `lean4/` and writes
  `evidence/tenth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Eleventh derivation (`prompt/eleventh/`) — plan and stopping conditions

Written before any other work of the eleventh derivation, as
`prompt/eleventh/prompt.md` requires. Inputs: `prompt/eleventh/prompt.md` and
`prompt/eleventh/seed_prompt.md`; the ten earlier derivations (`paper/`,
`paper/second/` … `paper/tenth/`, `code/xry/` … `code/tenth/`,
`lean4/H3V7N5QF/` … `lean4/Tenth/`, `evidence/` … `evidence/tenth/`) are
cited where used, never assumed. Everything above stays in force
(isolation, no network, `prompt/` untouched, `.lake/` never committed,
bookkeeping rules 1–4, the evidence-module coverage gate). Rule 5 of the
eleventh task: every result of an earlier derivation that is used is cited
and its proof re-checked from the eleventh seed, and the re-check says
whether the result survives once a writing can collide terms it does not
identify — in particular whether the ninth's one sameness, has-a-term
reachability, and jointly free results survive. In Lean the re-check is by
the identity on the ninth's states (`NDSt`) and the identity on the ninth's
changes (`Step9` as `Step11`): a writing is a function from terms to
letters, recorded as a reading of a result, not as a third multiplicity
beside `r` and `s`; every change of the ninth is a change of the eleventh
and conversely. The unchosen reading that puts the writing into the result
is kept and computed separately. Or by observing that the statement
mentions no writing; or by computing it again from the eleventh seed's own
exploration and comparing with the ninth's on every result.

## What differs in the seed

One passage (`diff` against the ninth seed) is added after the four kinds:

"A writing of terms may give two terms the same letter while they remain
two terms. Assertions are read from the writing. If two terms are written
the same and their assertions differ, the writing does not determine the
assertions."

Every other sentence is identical to the ninth seed (`diff`), and so to
the eighth with the seventh's empty beginning. The tenth seed's leftover
passage is not in this seed. The state stays the ninth's (terms, a
multiplicity for each ordered pair in `r` and in `s`, no names); the
beginning stays empty; the four kinds are the ninth's; nothing is
forbidden. What the ninth argued from the state and the four kinds alone
(the size as the cost, the has-a-term criterion, jointly free results, the
count by series, the exchange) must be re-examined with a writing that can
collide terms without identifying them; what it argued from terms and
multiplicities without mentioning a writing carries over through the
identity on states.

The ninth's sameness already treats two results that differ only in how
their terms are written as the same result; here a writing can collide two
terms without identifying them. The task's question is when the writing
determines the assertions, what a collision (same writing, different
assertions) forbids of every coarser writing, whether a collision in one
relation constrains the other, and which of the ninth's results survive
once writing and identifying are two different things.

## Layout

- `research/eleventh/` — reading notes (not evidence).
- `code/eleventh/` — typed Python package for the eleventh seed. Imported
  from the earlier packages what writing leaves intact: the two-relation
  state without names (`eighth.state.DState` with `names = None`, the
  ninth's empty beginning, `swap`, sameness, `canonical`), the four kinds,
  the list of changes and `perform` (`eighth.changes` / `ninth.changes`),
  the two-change cycle, the ninth's cost (the size), reachability (has a
  term), independent count (`ninth.orbits`), the ninth's exploration,
  sequence counts and comparisons with the seventh and the eighth, the
  statements tested (`ninth.follows`), the writers, `compare_evidence`,
  the Lean report runner. Defined afresh: a writing of terms (letters, not
  necessarily injective); when a writing determines the assertions
  (constant multiplicity on every letter-pair rectangle, in each
  relation); a collision (two terms the same letter, the rectangle not
  constant); coarser writings; whether a collision of one relation
  constrains the other; the unchosen reading that tags a result with a
  writing, and the witnesses that it yields results the ninth does not;
  the comparison with the ninth (same results, rounds, shortest-sequence
  counts under the chosen reading). Earlier derivations' files are not
  modified except to correct a defect, recorded in the relevant change
  log.
- `tests/test_eleventh_*.py` — tests of `code/eleventh/`; all of `code/`
  stays at ≥ 95 % line and ≥ 95 % branch coverage, every
  `code/**/evidence.py` fully covered (an injection test for every
  differential check); `mypy --strict` passes; the prose watchlist stays
  clean.
- `lean4/Eleventh/` — an eleventh Lean library in the same Lake package
  (the lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Tenth` (and through it `Ninth`).
  New: a writing `ℕ → ℕ`; `determines` (every letter-pair rectangle
  constant in both relations); `injOn` writings determine; coarser
  writings inherit failure to determine; a collision of one relation need
  not be a collision of the other; `Step11` as `Step9`; `Reach11`; the
  identity maps `Step9.toStep11`, `Step11.toStep9`; identifying drops a
  term, a colliding writing does not; the comparison with the ninth; the
  unchosen labeled state `Labeled` and the witnesses that its results are
  not the ninth's.
- `evidence/eleventh/` — written by `python code/generate_eleventh.py`;
  the axiom report by `python code/lean_report_eleventh.py`; `--check`
  regenerates into a temporary folder and compares.
- `paper/eleventh/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the eleventh seed (`research/eleventh/`)
Sentence-by-sentence diff against the ninth seed; the notion table with
source statuses; which readings change: C6 gains a clause (a writing of
terms may collide two terms that remain two; assertions are read from the
writing; a writing that writes two terms the same whose assertions differ
does not determine the assertions); C5⁗ unchanged (the four kinds;
identifying is not writing); C2, C4, C8′ unchanged in kind. New chosen
reading C-W1: a writing is a function from a result's terms to letters,
not a field of the result; a result remains a two-relation state up to
sameness; the writing determines the assertions exactly when, in each
relation, the multiplicity is constant on every rectangle of terms that
share a pair of letters. "Coarser" means a writing that writes together
every pair the first writing writes together, and possibly more. New
unchosen reading C-W2, kept: the writing (up to renaming letters) is part
of the result. Expected consequences to be proved or refuted: an
injective writing always determines; a collision forbids every coarser
writing from determining; a collision in one relation does not constrain
the other; writing is not identifying (the two terms remain); under C-W1
the ninth's cost, has-a-term criterion, jointly free results and
non-product count survive; under C-W2 they do not as a count of results
(more writings than states).

### Phase 2 — `code/eleventh/` and `tests/`
- writings of a state's terms (restricted growth strings); determination
  and collision, by relation and jointly; coarser writings; exploration
  reusing the ninth's; full logs at a small bound;
- every writing of every explored result checked: injective writings
  determine; a collision forbids every coarser writing; a collision of
  `r` need not be a collision of `s`; identifying two terms drops a term,
  writing them the same does not;
- the eleventh exploration compared with the ninth's at the same bound
  and rounds: the results, rounds and shortest-sequence counts must be
  the ninth's (the computed form of the citation under C-W1);
- the unchosen labeled reading explored at a small bound: more results
  than the ninth's (Bell number of writings per state);
- reachability, independent count, two-term closed form reused from the
  ninth and re-checked;
- property witnesses for "what does not follow", including writing
  statements;
- deterministic evidence writer with `--check`; Lean axiom-report writer
  for `lean4/Eleventh/Axioms.lean`.

### Phase 3 — `lean4/Eleventh/`
Targets, in order:
1. `Writing` (`ℕ → ℕ`); `determines`, `determinesRel`; injective
   writings determine (`inj_determines`); `Step11` as `Step9`; `Reach11`
   as `Reach9`; `Step9.toStep11`, `Step11.toStep9`; well-formedness, at
   least one term, the empty state, the first change, inherited through
   the identity (cited, re-checked).
2. Coarser writings: if `w` does not determine then neither does any
   coarser writing (`coarser_of_not_determines`); a collision of one
   relation need not be a collision of the other (`r_collision_not_s`);
   identifying two terms drops a term (`identify_drops_a_term`); a
   colliding writing leaves both terms (`collide_keeps_terms`); writing
   is not a multiplicity (`writing_not_assertion`).
3. What survives (`Eleventh/Compare.lean`): the ninth's results, cost
   (`fewest_changes11`), reachability (`reach11_iff`), jointly free
   results (`results_pair11`) and the identity on states (`toNDSt`);
   writing is not a third relation (`no_third_rel`); injective writings
   determine (`split_injective`); a leftover of one relation does not
   constrain the other (`no_cross_constraint`); the unchosen label
   (`Labeled`) has results the ninth has not (`labeled_extra`).
4. `Step11.swap`, `determines_swap` (exchange carries writings with the
   relations). Attempted once; if a step does not close it is proved in
   the paper and marked "not in Lean".
`#print axioms` for every theorem the eleventh paper cites, into
`evidence/eleventh/lean_axioms.txt`.

### Phase 4 — `evidence/eleventh/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The ten earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/eleventh/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives colliding writings; a section answering
the task's question: when the writing determines the assertions, what a
collision forbids of coarser writings, whether a collision of one
relation constrains the other, and which of the ninth's cost,
reachability, results and count survive; final section: nearest known
results and differences — the only place where outside names appear),
`claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, push, pull request.

## Stopping conditions (eleventh derivation)

The run stops when AC1–AC9 hold, or when a blocker is hit.

- AC1 Every notion in `paper/eleventh/paper.md` has one recorded source
  status.
- AC2 Every claim in `paper/eleventh/claim_ledger.md` has evidence, or is
  open.
- AC3 Every alternative is kept, or eliminated by a cited proof.
- AC4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- AC5 `lake build` (pinned toolchain, inside `lean4/`) passes for all
  eleven libraries; no `sorry`, `admit`, or declared axiom in `lean4/`;
  all eleven axiom reports regenerated and committed.
- AC6 `evidence/eleventh/` regenerates byte-identically (`--check`); the
  earlier derivations' evidence still regenerates byte-identically.
- AC7 Every use of an earlier result in the eleventh paper is cited and
  re-checked, with the re-check saying whether it survives a writing that
  can collide terms it does not identify (ledger column "re-check").
- AC8 The prose watchlist passes on the tracked tree; every pinned hit of
  the eleventh paper is in its final section.
- AC9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and on rounds together, as the ninth's, since under
  C-W1 the results of round `r` are the ninth's. Targets: 3 terms with 6
  rounds, 3 terms with 5, 2 terms with 8, full attempt logs at 2 terms
  and 3 rounds; the unchosen labeled reading at 2 terms with 4 rounds
  (writings of the ninth's states). Any run that does not complete in
  minutes here has its rounds lowered first, then its terms; the bounds
  used are declared in the paper; the frontier is exported exactly;
  completeness within the bound is certified by the ninth's independent
  count (C-W1) and by a labeled count (C-W2).
- Rounds: at most 100; no change is invented.
- Lean targets 1–3 required; target 4 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `worktree-eleventh-derivation`, made from the tenth's last
  commit; the pull request is opened against `worktree-tenth-derivation`
  if that branch is not yet on `main`, otherwise against `main`.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The
checkout's `lean4/.lake/packages` is the pinned packages of this same
repository (checked before Phase 0; no download happens).

## How to run (eleventh derivation)

From the repository root:
- `python -m pytest` (all tests, eleven derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_eleventh.py` writes `evidence/eleventh/`;
  `python code/generate_eleventh.py --check` compares with a fresh
  regeneration;
- `python code/lean_report_eleventh.py` builds `lean4/` and writes
  `evidence/eleventh/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Twelfth derivation (`prompt/twelfth/`) — plan and stopping conditions

Written before any other work of the twelfth derivation, as
`prompt/twelfth/prompt.md` requires. Inputs: `prompt/twelfth/prompt.md` and
`prompt/twelfth/seed_prompt.md`; the eleven earlier derivations (`paper/`,
`paper/second/` … `paper/eleventh/`, `code/xry/` … `code/eleventh/`,
`lean4/H3V7N5QF/` … `lean4/Eleventh/`, `evidence/` … `evidence/eleventh/`)
are cited where used, never assumed. Everything above stays in force
(isolation, no network, `prompt/` untouched, `.lake/` never committed,
bookkeeping rules 1–4, the evidence-module coverage gate). Rule 5 of the
twelfth task: every result of an earlier derivation that is used is cited
and its proof re-checked from the twelfth seed, and the re-check says
whether the result survives once an identification keeps a per-relation
record of which assertions of the two terms become one — in particular
whether the ninth's size-as-cost, jointly free results, and exchange of
the two relations survive. In Lean the re-check is by the identity on the
ninth's states (`NDSt`) and the identity on the ninth's changes (`Step9`
as `Step12`): the record is computed from the start and the two terms,
per relation, and is kept with the result of that identification; it is
not a third multiplicity beside `r` and `s`; every change of the ninth is
a change of the twelfth and conversely. The unchosen reading that puts
the record into the result as a field (so two identifications that land
on the same two-relation state with different records are different
results) is kept and computed separately. Or by observing that the
statement mentions no identification record; or by computing it again
from the twelfth seed's own exploration and comparing with the ninth's on
every result.

## What differs in the seed

One passage (`diff` against the ninth seed) is added after the four kinds:

"Identifying two terms records, for each relation, which assertions of
those two terms become one assertion. The record is kept with the
result."

Every other sentence is identical to the ninth seed (`diff`), and so to
the eighth with the seventh's empty beginning. The tenth seed's leftover
passage and the eleventh seed's colliding-writing passage are not in this
seed. The state stays the ninth's (terms, a multiplicity for each ordered
pair in `r` and in `s`, no names); the beginning stays empty; the four
kinds are the ninth's; nothing is forbidden. What the ninth argued from
the state and the four kinds alone (the size as the cost, the has-a-term
criterion, jointly free results, the count by series, the exchange) must
be re-examined with a per-relation record of each identification; what it
argued from terms and multiplicities without mentioning identification
carries over through the identity on states.

The eighth and ninth already merge both relations at once; they do not
keep a record of what the merge lost. The task's question is whether the
record of one relation is determined by that relation alone, whether the
two records can differ, whether a later change can restore what the
record lists, and which of the ninth's results survive once identifying
carries a kept record.

## Layout

- `research/twelfth/` — reading notes (not evidence).
- `code/twelfth/` — typed Python package for the twelfth seed. Imported
  from the earlier packages what the identification record leaves intact:
  the two-relation state without names (`eighth.state.DState` with
  `names = None`, the ninth's empty beginning, `swap`, sameness,
  `canonical`), the four kinds, the list of changes and `perform`
  (`eighth.changes` / `ninth.changes`), the two-change cycle, the ninth's
  cost (the size), reachability (has a term), independent count
  (`ninth.orbits`), the ninth's exploration, sequence counts and
  comparisons with the seventh and the eighth, the statements tested
  (`ninth.follows`), the writers, `compare_evidence`, the Lean report
  runner. Defined afresh: the per-relation identification record (which
  asserted pairs of the two terms become one pair); whether that record
  is determined by the relation alone; whether the two records can
  differ; whether a later change of the four kinds restores what the
  record lists; the unchosen reading that tags a result with the record,
  and the witnesses that it yields results the ninth does not; the
  comparison with the ninth (same results, rounds, shortest-sequence
  counts under the chosen reading). Earlier derivations' files are not
  modified except to correct a defect, recorded in the relevant change
  log.
- `tests/test_twelfth_*.py` — tests of `code/twelfth/`; all of `code/`
  stays at ≥ 95 % line and ≥ 95 % branch coverage, every
  `code/**/evidence.py` fully covered (an injection test for every
  differential check); `mypy --strict` passes; the prose watchlist stays
  clean.
- `lean4/Twelfth/` — a twelfth Lean library in the same Lake package (the
  lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Eleventh` (and through it `Ninth`).
  New: the identification record `IdentRecord` / `recordRel`; the record
  of one relation is determined by that relation's projection
  (`record_determined_by_rel`); the two records can differ
  (`r_record_not_s`); a later change that restores the listed assertions
  as separate assertions of two terms (`restores_listed`) fails on a
  non-empty merge and holds for the empty record by adding a term;
  `Step12` as `Step9`; `Reach12`; the identity maps `Step9.toStep12`,
  `Step12.toStep9`; the comparison with the ninth; the unchosen recorded
  state `Recorded` and the witnesses that its results are not the
  ninth's.
- `evidence/twelfth/` — written by `python code/generate_twelfth.py`; the
  axiom report by `python code/lean_report_twelfth.py`; `--check`
  regenerates into a temporary folder and compares.
- `paper/twelfth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the twelfth seed (`research/twelfth/`)
Sentence-by-sentence diff against the ninth seed; the notion table with
source statuses; which readings change: C6 gains a clause (identifying
records, for each relation, which assertions of the two terms become one,
and the record is kept with the result); C5⁗ unchanged (the four kinds;
an identification still merges both relations at once, and now also
records what each merge did); C2, C4, C8′ unchanged in kind. New chosen
reading C-M1: the record of an identification is computed from the start
state and the two terms, per relation (the grouping of asserted pairs
that share an image under the identification map); it is kept with the
result of that change as extra data on the attempt, not as a third
multiplicity beside `r` and `s`; a result remains a two-relation state
up to sameness. "Which assertions become one" is read as: the asserted
pairs that mention either identified term, grouped by the pair they
become. New unchosen reading C-M2, kept: the record (the pair of
per-relation groups) is a field of the result, persisting through later
non-identify changes and replaced by a new identification. Expected
consequences to be proved or refuted: the record of `r` is determined by
the `r` projection and the two terms, independently of `s`; the two
records can differ; a later change restores what a non-empty record
lists as separate two-term assertions for no one change of the four
kinds, while an empty record (nothing was asserted among the two terms)
is restored as a state by adding a term; under C-M1 the ninth's cost,
has-a-term criterion, jointly free results and non-product count
survive; under C-M2 they do not as a count of results (same underlying
state, different records).

### Phase 2 — `code/twelfth/` and `tests/`
- identification records per relation; determination by one relation;
  differing records; restoration; exploration reusing the ninth's with
  the record filled on every identification; full logs at a small bound;
- every identification within the bound checked: the `r` record ignores
  `s`; some identification has different `r` and `s` records; a non-empty
  record is not restored by any one later change; an empty record of two
  isolated terms is restored by adding a term;
- the twelfth exploration compared with the ninth's at the same bound
  and rounds: the results, rounds and shortest-sequence counts must be
  the ninth's (the computed form of the citation under C-M1);
- the unchosen recorded reading explored at a small bound: more results
  than the ninth's (same state, different records);
- reachability, independent count, two-term closed form reused from the
  ninth and re-checked;
- property witnesses for "what does not follow", including record
  statements;
- deterministic evidence writer with `--check`; Lean axiom-report writer
  for `lean4/Twelfth/Axioms.lean`.

### Phase 3 — `lean4/Twelfth/`
Targets, in order:
1. `IdentRecord`, `recordRel`, `recordOf`; the record of one relation is
   determined by that relation (`record_determined_by_rel`); `Step12` as
   `Step9`; `Reach12` as `Reach9`; `Step9.toStep12`, `Step12.toStep9`;
   well-formedness, at least one term, the empty state, the first change,
   inherited through the identity (cited, re-checked).
2. The two records can differ (`r_record_not_s`); a non-empty record is
   not restored by any one later `Step9` (`nonempty_not_restored`); an
   empty record of two isolated terms is restored by adding a term
   (`empty_record_restored_by_addTerm`); the record is not a multiplicity
   (`record_not_assertion`).
3. What survives (`Twelfth/Compare.lean`): the ninth's results, cost
   (`fewest_changes12`), reachability (`reach12_iff`), jointly free
   results (`results_pair12`) and the identity on states (`toNDSt`); the
   record is not a third relation (`no_third_rel`); a leftover of one
   relation does not constrain the other (`no_cross_constraint`); the
   unchosen recorded tag (`Recorded`) has results the ninth has not
   (`recorded_extra`).
4. `Step12.swap`, `record_swap` (exchange carries records with the
   relations). Attempted once; if a step does not close it is proved in
   the paper and marked "not in Lean".
`#print axioms` for every theorem the twelfth paper cites, into
`evidence/twelfth/lean_axioms.txt`.

### Phase 4 — `evidence/twelfth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The eleven earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/twelfth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives a kept identification record; a section
answering the task's question: whether the record of one relation is
determined by that relation alone, whether the two records can differ,
whether a later change can restore what the record lists, and which of
the ninth's cost, reachability, results and count survive; final section:
nearest known results and differences — the only place where outside
names appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, push, pull request.

## Stopping conditions (twelfth derivation)

The run stops when AD1–AD9 hold, or when a blocker is hit.

- AD1 Every notion in `paper/twelfth/paper.md` has one recorded source
  status.
- AD2 Every claim in `paper/twelfth/claim_ledger.md` has evidence, or is
  open.
- AD3 Every alternative is kept, or eliminated by a cited proof.
- AD4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch coverage over all of `code/` and
  every evidence module fully covered; `python -m mypy` passes.
- AD5 `lake build` (pinned toolchain, inside `lean4/`) passes for all
  twelve libraries; no `sorry`, `admit`, or declared axiom in `lean4/`;
  all twelve axiom reports regenerated and committed.
- AD6 `evidence/twelfth/` regenerates byte-identically (`--check`); the
  earlier derivations' evidence still regenerates byte-identically.
- AD7 Every use of an earlier result in the twelfth paper is cited and
  re-checked, with the re-check saying whether it survives a kept
  per-relation identification record (ledger column "re-check").
- AD8 The prose watchlist passes on the tracked tree; every pinned hit of
  the twelfth paper is in its final section.
- AD9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and on rounds together, as the ninth's, since under
  C-M1 the results of round `r` are the ninth's. Targets: 3 terms with 6
  rounds, 3 terms with 5, 2 terms with 8, full attempt logs at 2 terms
  and 3 rounds; the unchosen recorded reading at 2 terms with 5 rounds
  (records on the ninth's states). Any run that does not complete in
  minutes here has its rounds lowered first, then its terms; the bounds
  used are declared in the paper; the frontier is exported exactly;
  completeness within the bound is certified by the ninth's independent
  count (C-M1) and by a recorded count (C-M2).
- Rounds: at most 100; no change is invented.
- Lean targets 1–3 required; target 4 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `worktree-twelfth-derivation`, made from the eleventh's last
  commit; the pull request is opened against
  `worktree-eleventh-derivation` if that branch is not yet on `main`,
  otherwise against `main`.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The
checkout's `lean4/.lake/packages` is the pinned packages of this same
repository (checked before Phase 0; no download happens).

## How to run (twelfth derivation)

From the repository root:
- `python -m pytest` (all tests, twelve derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_twelfth.py` writes `evidence/twelfth/`;
  `python code/generate_twelfth.py --check` compares with a fresh
  regeneration;
- `python code/lean_report_twelfth.py` builds `lean4/` and writes
  `evidence/twelfth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Thirteenth derivation (`prompt/thirteenth/`) — plan and stopping conditions

Written before any other work of the thirteenth derivation, as
`prompt/thirteenth/prompt.md` requires. Inputs: `prompt/thirteenth/prompt.md` and
`prompt/thirteenth/seed_prompt.md`; the twelve earlier derivations (`paper/`,
`paper/second/` … `paper/twelfth/`, `code/xry/` … `code/twelfth/`,
`lean4/H3V7N5QF/` … `lean4/Twelfth/`, `evidence/` … `evidence/twelfth/`)
are cited where used, never assumed. Everything above stays in force
(isolation, no network, `prompt/` untouched, `.lake/` never committed,
bookkeeping rules 1–4, the evidence-module coverage gate). Rule 5 of the
thirteenth task: every result of an earlier derivation that is used is cited
and its proof re-checked from the thirteenth seed, and the re-check says
whether the result survives once a coarser writing of an assertion forgets
whether it was written with `r` or with `s` — in particular whether the
ninth's jointly free results, additive cost, and non-product count survive.
In Lean the re-check is by the identity on the ninth's states (`NDSt`) and
the identity on the ninth's changes (`Step9` as `Step13`): the coarser
writing is computed from the two multiplicities (their sum, a seventh
state), recorded with the result, and is not a third multiplicity beside
`r` and `s`; every change of the ninth is a change of the thirteenth and
conversely. The unchosen reading that takes the coarser writing as the
result (so two finer results that differ only in which relation wrote their
assertions may be the same coarser result) is kept and computed separately.
Or by observing that the statement mentions no coarser writing; or by
computing it again from the thirteenth seed's own exploration and comparing
with the ninth's on every result.

## What differs in the seed

One passage (`diff` against the ninth seed) is added after the four kinds:

"A coarser writing of an assertion forgets whether it was written with `r`
or with `s`. For every result, record also its coarser writing. Two results
that differ only in which relation wrote their assertions may be the same
coarser result."

Every other sentence is identical to the ninth seed (`diff`), and so to
the eighth with the seventh's empty beginning. The tenth seed's leftover
passage, the eleventh seed's colliding-writing passage, and the twelfth
seed's identification-record passage are not in this seed. The state stays
the ninth's (terms, a multiplicity for each ordered pair in `r` and in `s`,
no names); the beginning stays empty; the four kinds are the ninth's;
nothing is forbidden. What the ninth argued from the state and the four
kinds alone (the size as the cost, the has-a-term criterion, jointly free
results, the count by series, the exchange) must be re-examined with a
coarser writing that forgets the relation; what it argued from terms and
multiplicities without mentioning a writing of the relation carries over
through the identity on states.

The eighth and ninth already have two relations and an exchange of them;
they do not record a writing that forgets which relation asserted. The
task's question is when the coarser writing determines the finer one, when
two finer results that disagree in which relation wrote the assertion are
the same coarser result, whether the ninth's cost and reachability descend
to the coarser writing, and which of the ninth's results survive.

## Layout

- `research/thirteenth/` — reading notes (not evidence).
- `code/thirteenth/` — typed Python package for the thirteenth seed. Imported
  from the earlier packages what the coarser writing leaves intact: the
  two-relation state without names (`eighth.state.DState` with
  `names = None`, the ninth's empty beginning, `swap`, sameness,
  `canonical`), the four kinds, the list of changes and `perform`
  (`eighth.changes` / `ninth.changes`), the two-change cycle, the ninth's
  cost (the size), reachability (has a term), independent count
  (`ninth.orbits`), the ninth's exploration, sequence counts and
  comparisons with the seventh and the eighth, the statements tested
  (`ninth.follows`), the writers, `compare_evidence`, the Lean report
  runner. Defined afresh: the coarser writing (one multiplicity, the sum
  of `r` and `s`); when that writing determines the finer one; when two
  finer results are the same coarser result; whether a coarser collision
  of one pair constrains another; the unchosen reading that takes the
  coarser writing as the result, and the witnesses that it yields fewer
  results than the ninth; the comparison with the ninth (same results,
  rounds, shortest-sequence counts under the chosen reading). Earlier
  derivations' files are not modified except to correct a defect,
  recorded in the relevant change log.
- `tests/test_thirteenth_*.py` — tests of `code/thirteenth/`; all of `code/`
  stays at ≥ 95 % line and ≥ 95 % branch coverage, every
  `code/**/evidence.py` fully covered (an injection test for every
  differential check); `mypy --strict` passes; the prose watchlist stays
  clean.
- `lean4/Thirteenth/` — a thirteenth Lean library in the same Lake package
  (the lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Twelfth` (and through it `Ninth`).
  New: the coarser writing `coarse` (`NDSt → NSt`); the coarser writing
  of one state is the sum of the two projections (`coarse_eq_sum`);
  exchanging the relations keeps it (`coarse_swap`); it determines the
  finer one exactly when nothing is asserted (`determines_iff_nothing`);
  adding in `r` and adding in `s` land on the same coarser writing
  (`coarse_addAssertion_r_s`); `Step13` as `Step9`; `Reach13`; the
  identity maps `Step9.toStep13`, `Step13.toStep9`; the comparison with
  the ninth; the unchosen coarser result and the witnesses that its
  results are not the ninth's count.
- `evidence/thirteenth/` — written by `python code/generate_thirteenth.py`;
  the axiom report by `python code/lean_report_thirteenth.py`; `--check`
  regenerates into a temporary folder and compares.
- `paper/thirteenth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the thirteenth seed (`research/thirteenth/`)
Sentence-by-sentence diff against the ninth seed; the notion table with
source statuses; which readings change: C6 gains a clause (every result is
recorded also in a coarser writing that forgets whether an assertion was
written with `r` or with `s`; two results that differ only in which
relation wrote their assertions may be the same coarser result); C5⁗
unchanged (the four kinds); C2, C4, C8′ unchanged in kind. New chosen
reading C-C1: the coarser writing of a two-relation state is the
one-relation state whose multiplicity at each pair is the sum of the `r`
and `s` multiplicities (a seventh state); it is computed from the result,
recorded as extra data, not a third multiplicity beside `r` and `s`; a
result remains a two-relation state up to sameness. New unchosen reading
C-C2, kept: the result *is* the coarser writing (two finer states with
the same sum are one result). Expected consequences to be proved or
refuted: the coarser writing determines the finer one exactly when
nothing is asserted; `0 r 1` and `0 s 1` are different finer results and
the same coarser result; adding in `r` and adding in `s` land on the
same coarser writing; a coarser collision on one pair does not force a
collision on another; under C-C1 the ninth's cost, has-a-term criterion,
jointly free results and non-product count survive; under C-C2 the cost
and the has-a-term criterion descend (the size and the terms are the
same) while the count of results and jointly-free-as-a-product do not
(the quotient identifies splits of the same sum).

### Phase 2 — `code/thirteenth/` and `tests/`
- coarser writings; determination; same coarser result; exploration
  reusing the ninth's with the coarser writing filled on every result;
  full logs at a small bound;
- every explored result checked: the coarser writing is the sum; swap
  keeps it; it determines the finer one iff nothing is asserted; some
  pair of finer results share a coarser writing and differ in which
  relation wrote the assertion;
- the thirteenth exploration compared with the ninth's at the same bound
  and rounds: the results, rounds and shortest-sequence counts must be
  the ninth's (the computed form of the citation under C-C1);
- the unchosen coarser reading explored at a small bound: fewer results
  than the ninth's (same sum, different splits);
- reachability, independent count, two-term closed form reused from the
  ninth and re-checked;
- property witnesses for "what does not follow", including coarser
  statements;
- deterministic evidence writer with `--check`; Lean axiom-report writer
  for `lean4/Thirteenth/Axioms.lean`.

### Phase 3 — `lean4/Thirteenth/`
Targets, in order:
1. `coarse`, `determines`; the coarser writing is the sum of the two
   projections (`coarse_eq_sum`); exchanging the relations keeps it
   (`coarse_swap`); `Step13` as `Step9`; `Reach13` as `Reach9`;
   `Step9.toStep13`, `Step13.toStep9`; well-formedness, at least one
   term, the empty state, the first change, inherited through the
   identity (cited, re-checked).
2. The coarser writing determines the finer one when nothing is
   asserted (`determines_of_nothing`) and fails on `0 r 1`
   (`not_determines_twoBetween`); adding in `r` and adding in `s` land
   on the same coarser writing (`coarse_addAssertion_r_s`); the coarser
   writing is not a multiplicity of a third relation
   (`coarse_not_assertion`); the size descends (`size_coarse`).
3. What survives (`Thirteenth/Compare.lean`): the ninth's results, cost
   (`fewest_changes13`), reachability (`reach13_iff`), jointly free
   results (`results_pair13`) and the identity on states (`toNDSt`); the
   coarser writing is not a third relation (`no_third_rel`); a coarser
   collision of one pair does not constrain the other
   (`no_cross_constraint`); the unchosen coarser tag has results the
   ninth's count has not (`coarse_extra`: two finer, one coarser).
4. `Step13.swap`, `coarse_swap` (exchange carries coarser writings with
   the relations). Attempted once; if a step does not close it is proved
   in the paper and marked "not in Lean".
`#print axioms` for every theorem the thirteenth paper cites, into
`evidence/thirteenth/lean_axioms.txt`.

### Phase 4 — `evidence/thirteenth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The twelve earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/thirteenth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives a coarser writing that forgets the
relation; a section answering the task's question: when the coarser
writing determines the finer one, when two finer results are the same
coarser result, whether the ninth's cost and reachability descend, and
which of the ninth's results and count survive; final section: nearest
known results and differences — the only place where outside names
appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, push, pull request.

## Stopping conditions (thirteenth derivation)

The run stops when AE1–AE9 hold, or when a blocker is hit.

- AE1 Every notion in `paper/thirteenth/paper.md` has one recorded source
  status.
- AE2 Every claim in `paper/thirteenth/claim_ledger.md` has evidence, or is
  open.
- AE3 Every alternative is kept, or eliminated by a cited proof.
- AE4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch coverage over all of `code/` and
  every evidence module fully covered; `python -m mypy` passes.
- AE5 `lake build` (pinned toolchain, inside `lean4/`) passes for all
  thirteen libraries; no `sorry`, `admit`, or declared axiom in `lean4/`;
  all thirteen axiom reports regenerated and committed.
- AE6 `evidence/thirteenth/` regenerates byte-identically (`--check`); the
  earlier derivations' evidence still regenerates byte-identically.
- AE7 Every use of an earlier result in the thirteenth paper is cited and
  re-checked, with the re-check saying whether it survives a coarser
  writing that forgets which relation asserted (ledger column "re-check").
- AE8 The prose watchlist passes on the tracked tree; every pinned hit of
  the thirteenth paper is in its final section.
- AE9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and on rounds together, as the ninth's, since under
  C-C1 the results of round `r` are the ninth's. Targets: 3 terms with 6
  rounds, 3 terms with 5, 2 terms with 8, full attempt logs at 2 terms
  and 3 rounds; the unchosen coarser reading at 2 terms with 5 rounds
  (coarser writings of the ninth's states). Any run that does not
  complete in minutes here has its rounds lowered first, then its terms;
  the bounds used are declared in the paper; the frontier is exported
  exactly; completeness within the bound is certified by the ninth's
  independent count (C-C1) and by a coarser count (C-C2).
- Rounds: at most 100; no change is invented.
- Lean targets 1–3 required; target 4 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `worktree-thirteenth-derivation`, made from the twelfth's last
  commit; the pull request is opened against
  `worktree-twelfth-derivation` if that branch is not yet on `main`,
  otherwise against `main`.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The
checkout's `lean4/.lake/packages` is the pinned packages of this same
repository (checked before Phase 0; no download happens).

## How to run (thirteenth derivation)

From the repository root:
- `python -m pytest` (all tests, thirteen derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_thirteenth.py` writes `evidence/thirteenth/`;
  `python code/generate_thirteenth.py --check` compares with a fresh
  regeneration;
- `python code/lean_report_thirteenth.py` builds `lean4/` and writes
  `evidence/thirteenth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Fourteenth derivation (`prompt/fourteenth/`) — plan and stopping conditions

Written before any other work of the fourteenth derivation, as
`prompt/fourteenth/prompt.md` requires. Inputs: `prompt/fourteenth/prompt.md` and
`prompt/fourteenth/seed_prompt.md`; the thirteen earlier derivations (`paper/`,
`paper/second/` … `paper/thirteenth/`, `code/xry/` … `code/thirteenth/`,
`lean4/H3V7N5QF/` … `lean4/Thirteenth/`, `evidence/` … `evidence/thirteenth/`)
are cited where used, never assumed. Everything above stays in force
(isolation, no network, `prompt/` untouched, `.lake/` never committed,
bookkeeping rules 1–4, the evidence-module coverage gate). Rule 5 of the
fourteenth task: every result of an earlier derivation that is used is cited
and its proof re-checked from the fourteenth seed, and the re-check says
whether the result survives once a leftover is a writing that is not an
assertion — in particular whether the ninth's jointly free results and
size-as-cost survive. In Lean the re-check is by the identity on the ninth's
states (`NDSt`) and the identity on the ninth's changes (`Step9` as
`Step14`): leftover is a writing of the change, recorded with the change,
neither `xry` nor `xsy`, and is not a third multiplicity beside `r` and `s`;
every change of the ninth is a change of the fourteenth and conversely. The
unchosen reading that puts the leftover writing into the result as a field
is kept and computed separately. Or by observing that the statement mentions
no leftover; or by computing it again from the fourteenth seed's own
exploration and comparing with the ninth's on every result.

## What differs in the seed

One passage (`diff` against the ninth seed) is added after the four kinds:

"After every change, record what that change leaves. A leftover is written
neither `xry` nor `xsy`. A leftover is not an assertion and is not an
answer."

Every other sentence is identical to the ninth seed (`diff`), and so to the
eighth with the seventh's empty beginning. The tenth seed's three-outcome
grading, the eleventh seed's colliding-writing passage, the twelfth seed's
identification-record passage, and the thirteenth seed's coarser-writing
passage are not in this seed. The state stays the ninth's (terms, a
multiplicity for each ordered pair in `r` and in `s`, no names); the
beginning stays empty; the four kinds are the ninth's; nothing is forbidden.
What the ninth argued from the state and the four kinds alone (the size as
the cost, the has-a-term criterion, jointly free results, the count by
series, the exchange) must be re-examined with a leftover that is a third
kind of writing; what it argued from terms and multiplicities without
mentioning leftover carries over through the identity on states.

The tenth seed, if run, grades leftovers as three outcomes of the four kinds
of change. Here the leftover is a third kind of writing, not an assertion of
either relation, and it is not an answer to a change. The task's question is
whether a leftover can be identified with an assertion of `r` or of `s`,
whether clearing it is one of the four kinds, whether a leftover of one
relation is a leftover of the other, and which of the ninth's results
survive once a leftover is not an answer.

## Layout

- `research/fourteenth/` — reading notes (not evidence).
- `code/fourteenth/` — typed Python package for the fourteenth seed. Imported
  from the earlier packages what leftover-as-writing leaves intact: the
  two-relation state without names (`eighth.state.DState` with
  `names = None`, the ninth's empty beginning, `swap`, sameness,
  `canonical`), the four kinds, the list of changes and `perform`
  (`eighth.changes` / `ninth.changes`), the two-change cycle, the ninth's
  cost (the size), reachability (has a term), independent count
  (`ninth.orbits`), the ninth's exploration, sequence counts and
  comparisons with the seventh and the eighth, the statements tested
  (`ninth.follows`), the writers, `compare_evidence`, the Lean report
  runner. Defined afresh: the leftover writing (neither `xry` nor `xsy`);
  whether that writing is an assertion of `r` or of `s`; whether clearing
  it is one of the four kinds; whether leftover of a removal in one
  relation is leftover of a removal in the other (same pair, no relation
  in the writing); the unchosen reading that tags a result with the
  leftover writing, and the witnesses that it yields results the ninth
  does not; the comparison with the ninth (same results, rounds,
  shortest-sequence counts under the chosen reading). Earlier
  derivations' files are not modified except to correct a defect,
  recorded in the relevant change log.
- `tests/test_fourteenth_*.py` — tests of `code/fourteenth/`; all of `code/`
  stays at ≥ 95 % line and ≥ 95 % branch coverage, every
  `code/**/evidence.py` fully covered (an injection test for every
  differential check); `mypy --strict` passes; the prose watchlist stays
  clean.
- `lean4/Fourteenth/` — a fourteenth Lean library in the same Lake package
  (the lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Thirteenth` (and through it `Ninth`).
  New: the leftover writing `LeftWriting` / `leftover`; leftover of a
  removal ignores the relation (`leftover_remove_r_s`); leftover is not
  an assertion (`leftover_not_assertion`); leftover is not an answer;
  clearing leftover is not one of the four kinds; `Step14` as `Step9`;
  `Reach14`; the identity maps `Step9.toStep14`, `Step14.toStep9`; the
  comparison with the ninth; the unchosen tagged state `Tagged` and the
  witnesses that its results are not the ninth's.
- `evidence/fourteenth/` — written by `python code/generate_fourteenth.py`;
  the axiom report by `python code/lean_report_fourteenth.py`; `--check`
  regenerates into a temporary folder and compares.
- `paper/fourteenth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the fourteenth seed (`research/fourteenth/`)
Sentence-by-sentence diff against the ninth seed; the notion table with
source statuses; which readings change: C6 gains a clause (after every
change, record what that change leaves as a leftover writing neither
`xry` nor `xsy`; leftover is not an assertion and is not an answer); C5⁗
unchanged (the four kinds; leftover is not a fifth kind); C2, C4, C8′
unchanged in kind. New chosen reading C-F1: leftover is a writing of the
change, computed from the start and the change (additions write nothing;
a removal writes the pair with a third letter `ℓ`, not `r` or `s`; an
identification writes the two terms with `∼`, not an assertion); it is
kept with the result of that change as extra data on the attempt, not as
a third multiplicity beside `r` and `s`; a result remains a two-relation
state up to sameness. New unchosen reading C-F2, kept: the leftover
writing is a field of the result, replaced by each later change. Expected
consequences to be proved or refuted: leftover cannot be identified with
an assertion of `r` or of `s` (it is written neither `xry` nor `xsy` and
is not an assertion); clearing leftover is not one of the four kinds
(leftover is not a term and not an assertion; leftover is not an answer;
nothing else is a change); leftover of a removal in `r` of a pair is the
same leftover writing as leftover of a removal in `s` of that pair (the
writing names no relation); under C-F1 the ninth's cost, has-a-term
criterion, jointly free results and non-product count survive; under C-F2
they do not as a count of results (same underlying state, different
leftover writings).

### Phase 2 — `code/fourteenth/` and `tests/`
- leftover writings; not an assertion of `r` or of `s`; not an answer;
  not a kind of change; leftover of one relation is leftover of the
  other as writings of the same pair; exploration reusing the ninth's
  with leftover filled on every change; full logs at a small bound;
- every change within the bound checked: leftover is written neither
  `xry` nor `xsy`; leftover of `r`-removal equals leftover of
  `s`-removal of the same pair; additions write nothing; identifications
  write a merge, not an assertion;
- the fourteenth exploration compared with the ninth's at the same bound
  and rounds: the results, rounds and shortest-sequence counts must be
  the ninth's (the computed form of the citation under C-F1);
- the unchosen tagged reading explored at a small bound: more results
  than the ninth's (same state, different leftover writings);
- reachability, independent count, two-term closed form reused from the
  ninth and re-checked;
- property witnesses for "what does not follow", including leftover
  statements;
- deterministic evidence writer with `--check`; Lean axiom-report writer
  for `lean4/Fourteenth/Axioms.lean`.

### Phase 3 — `lean4/Fourteenth/`
Targets, in order:
1. `LeftWriting`, `leftover`; leftover of a removal is the pair, ignoring
   the relation (`leftover_remove`, `leftover_remove_r_s`); `Step14` as
   `Step9`; `Reach14` as `Reach9`; `Step9.toStep14`, `Step14.toStep9`;
   well-formedness, at least one term, the empty state, the first change,
   inherited through the identity (cited, re-checked).
2. Leftover is not an assertion (`leftover_not_assertion`); leftover of
   `r` and of `s` on the same pair agree (`r_leftover_is_s`); leftover is
   not an answer; clearing leftover is not one of the four kinds
   (`clearing_not_a_kind`); leftover is not a multiplicity
   (`leftover_not_in_M`).
3. What survives (`Fourteenth/Compare.lean`): the ninth's results, cost
   (`fewest_changes14`), reachability (`reach14_iff`), jointly free
   results (`results_pair14`) and the identity on states (`toNDSt`);
   leftover is not a third relation (`no_third_rel`); leftover of one
   relation does not constrain the other (`no_cross_constraint`); the
   unchosen tagged tag (`Tagged`) has results the ninth has not
   (`tagged_extra`).
4. `Step14.swap`, leftover of a swapped removal (exchange carries leftover
   writings with the pairs, not the relations). Attempted once; if a step
   does not close it is proved in the paper and marked "not in Lean".
`#print axioms` for every theorem the fourteenth paper cites, into
`evidence/fourteenth/lean_axioms.txt`.

### Phase 4 — `evidence/fourteenth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The thirteen earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/fourteenth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives a leftover that is a writing and not an
assertion; a section answering the task's question: whether leftover can
be identified with an assertion of `r` or of `s`, whether clearing it is
one of the four kinds, whether leftover of one relation is leftover of
the other, and which of the ninth's cost, reachability, results and count
survive; final section: nearest known results and differences — the only
place where outside names appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, push, pull request.

## Stopping conditions (fourteenth derivation)

The run stops when AF1–AF9 hold, or when a blocker is hit.

- AF1 Every notion in `paper/fourteenth/paper.md` has one recorded source
  status.
- AF2 Every claim in `paper/fourteenth/claim_ledger.md` has evidence, or is
  open.
- AF3 Every alternative is kept, or eliminated by a cited proof.
- AF4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch coverage over all of `code/` and
  every evidence module fully covered; `python -m mypy` passes.
- AF5 `lake build` (pinned toolchain, inside `lean4/`) passes for all
  fourteen libraries; no `sorry`, `admit`, or declared axiom in `lean4/`;
  all fourteen axiom reports regenerated and committed.
- AF6 `evidence/fourteenth/` regenerates byte-identically (`--check`); the
  earlier derivations' evidence still regenerates byte-identically.
- AF7 Every use of an earlier result in the fourteenth paper is cited and
  re-checked, with the re-check saying whether it survives a leftover
  that is a writing and not an assertion (ledger column "re-check").
- AF8 The prose watchlist passes on the tracked tree; every pinned hit of
  the fourteenth paper is in its final section.
- AF9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and on rounds together, as the ninth's, since under
  C-F1 the results of round `r` are the ninth's. Targets: 3 terms with 6
  rounds, 3 terms with 5, 2 terms with 8, full attempt logs at 2 terms
  and 3 rounds; the unchosen tagged reading at 2 terms with 5 rounds
  (leftover writings on the ninth's states). Any run that does not
  complete in minutes here has its rounds lowered first, then its terms;
  the bounds used are declared in the paper; the frontier is exported
  exactly; completeness within the bound is certified by the ninth's
  independent count (C-F1) and by a tagged count (C-F2).
- Rounds: at most 100; no change is invented.
- Lean targets 1–3 required; target 4 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `worktree-fourteenth-derivation`, made from the thirteenth's last
  commit; the pull request is opened against
  `worktree-thirteenth-derivation` if that branch is not yet on `main`,
  otherwise against `main`.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The
checkout's `lean4/.lake/packages` is the pinned packages of this same
repository (checked before Phase 0; no download happens).

## How to run (fourteenth derivation)

From the repository root:
- `python -m pytest` (all tests, fourteen derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_fourteenth.py` writes `evidence/fourteenth/`;
  `python code/generate_fourteenth.py --check` compares with a fresh
  regeneration;
- `python code/lean_report_fourteenth.py` builds `lean4/` and writes
  `evidence/fourteenth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Fifteenth derivation (`prompt/fifteenth/`) — plan and stopping conditions

Written before any other work of the fifteenth derivation, as
`prompt/fifteenth/prompt.md` requires. Inputs: `prompt/fifteenth/prompt.md` and
`prompt/fifteenth/seed_prompt.md`; the fourteen earlier derivations (`paper/`,
`paper/second/` … `paper/fourteenth/`, `code/xry/` … `code/fourteenth/`,
`lean4/H3V7N5QF/` … `lean4/Fourteenth/`, `evidence/` … `evidence/fourteenth/`)
are cited where used, never assumed. Everything above stays in force
(isolation, no network, `prompt/` untouched, `.lake/` never committed,
bookkeeping rules 1–4, the evidence-module coverage gate). Rule 5 of the
fifteenth task: every result of an earlier derivation that is used is cited
and its proof re-checked from the fifteenth seed, and the re-check says
whether the result survives once a reached result is not thereby admitted —
in particular whether the ninth's jointly free results, size-as-cost, and
has-a-term reachability survive. In Lean the re-check is by the identity on
the ninth's states (`NDSt`) and the identity on the ninth's changes (`Step9`
as `Step15`): admission is a record of a result, neither `xry` nor `xsy`,
and is not a third multiplicity beside `r` and `s`; every change of the
ninth is a change of the fifteenth and conversely. The unchosen reading that
puts the admission record into the result as a field is kept and computed
separately. Or by observing that the statement mentions no admission; or by
computing it again from the fifteenth seed's own exploration and comparing
with the ninth's on every result.

## What differs in the seed

One passage (`diff` against the ninth seed) is added after the four kinds:

"A result of the changes is reached. Whether it is admitted is not given by
the reaching. Record for every result whether it is admitted. Reaching a
result does not make it admitted."

Every other sentence is identical to the ninth seed (`diff`), and so to the
eighth with the seventh's empty beginning. The tenth seed's leftover
passage, the eleventh seed's colliding-writing passage, the twelfth seed's
identification-record passage, the thirteenth seed's coarser-writing
passage, and the fourteenth seed's leftover-as-writing passage are not in
this seed. The state stays the ninth's (terms, a multiplicity for each
ordered pair in `r` and in `s`, no names); the beginning stays empty; the
four kinds are the ninth's; nothing is forbidden. What the ninth argued from
the state and the four kinds alone (the size as the cost, the has-a-term
criterion, jointly free results, the count by series, the exchange) must be
re-examined with an admission record that reaching does not give; what it
argued from terms and multiplicities without mentioning admission carries
over through the identity on states.

The ninth treated every well-formed two-relation state as a result. The
first seed recorded a refused change and changed nothing; it did not
separate reaching from admitting. The task's question is whether admission
is independent of the two relations, whether every reached result can be
admitted, whether an admitted result in one relation constrains the other,
and which of the ninth's results survive once reaching does not admit.

## Layout

- `research/fifteenth/` — reading notes (not evidence).
- `code/fifteenth/` — typed Python package for the fifteenth seed. Imported
  from the earlier packages what admission-not-given-by-reaching leaves
  intact: the two-relation state without names (`eighth.state.DState` with
  `names = None`, the ninth's empty beginning, `swap`, sameness,
  `canonical`), the four kinds, the list of changes and `perform`
  (`eighth.changes` / `ninth.changes`), the two-change cycle, the ninth's
  cost (the size), reachability (has a term), independent count
  (`ninth.orbits`), the ninth's exploration, sequence counts and
  comparisons with the seventh and the eighth, the statements tested
  (`ninth.follows`), the writers, `compare_evidence`, the Lean report
  runner. Defined afresh: the admission record (neither `xry` nor `xsy`);
  whether that record is an assertion of `r` or of `s`; whether admitting
  is one of the four kinds; whether admission of a result in one relation
  constrains the other; whether every reached result can be admitted; the
  unchosen reading that tags a result with the admission record, and the
  witnesses that it yields results the ninth does not; the comparison with
  the ninth (same results, rounds, shortest-sequence counts under the
  chosen reading). Earlier derivations' files are not modified except to
  correct a defect, recorded in the relevant change log.
- `tests/test_fifteenth_*.py` — tests of `code/fifteenth/`; all of `code/`
  stays at ≥ 95 % line and ≥ 95 % branch coverage, every
  `code/**/evidence.py` fully covered (an injection test for every
  differential check); `mypy --strict` passes; the prose watchlist stays
  clean.
- `lean4/Fifteenth/` — a fifteenth Lean library in the same Lake package
  (the lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Fourteenth` (and through it `Ninth`).
  New: the admission record `Admission` / `admitted`; reaching does not
  admit (`reaching_does_not_admit`); every reached result can be admitted
  (`every_reached_can_be_admitted`); admission is not an assertion
  (`admission_not_assertion`); admission is not a change of the four kinds;
  `Step15` as `Step9`; `Reach15`; the identity maps `Step9.toStep15`,
  `Step15.toStep9`; the comparison with the ninth; the unchosen tagged
  state `Tagged` and the witnesses that its results are not the ninth's.
- `evidence/fifteenth/` — written by `python code/generate_fifteenth.py`;
  the axiom report by `python code/lean_report_fifteenth.py`; `--check`
  regenerates into a temporary folder and compares.
- `paper/fifteenth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the fifteenth seed (`research/fifteenth/`)
Sentence-by-sentence diff against the ninth seed; the notion table with
source statuses; which readings change: C6 gains a clause (a result of the
changes is reached; whether it is admitted is not given by the reaching;
record for every result whether it is admitted; reaching a result does not
make it admitted); C5⁗ unchanged (the four kinds; admitting is not a fifth
kind); C2, C4, C8′ unchanged in kind. New chosen reading C-A1: admission is
a record of a result, computed independently of the path that reached it
(reaching leaves the record as not-admitted; every reached result can be
admitted by a record that is not a change of the four kinds); it is kept
with the result as extra data, not as a third multiplicity beside `r` and
`s`; a result remains a two-relation state up to sameness. New unchosen
reading C-A2, kept: the admission record is a field of the result, so the
unadmitted and admitted copies of one ninth state are different results.
Expected consequences to be proved or refuted: admission is independent of
the two relations (it is not an assertion of `r` or of `s` and names no
relation); every reached result can be admitted (the record is available
for every well-formed two-relation state); an admitted result does not
constrain the other relation (admission is of the result, not of a
projection); under C-A1 the ninth's cost, has-a-term criterion, jointly
free results and non-product count survive; under C-A2 they do not as a
count of results (same underlying state, different admission records).

### Phase 2 — `code/fifteenth/` and `tests/`
- admission records; not an assertion of `r` or of `s`; not a kind of
  change; reaching does not admit; every reached result can be admitted;
  admission of one relation does not constrain the other; exploration
  reusing the ninth's with admission filled on every result; full logs at
  a small bound;
- every result within the bound checked: reaching leaves not-admitted;
  every reached result can be admitted; admission is written neither
  `xry` nor `xsy`; admission of a result with something in `r` only and
  something in `s` only is the same record;
- the fifteenth exploration compared with the ninth's at the same bound
  and rounds: the results, rounds and shortest-sequence counts must be
  the ninth's (the computed form of the citation under C-A1);
- the unchosen tagged reading explored at a small bound: more results
  than the ninth's (same state, admitted and not);
- reachability, independent count, two-term closed form reused from the
  ninth and re-checked;
- property witnesses for "what does not follow", including admission
  statements;
- deterministic evidence writer with `--check`; Lean axiom-report writer
  for `lean4/Fifteenth/Axioms.lean`.

### Phase 3 — `lean4/Fifteenth/`
Targets, in order:
1. `Admission`, `admitted`; reaching a result does not admit
   (`reaching_does_not_admit`); `Step15` as `Step9`; `Reach15` as
   `Reach9`; `Step9.toStep15`, `Step15.toStep9`; well-formedness, at
   least one term, the empty state, the first change, inherited through
   the identity (cited, re-checked).
2. Admission is not an assertion (`admission_not_assertion`); admission
   of `r` and of `s` on one result agree (`r_admission_is_s`); admission
   is not one of the four kinds (`admission_not_a_kind`); every reached
   result can be admitted (`every_reached_can_be_admitted`); admission is
   not a multiplicity (`admission_not_in_M`).
3. What survives (`Fifteenth/Compare.lean`): the ninth's results, cost
   (`fewest_changes15`), reachability (`reach15_iff`), jointly free
   results (`results_pair15`) and the identity on states (`toNDSt`);
   admission is not a third relation (`no_third_rel`); admission of one
   relation does not constrain the other (`no_cross_constraint`); the
   unchosen tagged tag (`Tagged`) has results the ninth has not
   (`tagged_extra`).
4. `Step15.swap`, admission of a swapped result (exchange keeps the
   admission record; it names no relation). Attempted once; if a step
   does not close it is proved in the paper and marked "not in Lean".
`#print axioms` for every theorem the fifteenth paper cites, into
`evidence/fifteenth/lean_axioms.txt`.

### Phase 4 — `evidence/fifteenth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The fourteen earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/fifteenth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives a reached result not thereby admitted; a
section answering the task's question: whether admission is independent of
the two relations, whether every reached result can be admitted, whether
an admitted result in one relation constrains the other, and which of the
ninth's cost, reachability, results and count survive; final section:
nearest known results and differences — the only place where outside names
appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, push, pull request.

## Stopping conditions (fifteenth derivation)

The run stops when AG1–AG9 hold, or when a blocker is hit.

- AG1 Every notion in `paper/fifteenth/paper.md` has one recorded source
  status.
- AG2 Every claim in `paper/fifteenth/claim_ledger.md` has evidence, or is
  open.
- AG3 Every alternative is kept, or eliminated by a cited proof.
- AG4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch coverage over all of `code/` and
  every evidence module fully covered; `python -m mypy` passes.
- AG5 `lake build` (pinned toolchain, inside `lean4/`) passes for all
  fifteen libraries; no `sorry`, `admit`, or declared axiom in `lean4/`;
  all fifteen axiom reports regenerated and committed.
- AG6 `evidence/fifteenth/` regenerates byte-identically (`--check`); the
  earlier derivations' evidence still regenerates byte-identically.
- AG7 Every use of an earlier result in the fifteenth paper is cited and
  re-checked, with the re-check saying whether it survives a reached
  result not thereby admitted (ledger column "re-check").
- AG8 The prose watchlist passes on the tracked tree; every pinned hit of
  the fifteenth paper is in its final section.
- AG9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and on rounds together, as the ninth's, since under
  C-A1 the results of round `r` are the ninth's. Targets: 3 terms with 6
  rounds, 3 terms with 5, 2 terms with 8, full attempt logs at 2 terms
  and 3 rounds; the unchosen tagged reading at 2 terms with 5 rounds
  (admission records on the ninth's states). Any run that does not
  complete in minutes here has its rounds lowered first, then its terms;
  the bounds used are declared in the paper; the frontier is exported
  exactly; completeness within the bound is certified by the ninth's
  independent count (C-A1) and by a tagged count (C-A2).
- Rounds: at most 100; no change is invented.
- Lean targets 1–3 required; target 4 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `worktree-fifteenth-derivation`, made from the fourteenth's last
  commit; the pull request is opened against
  `worktree-fourteenth-derivation` if that branch is not yet on `main`,
  otherwise against `main`.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The
checkout's `lean4/.lake/packages` is the pinned packages of this same
repository (checked before Phase 0; no download happens).

## How to run (fifteenth derivation)

From the repository root:
- `python -m pytest` (all tests, fifteen derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`, and
  `python ci/check_prose_watchlist.py`;
- `python code/generate_fifteenth.py` writes `evidence/fifteenth/`;
  `python code/generate_fifteenth.py --check` compares with a fresh
  regeneration;
- `python code/lean_report_fifteenth.py` builds `lean4/` and writes
  `evidence/fifteenth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Sixteenth derivation (`prompt/sixteenth/`) — plan and stopping conditions

Written before any other work of the sixteenth derivation, as
`prompt/sixteenth/prompt.md` requires. Inputs: `prompt/sixteenth/prompt.md`
and `prompt/sixteenth/seed_prompt.md`; the fifteen earlier derivations
(`paper/`, `paper/second/` … `paper/fifteenth/`, `code/xry/` …
`code/fifteenth/`, `lean4/H3V7N5QF/` … `lean4/Fifteenth/`, `evidence/` …
`evidence/fifteenth/`) are cited where used, never assumed. Everything above
stays in force (isolation, no network, `prompt/` untouched, `.lake/` never
committed, bookkeeping rules 1–4, the evidence-module coverage gate, and now
the three `ci/` gates of `ci/OEWAS_GATES.md`). Rule 5 of the sixteenth task:
every result of an earlier derivation that is used is cited and its proof
re-checked from the sixteenth seed, and the re-check says whether the result
survives once the record feeds back into the state. In Lean the re-check is
through two maps: the *projection* of a sixteenth state to a ninth state
(`RSt.toNDSt`: the terms and the two multiplicity functions, the record
forgotten) and the *embedding* of a ninth state as a sixteenth state with an
empty record (`NDSt.ofNDSt`). Every change of the sixteenth projects to a
change of the ninth (an admission projects to an addition of an assertion);
every addition and identification of the ninth is a change of the sixteenth
on the embedded states, and a removal of the ninth is a change of the
sixteenth whose outcome carries one recorded leftover — the embedding is
*not* a map of changes on removals, and that is the whole difference. Or by
observing that the statement mentions no record; or by computing it again
from the sixteenth's own exploration and comparing with the ninth's on the
results with an empty record. A claim of the tenth to fifteenth that held
*by construction* because the record sat off the result is re-examined here
and downgraded to chosen / by construction, refuted with a witness, or
re-proved, as the evidence requires.

## What differs in the seed

One sentence (`diff` against the fourteenth seed): "A leftover is not an
assertion and is not an answer." becomes

"A recorded leftover `xℓy` may be admitted, adding the assertion `xry` or
the assertion `xsy`; an unadmitted leftover is not an assertion."

Every other sentence is identical to the fourteenth seed (`diff`), and so to
the ninth with the record passage. The state can no longer be the ninth's:
a recorded leftover may later be admitted, so the unadmitted leftovers must
be carried by the state (a leftover recorded off the result could not feed
back). The fourteenth's leftover *writing* survives (additions leave
nothing; a removal leaves the pair written `xℓy`; an identification leaves
the merge writing); what changes is where the pair writing lives and what
it can do.

## Readings

- **C-R1 (chosen).** A state is a ninth state together with its *record*:
  for every ordered pair of its terms, how many leftovers `xℓy` are recorded
  and not admitted (a count, since each removal records one leftover and
  "record what that change leaves" is said of every change). A removal of
  `xqy` (`q` either relation) lowers the multiplicity by one and raises the
  record of `(x, y)` by one. An *admission* of a recorded `xℓy` into `q`
  raises the multiplicity of `xqy` by one and lowers the record of `(x, y)`
  by one; it is a change — the kind "adding an assertion", performed by
  admitting rather than directly — and it leaves nothing. The leftover
  names no relation, so a leftover left by a removal in `r` may be admitted
  into `s`. An identification replaces both terms by one in the record as
  in every assertion (the record of the merged pairs adds up). The merge
  writing of an identification is recorded on the change, as under the
  fourteenth's C-F1, and is not admissible: it is not written `xℓy`. Two
  results are the same when a rewriting of the terms carries the two
  relations *and* the record of one onto the other. The attempt order is
  fewest additions first: identifications, removals in `r`, in `s`, a term,
  the direct additions in `r`, in `s`, then the admissions in `r`, in `s`
  (an admission adds an assertion; it is listed after the direct additions).
- **C-R2 (unchosen, kept, computed).** The record is a set: a leftover of a
  pair is recorded or not, and a second removal of the same pair records
  nothing new. Explored at a small bound; its count and its cost compared.
- **C-R3 (unchosen, kept, computed).** An identification drops the
  leftovers naming either merged term instead of carrying them to the
  surviving term. Explored at a small bound; compared.
- **Set aside, with the sentence that refuses each:** *admission is not a
  change* (it adds the assertion `xry`, and adding an assertion is one of
  the four kinds); *an admitted leftover stays recorded and may be admitted
  again* (an unadmitted leftover is not an assertion, so an admitted one is
  the assertion it added; a second admission would add an assertion from no
  leftover); *the merge writing is part of the result* (the fourteenth's
  C-F2, cited: it multiplies results without changing what any change can
  do, since it can never be admitted; not recomputed).

## Expected consequences, to be proved or refuted

1. **Same relation.** Removing `xqy` and then admitting `xℓy` into `q` is
   the identity on the state, record included (Lean, computed on every
   removal within the bound).
2. **Other relation.** Removing `xqy` and then admitting `xℓy` into the
   other relation is a result different from the start (the `q` total
   falls, the other rises, and no rewriting changes a total) and different
   from removing then adding directly (the record differs by one leftover);
   its ninth state is reachable from the empty beginning by additions alone,
   so no *ninth* state is new — what is new is the pairing of a state with
   an emptier record.
3. **Termination.** The feedback does not terminate: remove then admit is a
   two-change cycle at every state with an assertion, and the record is
   unbounded (add, remove, add, remove, …). A finite bound on terms and on
   rounds is declared, the frontier exported, completeness within it
   certified by an independent count.
4. **Cost.** The potential `size + 2·record` (size the ninth's; record the
   number of unadmitted leftovers) rises by exactly one on an addition and
   on a removal and falls by exactly one on an admission and on an
   identification, so the fewest changes from the empty beginning to a
   result is exactly its potential, and no shortest sequence admits or
   identifies: an assertion that arrives by admission costs three changes
   (add, remove, admit) where a direct addition costs one. Between results
   an admission can be the only route (the identity pair of item 1).
5. **Mass.** The sum of both totals and the record never falls along a
   change (a removal moves one unit into the record, an admission moves it
   back, an identification merges, additions raise), nor does its diagonal
   part; so the ninth's has-a-term criterion fails — the one-term state
   asserting `ara` once never returns to the one-term state asserting
   nothing — and reachability among the results with a term is one-way
   along the mass again (Lean: the two invariants and the witness).
6. **Reachability criterion (computed; partly in Lean).** A result reaches
   another exactly when the first is empty, or there is a map of the terms
   of the first into the terms of the second under which every pair of the
   second receives at most its own mass. Checked against breadth-first
   search on every ordered pair of results within a small bound; necessity
   of the two mass invariants and sufficiency with the same terms in Lean.
7. **Results and count.** Every well-formed state (a ninth state with any
   record over its terms) is a result; the ninth's results are exactly the
   results with an empty record, at the same rounds; the count by (terms,
   potential) is the orbit count with a third factor `1 / (1 − x^{2L})` per
   cycle of pairs beside the two `1 / (1 − x^L)` factors; the one-term
   results of round `k ≥ 1` number `(⌊(k−1)/2⌋ + 1)·(⌈(k−1)/2⌉ + 1)`.
8. **What survives.** The ninth's cost survives on the results with an empty
   record and fails off them; the has-a-term criterion fails; jointly free
   results survive with any record; the count survives as the count of the
   empty-record results; the two-change cycle survives (a term added and
   identified away; remove then admit) but the ninth's add-then-remove is no
   longer a cycle — it leaves a leftover; the fourteenth's "leftover is not
   an assertion" survives as "an *unadmitted* leftover is not an assertion";
   "leftover of `r` is leftover of `s`" survives and now has force (it is
   what admits an `r` leftover into `s`); "clearing leftover is not one of
   the four kinds" fails — an admission clears a leftover and is adding an
   assertion; "leftover is not a third multiplicity" is re-examined: the
   record is a count per pair kept in the state, but it is not asserted, is
   not raised by an addition, and is not a third relation.

## Layout

- `research/sixteenth/` — reading notes (not evidence).
- `code/sixteenth/` — typed Python package for the sixteenth seed. Imported
  from the earlier packages what the feedback leaves intact: the ninth's
  two-relation state, `perform` of the four kinds on it, `changes`, `Kind`,
  `canonical`, `rewrite`, `swap` (`ninth.state`, `ninth.changes`,
  `eighth.state`), the fourteenth's leftover writings (`fourteenth.leftover`:
  `LeftWriting`, `leftover_of`, `leftover_pair`, `leftover_nothing`,
  `leftover_merge`), the cycle machinery and the series of the orbit counts
  (`xry.orbits`, `fourth.orbits.series`, `sixth.orbits.diag_cycles`), the
  ninth's exploration, orbit count and criterion for the comparison, the
  writers, `compare_evidence`, the Lean report runner. Defined afresh: the
  state with a record (`RState`) and its sameness (the rewriting acting on
  the record too), the five changes (`Change16`: the four kinds and the
  admission), `perform`, the exploration with its frontier and
  shortest-sequence counts, the potential and the cost rule, the mass
  invariants, the reachability criterion and the search, the independent
  count with the third factor and the one-term closed form, the checks
  (`RecordCheck`), the statements tested, the two unchosen readings, the
  comparison with the ninth and with the fourteenth, the evidence writer.
  Earlier derivations' files are not modified except to correct a defect,
  recorded in the relevant change log; `ci/check_mutation_bite.py` gains a
  sixteenth panel and `ci/check_definitional_citations.py` the sixteenth's
  record noun (both recorded in `paper/sixteenth/change_log.md`).
- `tests/test_sixteenth_*.py` — tests of `code/sixteenth/`; all of `code/`
  stays at ≥ 95 % line and ≥ 95 % branch coverage, every
  `code/**/evidence.py` fully covered (an injection test for every
  differential check); `mypy --strict` passes; the prose watchlist stays
  clean; the vacuous-check, definitional-citation and mutation-bite gates
  pass, the last with a sixteenth panel in which every disagreement field of
  `RecordCheck` bites under its mutation.
- `lean4/Sixteenth/` — a sixteenth Lean library in the same Lake package
  (the lakefile gains the library target and a default target; recorded in
  `paper/change_log.md`). It imports `Fifteenth` (and through it `Ninth` and
  `Fourteenth`). New: `RSt` (a ninth state and a record function on pairs),
  `WF`, `potential`, `mass`, the projection `toNDSt` and the embedding
  `ofNDSt`, the five operations, `Step16` (five constructors), `Reach16`,
  the maps of changes, the same-relation identity, the other-relation
  witnesses, the cost theorems, the mass invariants, the failure of the
  has-a-term criterion, the results, the comparison with the ninth and the
  fourteenth, and `rename16` (attempted).
- `evidence/sixteenth/` — written by `python code/generate_sixteenth.py`;
  the axiom report by `python code/lean_report_sixteenth.py`; `--check`
  regenerates into a temporary folder and compares.
- `paper/sixteenth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the sixteenth seed (`research/sixteenth/`)
Sentence-by-sentence diff against the fourteenth seed; the notion table with
source statuses; the readings above with what refuses each set-aside one;
the expected consequences; which "by construction" claims of the tenth to
fifteenth are re-examined.

### Phase 2 — `code/sixteenth/` and `tests/`
- the state with a record, canonical form and sameness over the record;
  the five changes; `perform`; the leftover writing of every change reused
  from the fourteenth; the admissibility of a writing (a pair writing of a
  recorded pair, never a merge writing, never nothing);
- the exploration (same protocol; admissions attempted after the direct
  additions), the frontier (attempts leaving the bound on terms), the
  shortest-sequence counts (the changes raising the potential by one), full
  logs at a small bound;
- the potential checked to move by exactly one on every change within the
  bound, up on additions and removals, down on admissions and
  identifications; the round of every result checked to be its potential;
  the same-relation identity checked on every removal within the bound; the
  other-relation outcome checked to differ from the start and from the
  direct addition; the mass and its diagonal part checked never to fall;
- the reachability criterion checked against breadth-first search on every
  ordered pair of results within a small bound, and compared with the
  ninth's criterion (the pairs the ninth admits and the sixteenth refuses,
  counted);
- the independent count with the third factor as the completeness
  certificate; the ninth's count recovered as the empty-record part; the
  one-term closed form checked;
- the comparison with the ninth: the empty-record results, their rounds and
  their shortest-sequence counts must be the ninth's; the comparison with
  the fourteenth: the leftover writing of every change of the four kinds is
  the fourteenth's;
- the unchosen readings C-R2 and C-R3 explored at a small bound and
  compared (counts, cost, the identity of item 1);
- property witnesses for "what does not follow";
- the checks as a dataclass `RecordCheck` whose every disagreement field is
  driven by an injection test and by a mutation in the sixteenth panel of
  `ci/check_mutation_bite.py`;
- deterministic evidence writer with `--check`; Lean axiom-report writer
  for `lean4/Sixteenth/Axioms.lean`.

### Phase 3 — `lean4/Sixteenth/`
Targets, in order:
1. `RSt`, `WF`, `potential`, `mass`, `toNDSt`, `ofNDSt`, the five
   operations; `Step16`, `Reach16`; `Step16.proj` (every change projects to
   a `Step9`), `Step9.embed` (an addition or an identification embeds; a
   removal embeds to the state with one leftover recorded), `Step16.wf`, a
   term stays, the first change adds a term, the empty state is never
   returned to.
2. `remove_admit_same` (the identity), `remove_admit_other_ne` (the start
   and the direct-addition outcome both differ), `admit_lowers_record`,
   `remove_raises_record`; the leftover of an admission is nothing.
3. Cost: `Step16.potential_step` (exactly one, with the direction by kind),
   `Reach16.potential_le`, `fewest_changes16` (lower bound by the potential;
   upper bound by the ninth's additions through the embedding and then an
   addition-removal pair per recorded leftover), `no_admission_on_shortest`
   (a sequence from the empty beginning of length the potential admits and
   identifies nothing, by a count of the falling changes).
4. Reachability: `Reach16.mass_le`, `Reach16.diag_le` (necessity),
   `has_term_criterion_fails16` (the witness), `reach16_same_terms`
   (sufficiency with the same terms), `result16_iff` (every well-formed
   state is a result), `cycle2_16` (remove then admit; a term added and
   identified away), `add_remove_not_cycle16` (the ninth's cycle leaves a
   leftover).
5. What survives (`Sixteenth/Compare.lean`): the ninth's cost on the
   empty-record results (`fewest_changes16_of_empty_record`) and its failure
   off them; the ninth's results as the empty-record results
   (`results_ninth_iff16`); jointly free results with any record; the
   fourteenth's `leftover_remove_r_s` as a step admitting an `r` leftover
   into `s` (`r_leftover_admitted_into_s`); `clearing_is_a_kind16` (an
   admission clears a leftover and is a `Step16`); the record is not raised
   by any addition (`record_not_raised_by_addition`).
6. `rename16`, `Step16.rename`, `Reach16.rename`, the potential in every
   writing. Attempted once; if a step does not close it is proved in the
   paper and marked "not in Lean".
`#print axioms` for every theorem the sixteenth paper cites, into
`evidence/sixteenth/lean_axioms.txt`.

### Phase 4 — `evidence/sixteenth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The fifteen earlier derivations' `--check` and Lean reports are
re-run to confirm their evidence still regenerates.

### Phase 5 — `paper/sixteenth/`
`paper.md` (findings; every use of an earlier derivation cited with the
re-check and whether it survives the feedback; a section answering the
task's questions: the same-relation identity, the other-relation result,
termination, the cost, reachability, the result set and the count, and
which earlier collapses and independence survive; final section: nearest
known results and differences — the only place where outside names appear),
`claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, push, pull request.

## Stopping conditions (sixteenth derivation)

The run stops when AH1–AH10 hold, or when a blocker is hit.

- AH1 Every notion in `paper/sixteenth/paper.md` has one recorded source
  status.
- AH2 Every claim in `paper/sixteenth/claim_ledger.md` has evidence, or is
  open.
- AH3 Every non-isomorphic alternative is kept, or eliminated by a cited
  proof; results are quotiented only under the implemented sameness.
- AH4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch coverage over all of `code/` and
  every evidence module fully covered; `python -m mypy` passes.
- AH5 `lake build` (pinned toolchain, inside `lean4/`) passes for all
  sixteen libraries; no `sorry`, `admit`, or declared axiom in `lean4/`;
  all sixteen axiom reports regenerated and committed.
- AH6 `evidence/sixteenth/` regenerates byte-identically (`--check`); the
  earlier derivations' evidence still regenerates byte-identically.
- AH7 Every use of an earlier result in the sixteenth paper is cited and
  re-checked, with the re-check saying whether it survives the feedback
  (ledger column "re-check"); every "by construction" claim of the tenth to
  fifteenth that the feedback touches is re-examined.
- AH8 The prose watchlist passes on the tracked tree; every pinned hit of
  the sixteenth paper is in its final section.
- AH9 `python ci/check_vacuous_checks.py`,
  `python ci/check_definitional_citations.py` and
  `python ci/check_mutation_bite.py` pass, the last with a sixteenth panel
  covering every disagreement field of `RecordCheck`.
- AH10 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and on rounds together. Targets: 3 terms with 6 rounds;
  2 terms with 8 rounds; full attempt logs at 2 terms and 3 rounds;
  reachability by search among the results of 2 terms and 5 rounds (and,
  if it completes in minutes, 3 terms and 4 rounds); the unchosen readings
  at 2 terms with 6 rounds. Any run that does not complete in minutes here
  has its rounds lowered first, then its terms; the bounds used are
  declared in the paper; the frontier is exported exactly; completeness
  within the bound is certified by the independent count.
- Rounds: at most 100; no change is invented.
- Lean targets 1–5 required; target 6 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `worktree-sixteenth-derivation`, made from `main`; the pull
  request is opened against `main` and not merged.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question. The
checkout's `lean4/.lake/packages` holds the pinned packages of this same
repository (checked before Phase 0: `Mathlib.olean` present; no download
happens during the derivation).

## How to run (sixteenth derivation)

From the repository root:
- `python -m pytest` (all tests, sixteen derivations), then
  `python code/xry/gate.py coverage.json`, `python -m mypy`,
  `python ci/check_prose_watchlist.py`, `python ci/check_vacuous_checks.py`,
  `python ci/check_definitional_citations.py` and
  `python ci/check_mutation_bite.py`;
- `python code/generate_sixteenth.py` writes `evidence/sixteenth/`;
  `python code/generate_sixteenth.py --check` compares with a fresh
  regeneration;
- `python code/lean_report_sixteenth.py` builds `lean4/` and writes
  `evidence/sixteenth/lean_axioms.txt`;
- the earlier derivations' commands are unchanged (see above).

---

# Seventeenth derivation (`prompt/seventeenth/`) — plan and stopping conditions

Written before any other work of the seventeenth derivation, as
`prompt/seventeenth/prompt.md` requires. Inputs: `prompt/seventeenth/prompt.md`
and `prompt/seventeenth/seed_prompt.md`. The parent is the base derivation
(`prompt/seed_prompt.md`, `paper/paper.md`, `code/xry/`, `lean4/H3V7N5QF/`,
`evidence/`), not the sixteenth. Later derivations are not inputs. Everything
above stays in force (isolation, no network, `prompt/` untouched, `.lake/`
never committed, bookkeeping rules 1–4, the evidence-module coverage gate).
Rule 5 of the seventeenth task: every result of the base that is used is
cited and its proof re-checked from this seed — whether it rested on the
struck ban ("for no term `x` may `xrx` be asserted") or only on the
obstruction procedure, which is kept. In Lean the re-check is an embedding
of the base's unobstructed steps into this seed's steps on loop-free states,
and a case split the other way; a theorem that assumed `Legal` as a given is
re-proved without that hypothesis or downgraded. Or by computing this seed's
exploration and comparing it with the base's on the results that assert no
`xrx`.

## What differs in the seed

One sentence is struck (`diff` against `prompt/seed_prompt.md`): "For no
term `x` may `xrx` be asserted." Every other sentence is identical,
including the obstruction paragraph. So a change that makes some `xrx`
asserted is still obstructed and must still be answered (refuse / remove
the obstruction / build structure). What the base argued *from the ban*
— `Legal` as a filter on states, `a ≠ b` via `given_distinct`, the
would-be outcome of an obstructed change not being a result, the orbit
count of states with no diagonal — must be re-examined. What it argued
from the four kinds and from the obstruction test on a loop-free state
carries over once that test is re-proved without taking the ban as a
given.

## Layout

- `research/seventeenth/` — reading notes (not evidence).
- `code/seventeenth/` — typed Python. Imported from `code/xry/` what the
  struck ban leaves intact: `State` (a state may hold `xrx`; `legal` is
  the predicate "no `xrx`", no longer a given), sameness, the four kinds,
  `perform`, the base obstruction (`obstruction`: the assertions that
  would become `xrx`), `answers`, `explore` (unobstructed steps only),
  `cost`, and the legal orbit counts. Defined afresh: the predicate
  `has_xrx`; a second obstruction test (the outcome asserts some `xrx`);
  the exploration that *performs* an obstructed change and records its
  outcome; the comparison with the base exploration; witnesses that the
  base cost is not a lower bound on that exploration; the count of states
  with the diagonal admitted. The launcher is `code/run_seventeenth.py`
  (`--check` regenerates into a temporary folder and compares). Base
  files are not modified except to correct a defect, recorded in
  `paper/change_log.md`.
- `tests/test_seventeenth_*.py` — tests of `code/seventeenth/`; all of
  `code/` stays at ≥ 95 % line and ≥ 95 % branch coverage, every
  `code/**/evidence.py` fully covered; `mypy --strict` passes; the prose
  watchlist stays clean.
- `lean4/Seventeenth/` — a seventeenth Lean library in the same Lake
  package (the lakefile gains the library target and a default target;
  recorded in `paper/change_log.md` because that file is from the base).
  It imports `H3V7N5QF`. `LoopFree` is a predicate, not a hypothesis of
  the seed. `Step17` is the base `Step` with no `Legal` side-condition on
  the state; `Step17.unobstructed` is the step that does not make an
  `xrx`. The base's unobstructed `Step` embeds and, on a loop-free state,
  a `Step17` that stays loop-free is a base `Step`.
- `evidence/seventeenth/` — written by `python code/run_seventeenth.py`.
- `paper/seventeenth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.
- `ci/check_mutation_bite.py` — a seventeenth panel, same shape as the
  others (one mutation per disagreement field).

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the seed (`research/seventeenth/`)
Sentence-by-sentence diff against the base seed. The notion table.
Readings kept:

- **A-replace** (the base's C7, kept): an obstructed change is not
  entered. Refusal changes nothing. Removing the obstruction is the
  removals, then the change (which is then unobstructed). Building is
  additions only, as in the base. The exploration is the base's.
- **A-perform** (dropped by the base because no state may hold `xrx`;
  the ban is struck, so the reading is kept): the obstructed change is
  performed and its outcome is a result, then answered. Refusal still
  changes nothing (it does not perform). Removing the obstruction of an
  identification after the identification, and before it, end at the
  same state; only the after-path has an `xrx` in between.
- **M1** (chosen, the base's obstruction): the obstruction is the
  assertions that would become some `xrx` — for an identification, those
  of `xry`, `yrx` that are asserted; for adding `xrx`, that assertion.
  An existing `xrx` does not by itself obstruct an unrelated change.
- **M2** (unchosen, kept): a change is obstructed when its outcome
  asserts some `xrx`, whether newly made or already there.

Expected, to be proved or refuted, not assumed:

- On a loop-free state M1 and M2 name the same changes (the base's D3
  without taking `Legal` as a given: the "related, hence obstructed"
  direction never used `Legal`; the converse uses loop-freeness of the
  start, not the ban). On a state that already asserts `ara`, identifying
  two other terms with nothing between them is obstructed under M2 and
  not under M1.
- Under A-replace, from either beginning (no `xrx`), every result asserts
  no `xrx`. The implemented predicate `has_xrx` is false on every
  reached result. The obstruction procedure plus "do not enter an
  obstructed change" reconstructs the irreflexivity the ban imposed.
  The base's results, rounds, cost, and legal orbit count survive, by
  the embedding and by comparing explorations.
- Under A-perform the predicate is true: adding `ara` to what is given,
  and identifying `a` with `b` while `arb` is asserted, are changes, and
  each outcome asserts some `xrx`. Those outcomes were forbidden by the
  ban and are valid now ("any outcome is valid"). The ban is not
  redundant under this reading. The base cost is not a lower bound
  (identifying `a` with `b` is one change; the base formula returns 3
  on the one-term state asserting `ara`). `a` and `b` need not stay two
  terms. After that identification `ara` is asserted, so "once `a` and
  `b` are one term, `arb` is never asserted again" fails if `ara` counts
  as what `arb` became, and holds only as a statement about two terms.
- What does not follow: that every well-formed state asserts no `xrx`;
  that A-replace and A-perform have the same results; that M1 and M2
  disagree on a loop-free state; that the base cost is the fewest
  changes once an obstructed change is performed.

The beginning is still the two states on the terms `a`, `b` asserting
`arb`, with `bra` or not (chosen, C2). Unchosen: a beginning that also
asserts `ara` or `brb`. Under A-replace those are not results of the
chosen beginning (adding `xrx` is not entered). Under A-perform they
are one addition away. Both are computed; neither is dropped.

### Phase 2 — `code/seventeenth/` and `tests/`
- `has_xrx`; M1 reused; M2; agreement on every loop-free state within
  the bound; one witness that they differ on a state with `ara`.
- A-replace exploration is `xry.explore`, compared result-for-result and
  round-for-round with a fresh call, both beginnings, both readings of
  sameness, at the declared bound. `has_xrx` checked false on each.
- A-perform exploration: breadth-first under `perform` of every change,
  obstructed or not, fewest additions first, same bound on terms and
  rounds. `has_xrx` checked true. The two witnesses above recorded.
  Answers of the base recorded beside each obstructed change; the
  perform-first and remove-first identifications compared.
- Base cost checked against A-replace rounds (must agree) and against
  the A-perform witness (must disagree: round 1, formula 3).
- Independent count: A-replace reuses `xry.orbits` (legal states) as the
  completeness certificate. A-perform counts states with the diagonal
  pairs included, if the exploration's scope is proved to be all
  well-formed states within the bound; otherwise the frontier is
  exported and the count is marked partial.
- Property witnesses for "what does not follow".
- `code/run_seventeenth.py` with `--check`. A Lean axiom-report writer
  for `lean4/Seventeenth/Axioms.lean`, same shape as
  `code/lean_report.py`.

### Phase 3 — `lean4/Seventeenth/`
Targets, in order:

1. `LoopFree`; `Step17` (four kinds, no `Legal` hypothesis); `Reach17`;
   `unobstructed`; `adding_xrx_obstructed` with no `Legal` hypothesis;
   on a loop-free state, an identification is obstructed under M1 iff
   under M2 iff the two terms are related. `has_xrx` of an unobstructed
   step from a loop-free state is false.
2. Embedding: every unobstructed `Step17` on a loop-free state is a
   base `Step`, and conversely. `Reach17` along unobstructed steps from
   a loop-free start stays loop-free and coincides with the base `Reach`.
   The base cost, cited, is the fewest changes along those steps.
3. A-perform: `perform` of adding `xrx` and of identifying related terms
   are steps; the outcome asserts `xrx` (`xrx_reached`); the base cost
   of that one-term outcome is not the length (`cost_not_lower_bound`);
   `a` and `b` are one term there (`names_merged_with_loop`).
4. Answers: remove-first and perform-first end at the same state
   (the base's `remove_obstruction_first_or_last`, re-checked; it no
   longer shows the intermediate is not a result). Refusal changes
   nothing.
5. `rename` for `Step17`. Attempted once; if it does not close, the
   step is proved in the paper and marked "not in Lean".

`#print axioms` for every theorem the seventeenth paper cites, into
`evidence/seventeenth/lean_axioms.txt`.

### Phase 4 — `evidence/seventeenth/`
Generated, hashed (`MANIFEST.sha256`), regenerated and compared with
`--check`. The base `python code/generate.py --check` is re-run to
confirm the base evidence still regenerates.

### Phase 5 — `paper/seventeenth/`
`paper.md` (findings; every use of a base result cited with the
re-check and whether it rested on the ban; a section answering whether
the obstruction rule reconstructs irreflexivity, whether any reachable
result asserts `xrx`, and which base results survive; final section:
nearest known results and differences — the only place outside names
appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit, pull request to `main`.

## Stopping conditions (seventeenth derivation)

The run stops when AI1–AI9 hold, or when a blocker is hit.

- AI1 Every notion in `paper/seventeenth/paper.md` has one recorded
  source status.
- AI2 Every claim in `paper/seventeenth/claim_ledger.md` has evidence,
  or is open.
- AI3 A-replace, A-perform, M1 and M2 are kept, or eliminated by a cited
  proof. The beginnings with `ara` or `brb` are kept or eliminated by a
  cited proof.
- AI4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- AI5 `lake +leanprover/lean4:v4.33.1 -d lean4 build` passes (exit code
  read on its own); no `sorry`, `admit`, or declared axiom in `lean4/`;
  the axiom report regenerated and committed.
- AI6 `evidence/seventeenth/` regenerates byte-identically (`--check`);
  the base `evidence/` still regenerates byte-identically.
- AI7 Every use of a base result is cited and re-checked, and the
  re-check says whether it rested on the ban (ledger column "re-check").
- AI8 The prose watchlist passes; `ci/check_vacuous_checks.py`,
  `ci/check_definitional_citations.py` and `ci/check_mutation_bite.py`
  pass, the last with a seventeenth panel covering every disagreement
  field. Every pinned hit of the seventeenth paper is in its final
  section.
- AI9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms, as the base, and on rounds for A-perform (a state
  has `n²` possible assertions, not `n² − n`). Targets: A-replace at 4
  terms (names kept) and 3 terms (any rewriting) with the base's round
  cap; A-perform at 3 terms with 4 rounds and 2 terms with 8 rounds;
  full attempt logs at 2 terms and 3 rounds. Any run that does not
  complete in minutes here has its rounds lowered first, then its
  terms. The bounds used are declared in the paper; the frontier is
  exported exactly; completeness within the bound is certified by the
  independent count where the count is proved, and marked partial
  where it is not.
- Rounds: at most 100; no change is invented.
- Lean targets 1–4 required; target 5 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `derivation/seventeenth`, made from `main` after the
  seventeenth-through-twentyfirst seeds were merged. The pull request
  is opened against `main`.

Blockers (stop and report): anything that would need the network, a
file outside the repository, a change to `prompt/`, or a question. The
checkout's `lean4/.lake/packages` holds the pinned packages of this
same repository (checked before Phase 0; no download happens).

## How to run (seventeenth derivation)

From the repository root:
- `python -m pytest`, then `python code/xry/gate.py coverage.json`,
  `python -m mypy`, `python ci/check_prose_watchlist.py`,
  `python ci/check_vacuous_checks.py`,
  `python ci/check_definitional_citations.py`, and
  `python ci/check_mutation_bite.py`;
- `python code/run_seventeenth.py` writes `evidence/seventeenth/`;
  `python code/run_seventeenth.py --check` compares with a fresh
  regeneration;
- the Lean build is `lake +leanprover/lean4:v4.33.1 -d lean4 build`,
  with the exit code read on its own line;
- the base derivation's commands are unchanged (see above).

---

# Eighteenth derivation (`prompt/eighteenth/`) — plan and stopping conditions

Written before the rest of the eighteenth derivation, as `prompt/eighteenth/prompt.md`
requires. Inputs: `prompt/eighteenth/prompt.md` and `prompt/eighteenth/seed_prompt.md`.
The parent is the base (`paper/`, `code/xry/`, `lean4/H3V7N5QF/`, `evidence/`).
The base is cited where used, and the citation says whether the result used the
sentence that two writings are the same result. `prompt/` is not modified.
`.lake/` is not committed.

## What differs

One sentence. The base says two results that differ only in how their terms
are written are the same result. This seed says they are different results.
The changes, the obstruction, and what is given are the base's.

## Plan

The chosen sameness is equality of the written state. The base's `canonical`
is not applied to an outcome. Both of the base's readings of what is given
(`bra` or not; names kept or not) are run. The unchosen reading that any
rewriting, including one no change produces, is a result, is kept and counted:
with the letters the changes assign it is the set of permutations of the
terms; with an unbounded supply of letters it is infinite. The declared bound
is 3 terms and 12 rounds, which is past the last round that reaches a new
result inside the bound. The frontier is the attempts that add a fourth term.

Lean records that swapping the two terms of what is given is a different
state from what is given and from the other beginning. The base does not
formalise the rewriting it quotients by; that limit stays named.

## Stopping

Stop when the paper, the ledger and the change log are written, the gates in
the prompt pass, and the evidence regenerates. Open claims stay open with a
falsifier. No `sorry`.

## How to run

From the repository root: `python -m pytest`, `python -m mypy`,
`python ci/check_prose_watchlist.py`, `python ci/check_vacuous_checks.py`,
`python ci/check_definitional_citations.py`, `python ci/check_mutation_bite.py`,
`python code/run_eighteenth.py --check`, and
`lake +leanprover/lean4:v4.33.1 -d lean4 build Eighteenth` with `$LASTEXITCODE`
read on its own line. `python code/lean_report_eighteenth.py` writes the
axiom report.

---

# Nineteenth, twentieth, and twenty-first derivations — plan and stopping conditions

Written before the rest of this run, as `prompt/nineteenth/prompt.md`,
`prompt/twentieth/prompt.md`, and `prompt/twentyfirst/prompt.md` require.
Each seed is the base seed (`prompt/seed_prompt.md`) with one sentence
changed. The parent is the base (`paper/`, `code/xry/`, `lean4/H3V7N5QF/`,
`evidence/`). Later derivations are not inputs. Everything above stays in
force (isolation, no network, `prompt/` untouched, `.lake/` never committed,
bookkeeping rules 1–4, the evidence-module coverage gate, the three `ci/`
gates). Rule 5: every base result that is used is cited and re-checked from
the changed sentence. The three runs share one branch because each diffs the
base and the user asked for all three; each keeps its own code, Lean
library, evidence, and paper.

## Nineteenth — identification rewrites one chosen assertion

The sentence "Identifying two terms replaces both by one term in every
assertion" becomes "in one chosen assertion".

- **P1 (chosen).** A partial identification picks two terms `u < v`, one
  asserted pair that mentions at least one of them, and a survivor in
  `{u, v}`. That one pair is rewritten; the terms stay. A rewrite that
  leaves the pair unchanged is not a change. The other three kinds are the
  base's. An outcome that asserts some `xrx` is obstructed and refused.
- **P2 (unchosen, kept).** Only a pair in which the two terms already both
  occur. Every such rewrite is a loop, so every such change is obstructed.
- **Set aside.** Dropping a term while rewriting only one assertion: an
  assertion that still names the dropped term is not a state of the base
  (assertions are between terms that are there). Not explored.

Expected, to be proved or refuted: a partial never changes the number of
terms, so the base's global identification (it erases a term) is not a
sequence of partials; the reachable results are the base results in which
the two names stay two terms; P1 and P2 reach the same results; adding a
term is never obstructed, so the process does not terminate.

## Twentieth — fewest total changes first

The sentence "Attempt every change, fewest additions first" becomes
"Attempt every change, fewest total changes first".

- **O1 (chosen).** A round is one performed change on a result already
  reached. The base exploration already spreads that way. "Fewest additions
  first" only lists the attempts inside a round. Both listings are run.
- **O2 (unchosen, kept).** Fewest additions is a global priority: expand the
  reached result with the smallest number of terms and assertions added,
  and stop after expanding as many results as O1 has reached by round 2.

Expected: under O1 the layers, the term-bound frontier, and the base
closure agree, at either beginning and either sameness. The recorded
additions do not equal the round. Under O2, before the closure is finished,
results enter and leave. "Complete within the term bound" is not an
artifact of the listing. Adding a term is never obstructed, so the process
does not terminate.

## Twenty-first — an obstructed change is refused

The sentence that an obstructed change must be answered is replaced by
"An obstructed change is refused." The ban on `xrx` stays.

- **R1 (chosen).** Refusal changes nothing. The exploration is the base's
  unobstructed steps. The base's answers are computed and compared; they
  are not performed as extra routes.
- No second exploration: the base already spreads along unobstructed steps
  and only checks answers afterwards (base D10). Re-checked, not assumed.

Expected: the reachable set is the base's, so it is not smaller; no answer
inside the bound buys a result the base lacks; the start has unobstructed
changes, so an alternative does not stop at the first obstruction; adding
a term is never obstructed, so the process does not terminate.

## Layout

- `code/nineteenth/`, `code/twentieth/`, `code/twentyfirst/` with
  `code/run_*.py`.
- `tests/test_nineteenth.py`, `tests/test_twentieth.py`,
  `tests/test_twentyfirst.py`.
- `lean4/Nineteenth/`, `lean4/Twentieth/`, `lean4/Twentyfirst/`, each
  importing `H3V7N5QF`. The lakefile gains the three targets (recorded in
  `paper/change_log.md`).
- `evidence/nineteenth/`, `evidence/twentieth/`, `evidence/twentyfirst/`.
- `paper/nineteenth/`, `paper/twentieth/`, `paper/twentyfirst/`.
- `ci/check_mutation_bite.py` gains three panels.

## Stopping conditions

The run stops when AJ1–AJ9 hold, or when a blocker is hit.

- AJ1 Every notion in the three papers has one recorded source status.
- AJ2 Every claim in the three ledgers has evidence, or is open.
- AJ3 P1/P2, O1/O2, and R1 are kept or eliminated by a cited proof.
- AJ4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- AJ5 `lake +leanprover/lean4:v4.33.1 -d lean4 build` of the three new
  libraries passes (exit code read on its own); no `sorry`, `admit`, or
  declared axiom in `lean4/`; the three axiom reports regenerated.
- AJ6 Each new `evidence/` regenerates byte-identically (`--check`); the
  base `evidence/` still regenerates.
- AJ7 Every use of a base result is cited and re-checked (ledger column
  "re-check").
- AJ8 The prose watchlist, vacuous-check, definitional-citation, and
  mutation-bite gates pass, the last with a panel per derivation covering
  every disagreement field.
- AJ9 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounds: 3 terms and 12 rounds (the base closure inside 3 terms has finished
by then). The frontier is the attempts that would add a fourth term. No
change is invented to reach 100 rounds.

Blockers: anything that would need the network, a file outside the
repository, a change to `prompt/`, or a question. `lean4/.lake/packages`
stays the pinned checkout; no `lake update`.

## How to run

From the repository root:

- `python -m pytest`, then `python code/xry/gate.py coverage.json`,
  `python -m mypy`, and the four `ci/check_*.py` gates;
- `python code/run_nineteenth.py`, `python code/run_twentieth.py`,
  `python code/run_twentyfirst.py`, each with `--check`;
- `python code/lean_report_nineteenth.py`,
  `python code/lean_report_twentieth.py`,
  `python code/lean_report_twentyfirst.py`;
- `lake +leanprover/lean4:v4.33.1 -d lean4 build Nineteenth Twentieth Twentyfirst`,
  then read the exit code on its own line.

---

# Isolation for later derivations (operator note, 2026-09-24)

A plan for reviewing the finished derivations stood here. It governed no
derivation and was moved out of this file; `paper/change_log.md` item 41
records the move.

These are operator steps, not results, and they hold for every later run:

- `.claude/settings.json` denies the network tools (web fetch and search,
  `curl`, `git fetch`, `pull` and `push`, `gh`, package installs,
  `lake update`), outside connectors and servers, reads outside the working
  directory, and edits to `.claude/`. A run commits on its branch; the
  operator pushes it and opens the pull request.
- A run starts in a fresh clone of a one-commit snapshot of `main` that omits
  `meta/`, with skills, plugins, memory and user settings off (from
  2026-09-26; earlier runs used a worktree). Nothing outside the clone is an
  input. The operator replays the run's commits onto `main`.

---

# Twenty-second derivation (`prompt/twentysecond/`) — plan and stopping conditions

Written before any other work of the twenty-second derivation, as
`prompt/twentysecond/prompt.md` requires. Inputs: `prompt/twentysecond/prompt.md`
and `prompt/twentysecond/seed_prompt.md`. The parent is the ninth
(`prompt/ninth/seed_prompt.md`, `paper/ninth/`, `code/ninth/`,
`evidence/ninth/`); the ninth's own parents — the seventh, the eighth, and
through them the first — are cited through it. The other derivations are not
inputs: their papers and results are not read or cited. Everything above
stays in force (isolation, no network, `prompt/` untouched, `.lake/` never
committed, bookkeeping rules 1–4, the evidence-module coverage gate, the
`ci/` gates). Rule 5 of this task: every earlier result used is cited, its
proof re-checked from this seed, and the ledger's re-check column says how —
*no change*, *re-proved*, or *computed again*.

## What differs in the seed

One sentence (`diff` against the ninth seed): "Two results that differ only
in how their terms are written are the same result." becomes "Two results
that differ only in how their terms are written, or only by an `xry` and an
`xsy` asserted together, are the same result." The state, the empty
beginning and the four kinds of change are the ninth's; what changes is when
two states are one result. So everything the ninth argued about states and
changes stands on states; everything it argued about *results* (its cost,
the round of a result, reachability between results, its count, the
exchange of the two relations, what is recorded for a result) must be
re-examined under the coarser sameness.

## Readings

- **C-J1 (chosen).** "Differ only by an `xry` and an `xsy` asserted
  together": one state is the other with one more `xry` and one more `xsy`
  on the same two terms `x`, `y` (`x = y` allowed, as the seed writes every
  assertion `xry`). "Are the same result" makes sameness an equivalence: the
  one generated by these steps and by rewriting. Expected (to prove): two
  states are the same result exactly when they have equally many terms and,
  after one rewriting, the same *excess* `M_r(x, y) − M_s(x, y)` at every
  ordered pair; every result has one *plain state* up to writing — the
  state asserting no pair in both relations.
- **C-J2 (unchosen, kept, computed).** The letters read as placeholders:
  any `xry` and any `usv` asserted together. Then only the terms and the
  difference of the two totals are kept; computed at a small bound (count,
  cost) and compared.
- **C-J3 (unchosen, kept, computed).** Only two different terms (`x ≠ y`):
  `xrx` and `xsx` are not merged. Computed at a small bound and compared.
- **Set aside, with the words that refuse each:** "one result has `xry`
  where the other has `xsy`" (refused by "asserted together": both are in
  one result); "the same only when the extra pair appears once, not closed
  under repetition" (refused by "are the same result": sameness is an
  equivalence).
- **C-X (chosen).** A change of a result is a change of any state that is
  that result; its outcome is the result of the outcome state. Expected (to
  prove): the results one change away do not depend on the state taken
  (additions and identifications directly; a removal of `xry` from a state
  that is not plain has the outcome of adding `xsy` to the plain state), so
  the exploration attempts the plain state's changes. Unchosen C-X′ (only
  the plain state's changes are changes of the result): the same results one
  change away and the same rounds (to prove); not computed apart.
- **C-R (chosen).** What is recorded for a result (G11: the terms and
  assertions it adds to what is given) is read on its plain state: its terms
  and its assertions `Σ |excess|`, split by relation. Unchosen: the counts
  of the state a particular sequence reached — a record of a sequence, not
  of a result; kept in the attempt log as the raw outcome's counts.

## Expected consequences, to be proved or refuted

1. **Undoing.** In the ninth no addition undoes an earlier addition: the
   size rises by one at each addition and the ninth's sameness keeps the
   size. Here adding `xsy` after adding `xry` gives back the result before
   both; on every state adding `xsy` has the outcome of removing `xry` (the
   same result). Two additions in a row return to their start's result
   exactly when, after one rewriting, their excesses cancel (the same pair
   in the two relations always does).
2. **Cost.** The fewest changes to a result is `n + Σ |excess|`, the ninth's
   cost of its plain state (lower bound: that quantity rises by at most one
   per change and is kept by the sameness; upper bound: additions). The
   ninth's cost of any state that is the result exceeds it by twice the
   number of pairs asserted together. Every shortest sequence is additions
   only, never adds both relations at one pair, and ends at the plain state.
3. **Which changes lower what is recorded, and by how much.** Adding a term:
   never (terms +1). Adding `xqy`: lowers the assertions by exactly one when
   the result asserts the other relation at that pair, else raises by one.
   Removing `xqy` from a state asserting it: lowers by exactly one when the
   result asserts `xqy`, else raises by one. Identifying two terms: lowers
   the terms by one and the assertions by an even number `2c`, `c ≥ 0`, as
   large as the merged excesses of opposite relations allow (unbounded). In
   the ninth only a removal (one assertion) and an identification (one term)
   lower it.
4. **Which of the ninth's results remain different.** Every ninth result is
   the same here as exactly one plain state; two plain states are the same
   here only if they are the same ninth result. What a merge loses: at each
   pair the part asserted in both relations (`min(M_r, M_s)`), hence the two
   totals separately, the size, each part as a seventh state, and whether a
   pair is asserted in both relations. A ninth state is determined by its
   result here together with that common part.
5. **Mapping an earlier seed in.** The ninth's states do not map one to one
   (witness: the one-term state asserting nothing and the one-term state
   asserting `ara` and `asa` once). The seventh's do: a seventh state read
   as a state asserting nothing with `s` gives distinct results for distinct
   seventh results, and each seventh change is carried to a change of the
   same kind. The map back reads the plain state: its `r` part if it asserts
   nothing with `s`, "none" otherwise; it returns the original on every
   mapped state and answers "none" first on the one-term result asserting
   `asa` once (round 2, the smallest such result). The eighth's and the
   first's states carry names, which results here forget: not one to one
   (witness).
6. **What survives of the ninth.** Reachability (a result reaches another
   exactly when the other has a term or the first is empty); the one-way
   exit from the empty state; the exchange of the relations (it negates
   every excess; a symmetry of results, cost and reachability). Expected to
   fail: the cost as the size off plain states; the one-term interleaving
   count `C(p + q, p)` (one shortest sequence per one-term result, as under
   the seventh); the ninth's count. New count: each cycle of pairs of a
   rewriting contributes `(1 + x^L) / (1 − x^L)`; with at most two terms the
   results of round `r` are `[r = 0] + [r = 1] + [r ≥ 2]·(2 + c₂(r − 2))`,
   `c₂(0) = 1`, `c₂(t) = 4t(t² + 2)/3 + [t even]·t`, of order `r³`.

## Layout

- `research/twentysecond/` — reading notes (not evidence).
- `code/twentysecond/` — typed Python. Imported where a result still
  applies: the two-relation state, `canonical`, `rewrite`, `swap`, `empty`
  (`ninth.state`, `eighth.state`), the change record, `changes`, `perform`
  (`ninth.changes`), the ninth's exploration and sequence counts for the
  comparison (`ninth.explore`), the seventh's exploration for the embedding
  (`seventh.explore`, `seventh.state`), the cycle machinery
  (`xry.orbits.partitions`, `class_size`), the writers, `compare_evidence`,
  the Lean report runner. Defined afresh: the excess, the plain state and
  the sameness of this seed; the exploration of results; the cost; the
  record and the rule for which changes lower it; the undoing checks; the
  seventh embedding and the map back; the merge losses; the count and the
  two-term closed form; reachability; the unchosen readings C-J2, C-J3; a
  `*Check` dataclass whose every disagreement field is driven by an
  injection test and by a mutation in a new panel of
  `ci/check_mutation_bite.py`. Launcher `code/run_twentysecond.py`
  (`--check` regenerates into a temporary folder and compares); axiom report
  `code/lean_report_twentysecond.py`, refusing any axiom other than
  `propext` and `Quot.sound`.
- `tests/test_twentysecond_*.py`.
- `lean4_core/` — a new Lake package, no `require`, toolchain
  `leanprover/lean4:v4.33.1`, library `Twentysecond`, nothing imported from
  `lean4/`. The ninth's state is re-written without the outside library:
  terms `0 … n − 1` (a rewriting of the ninth's finite set of terms,
  licensed by the sameness) and the assertions as a list of atoms
  (relation, `x`, `y`) whose counts are the multiplicities; an
  identification merges and rewrites the last term into the freed place.
  The seventh's state likewise with one relation. Re-proved there:
  everything used.
- `evidence/twentysecond/` — generated, with `MANIFEST.sha256`.
- `paper/twentysecond/` — `paper.md`, `claim_ledger.md`, `change_log.md`.
- `ci/check_axiom_citations.py` and `ci/check_definitional_citations.py`
  read `lean4/` only; they gain `lean4_core/` and the twenty-second
  derivation, so this derivation's citations are checked, not skipped
  (recorded in `paper/twentysecond/change_log.md`).

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the seed (`research/twentysecond/`)
Sentence-by-sentence diff against the ninth seed; the notion table with
source statuses; the readings above; which of the ninth's claims are about
results (re-examined) and which about states (no change).

### Phase 2 — `code/twentysecond/` and `tests/`
- the excess, the plain state, sameness (plain state, then the least
  writing under rewriting); a check that the equivalence generated by the
  seed's two clauses, found by search on small states, is exactly this;
- the exploration of results from the empty state, bounded in terms and
  rounds, attempting the plain state's changes fewest additions first;
  frontier; shortest-sequence counts; a full attempt log at a small bound
  (raw outcome and result recorded);
- per change within the bound: the cost moves by at most one; the recorded
  counts move as item 3 says; removals from states that are not plain land
  on an outcome of the plain state's list (C-X); two additions that undo;
- the cost formula against the explored rounds; the ninth's cost beside it;
- an independent count with the factor per cycle as the completeness
  certificate; the two-term closed form against the count and the run;
- comparison with the ninth's exploration (every ninth result is a result
  here within the bound; the plain ninth results are exactly the results,
  one each; how many ninth results each result takes in) and with the
  seventh's (the embedded seventh results are the results whose plain state
  asserts nothing with `s`, at the same rounds, with the same sequence
  counts);
- the map back and its smallest "none"; reachability against search; the
  exchange; the unchosen readings C-J2, C-J3 at a small bound;
- property witnesses for "what does not follow";
- deterministic evidence writer with `--check`; the Lean report writer.

### Phase 3 — `lean4_core/`
Targets, in order:
1. The model (atoms, states, well-formedness, the four operations, `Step`,
   `Reach`), the plain state (the list with the pairs asserted together
   taken out) and its counts; the seed's sameness at a fixed writing (the
   equivalence generated by adding a pair asserted together) is exactly
   "same terms and same plain state"; the exchange respects it.
2. Undoing: the ninth's additions never return to their start (size); here
   `xry` then `xsy` does; adding `xsy` and removing `xry` give the same
   result.
3. Cost: the lower bound (the plain size rises by at most one per change),
   the upper bound (additions), fewest changes exactly; shortest sequences
   are additions ending at the plain state.
4. What is recorded: the exact move of each kind of change (item 3).
5. The seventh's states: the map in, changes carried, one to one; the map
   back returning the original, answering "none" on `a; asa`, and on no
   result of cost below 2; the ninth's map not one to one (witness); what a
   merge loses (the common part; a ninth state is determined by its result
   and its common part).
6. Reachability (the ninth's criterion re-proved) and the exchange.
7. Rewriting: the full sameness (rewriting and pairs asserted together) in
   one normal form; the one-to-one statement of target 5 up to rewriting.
   Attempted once; if it does not close, proved in the paper and marked
   "not in Lean".
`#print axioms` for every theorem the paper cites, in
`lean4_core/Twentysecond/Axioms.lean`, reported by
`code/lean_report_twentysecond.py` into
`evidence/twentysecond/lean_axioms.txt`.

### Phase 4 — `evidence/twentysecond/`
Generated, hashed, regenerated and compared with `--check`. Every earlier
derivation's `--check` re-run to confirm its evidence still regenerates.

### Phase 5 — `paper/twentysecond/`
`paper.md` (findings; every use of the ninth, seventh, eighth or first
cited with its re-check; the answers to the task's questions: undoing, the
fewest changes, which changes lower what is recorded and by how much, which
of the ninth's results remain different and what the merge loses, the map
in and the map back, and which of the ninth's results — cost,
reachability, the exchange — hold here and where they do not; final
section: nearest known results and differences, the only place where
outside names appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit (no push).

## Stopping conditions (twenty-second derivation)

The run stops when AK1–AK10 hold, or when a blocker is hit.

- AK1 Every notion in `paper/twentysecond/paper.md` has one recorded source
  status.
- AK2 Every claim in `paper/twentysecond/claim_ledger.md` has evidence, or
  is open; the ledger has the columns ID, statement, status, evidence, axiom
  report, re-check, falsifier.
- AK3 C-J1/C-J2/C-J3, C-X/C-X′ and C-R are kept or eliminated by a cited
  proof; every non-isomorphic result within the bound is kept.
- AK4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- AK5 `lake +leanprover/lean4:v4.33.1 -d lean4_core build` passes, its exit
  code read on its own line; no `sorry`, `admit` or declared axiom in
  `lean4_core/`; the axiom report lists only `propext` and `Quot.sound`.
- AK6 `python code/run_twentysecond.py --check` matches; every earlier
  derivation's evidence still regenerates byte-identically.
- AK7 Every use of an earlier result is cited and re-checked (ledger column
  "re-check": no change, re-proved, or computed again).
- AK8 The prose watchlist, `ci/check_vacuous_checks.py`,
  `ci/check_definitional_citations.py`, `ci/check_mutation_bite.py` (with a
  twenty-second panel covering every disagreement field) and
  `ci/check_axiom_citations.py` pass; every pinned hit of the paper is in
  its final section.
- AK9 The paper states whether an addition can undo an earlier addition
  here, and which of the ninth's results (cost, reachability, exchange)
  hold here and where not.
- AK10 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and rounds together. Targets: 5 terms with 8 rounds, 3
  terms with 10, 2 terms with 24; a full attempt log at 2 terms and 3
  rounds; reachability among the results of 3 terms and 4 rounds; the
  ninth's exploration for the comparison at bounds it completes in minutes
  (declared); the unchosen readings at 2 terms. Any run that does not
  complete in minutes here has its rounds lowered first, then its terms;
  the bounds used are declared in the paper; the frontier is exported
  exactly; completeness within the bound is certified by the independent
  count; the two-term round counts are proved in closed form for every
  round, so the seed's 100 rounds are given by formula, not listed.
- Rounds: at most 100; no change is invented.
- Lean targets 1–6 required; target 7 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `derivation/twentysecond`; commits only, no push.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question.
`lean4_core/` needs no package; should `lake` try to fetch anything, the
build is stopped and the Lean claims are marked open.

## How to run (twenty-second derivation)

From the repository root:
- `python -m pytest`, then `python code/xry/gate.py coverage.json`,
  `python -m mypy`, `python ci/check_prose_watchlist.py`,
  `python ci/check_vacuous_checks.py`,
  `python ci/check_definitional_citations.py`,
  `python ci/check_mutation_bite.py`, `python ci/check_axiom_citations.py`;
- `python code/run_twentysecond.py` writes `evidence/twentysecond/`;
  `python code/run_twentysecond.py --check` compares with a fresh
  regeneration;
- `lake +leanprover/lean4:v4.33.1 -d lean4_core build`, then read the exit
  code on its own line; `python code/lean_report_twentysecond.py` builds
  and writes `evidence/twentysecond/lean_axioms.txt`.

---

# Twenty-third derivation (`prompt/twentythird/`) — plan and stopping conditions

Written before any other work of the twenty-third derivation, as
`prompt/twentythird/prompt.md` requires. Inputs: `prompt/twentythird/prompt.md`
and `prompt/twentythird/seed_prompt.md`. The parent is the twenty-second
(`prompt/twentysecond/seed_prompt.md`, `paper/twentysecond/`,
`code/twentysecond/`, `lean4_core/Twentysecond/`, `evidence/twentysecond/`);
its own parents — the ninth, the seventh, the eighth, and through them the
first — are cited through it. The other derivations are not inputs.
Everything above stays in force (isolation, no network, `prompt/` untouched,
`.lake/` never committed, bookkeeping rules 1–4, the evidence-module coverage
gate, the `ci/` gates). Rule 5 of this task: every earlier result used is
cited, its proof re-checked from this seed, and the ledger's re-check column
says how — *no change*, *re-proved*, *imported* (a `lean4_core/Twentysecond`
theorem used as it stands, its statement mentioning nothing this seed
changes), or *computed again*.

## What differs in the seed

Against the twenty-second seed (`diff`): the sameness sentence gains a third
clause — "Two results that differ only in how their terms are written, only by
an `xry` and an `xsy` asserted together, or only by raising terms, are the
same result." — and one sentence is added: "Raising a term `x` adds `xry` and
`ysx` once for every other term `y`." Every other sentence is the twenty-
second's, and so the ninth's except for sameness. States, the empty
beginning and the four kinds of change are unchanged; only *when two states
are one result* changes again. Raising is not a change ("Nothing else is a
change"): it only says which states are one result.

## Readings

- **C-H1 (chosen). Raising.** Raising `x` gives the state with one more `xry`
  and one more `ysx` for every term `y` other than `x` (the terms of the state
  being raised). "Differ only by raising terms": one state is the other with
  some of its terms raised, each some number of times. "Are the same result"
  makes the sameness an equivalence: the one generated by the three clauses.
  Expected (to prove): two states are one result exactly when they have
  equally many terms and, after one rewriting, their excesses
  `M_r(x, y) − M_s(x, y)` differ by `g(x) − g(y)` at every ordered pair, for
  some whole number `g(x)` per term (so the loops `xrx`, `xsx` keep their
  excess).
- **C-H2 (unchosen, kept, computed).** "Raising terms" as raising every term
  at once. Raising every term once adds, at every ordered pair of two
  different terms, one `xry` and one `xsy`: pairs asserted together. Expected
  (to prove): the results are then exactly the twenty-second's.
- **C-H3 (unchosen, eliminated if the proof closes).** Each term raised at
  most once. The sameness is an equivalence, and raising a term of a state
  that is itself a raised state raises it twice, so the generated equivalence
  is C-H1's.
- **Set aside, with the words that refuse each:** raising also adds `xrx` and
  `xsx` (refused by "every other term"); raising is a change (refused by
  "Nothing else is a change").
- **The twenty-second's readings of its clause** (C-J1 chosen, C-J2 and C-J3
  kept) are re-examined with raising added: under C-J2 raising is a
  combination of its steps, so C-J2's results are unchanged (to prove); C-J3
  with raising is computed at a small bound.
- **C-E (chosen). The exploration.** As the task says, changes are performed
  on states and the results formed afterwards: the twenty-second's
  exploration (its alternatives are its results, i.e. its plain states up to
  writing) is run as it stands, and its reached states are then grouped into
  this seed's results; the round of a result is the first round in which one
  of its states is reached. Unchosen C-E′ (computed again at smaller bounds):
  the ninth's exploration of states, grouped likewise; expected the same
  results and rounds. The twenty-second's C-X (a change of a result is a change
  of any of its states, the results one change away not depending on the
  state) is expected to fail here: adding a term to `a b` and to
  `a b; arb bsa` (the same result) gives two different results.
- **C-R (chosen). What is recorded.** The terms, and the assertions in `r`
  and in `s` of a state of the result asserting the fewest assertions.
  Expected (to prove): the same for every such state (the sum of the excess
  over all ordered pairs is kept by the sameness, so the split between `r` and
  `s` is).

## Expected consequences, to be proved or refuted

1. **Nothing asserted.** In the twenty-second a result is the result
   asserting nothing on its terms exactly when its excess is zero everywhere:
   a state asserting something can be (`a; ara asa`), a result whose plain
   state asserts something cannot. Here: exactly when every loop has excess
   zero, every two terms have excesses summing to zero both ways round, and
   every three terms have excesses summing to zero around — equivalently the
   excess is `g(x) − g(y)`. Every other result carries a loop, two terms or
   three terms whose sum is not zero, the same in every state of it; no
   longer sum is needed. Witnesses: `a b; arb bsa` (raising `a`) is the result
   asserting nothing here and not in the twenty-second; `a b c; arb bsa` is
   not, its three-term sum being one.
2. **Changes of a result depend on the state taken.** Adding a term to two
   states of one result can give different results; identifying two terms too
   (with four terms or more). A change performed on a state of the result
   asserting the fewest raises the cost by at most one; performed on another
   state of the same result, adding a term can raise it by `2k + 1` for every
   `k`.
3. **Fewest changes.** The fewest changes to a result is `n` plus the fewest
   assertions among its states, `n + min_g Σ |e(x, y) + g(x) − g(y)|`. At
   least `n` plus the loops' and the two-way sums' absolute values; equal with
   at most two terms; with three terms a closed form in the loops, the three
   two-way sums and the three-term sum; in general reached by raising sets of
   terms one set at a time while the count falls (to prove). Parity:
   `n + Σ e` is kept by the sameness and changed by every change, so no change
   returns a result to itself or keeps its round's parity.
4. **Which states assert the fewest.** Exactly the states asserting no pair in
   both relations for which raising no set of terms (then taking out the
   pairs asserted together) lowers the count. With at most three terms single
   terms suffice (every set is a term or all the terms but one); with two
   terms the condition is: no `xry` asserted together with `ysx`. With four
   terms single terms do not suffice (witness to be found and proved). A
   result can have arbitrarily many such states (two terms, `arb` `k` times).
5. **Mapping an earlier seed in.** Expected: none of the four maps one to one.
   `a b; arb arb` and `a b; arb bra` are different seventh results, ninth
   states and twenty-second results, and one result here; for the first seed
   (one relation, each pair at most once, no `xrx`), `a b c; arb arc` and
   `a b c; bra cra`, different in every writing. Any map sending the empty
   state to the empty result and each addition to the same addition here
   merges them. The map back goes to the twenty-second's results: a result's
   state asserting the fewest, when it is one twenty-second result up to
   writing, "none" otherwise. It returns the original on a twenty-second
   result exactly when that result is the only state of its result here
   asserting the fewest; it answers another twenty-second result on the
   others that it answers. Expected smallest "none": cost 4, two terms
   (`a b; arb arb`, `a b; ara arb` and their variants).
6. **What a merge loses.** Where two twenty-second results become one: the
   excess beyond what the loops, the two-way sums and the three-term sums fix
   (the `g`); with it the twenty-second's cost, its plain state, and the
   excess at each ordered pair. Kept: the terms, those sums, `Σ e`, the cost
   and what is recorded.
7. **What of the twenty-second holds here.** Reachability (a result reaches
   another exactly when the other has a term or the first is empty) holds;
   the exchange of the relations holds (it negates every excess and turns
   raising into raising all the other terms); the cost holds exactly on the
   results whose plain twenty-second state asserts the fewest; "the results
   one change away do not depend on the state" fails (item 2); undoing now
   also by `xry` then `ysx` on two terms. With one term nothing changes. With
   two terms the results recording `t` assertions number `2t² + t + 1`
   (`t ≥ 1`), so the results of round `r` with at most two terms are of order
   `r²`; within the seed's 100 rounds they are given by formula.

## Layout

- `research/twentythird/` — reading notes and scratch (not evidence).
- `code/twentythird/` — typed Python. Imported where a result still applies:
  the state, `canonical`, `rewrite`, `swap`, `empty`, `excess`, `plain`,
  `result_of` (the twenty-second's result, which is this seed's *state* of
  the exploration), the twenty-second's exploration, its orbit count and
  closed forms, its checks' writers; the ninth's and seventh's explorations
  for the comparisons; `xry.orbits`; the writers, `compare_evidence`, the Lean
  report runner. Defined afresh: raising; the normal form of a result (the
  excess made zero at every pair `(x, 0)`, then the least writing); the
  sums that show a result is not the result asserting nothing; the fewest
  assertions (descent by raising sets of terms, checked against a search over
  `g` and against the closed forms); the states asserting the fewest; the
  grouping of the exploration into results; the record; the counts; the
  mapping witnesses and the map back; reachability; the readings C-H2, C-J2,
  C-J3; a `*Check` dataclass whose every disagreement field has an injection
  test and a mutation in a new panel of `ci/check_mutation_bite.py`.
  Launcher `code/run_twentythird.py` (`--check`); axiom report
  `code/lean_report_twentythird.py`, refusing any axiom other than `propext`
  and `Quot.sound`.
- `tests/test_twentythird_*.py`.
- `lean4_core/Twentythird/` — a library `Twentythird` in the existing package,
  importing `Twentysecond`; the lakefile gains the library and a default
  target (recorded in `paper/twentysecond/change_log.md`, since the lakefile
  is the twenty-second's).
- `evidence/twentythird/` — generated, with `MANIFEST.sha256`.
- `paper/twentythird/` — `paper.md`, `claim_ledger.md`, `change_log.md`.
- `ci/check_axiom_citations.py` lists the twenty-third derivation.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the seed (`research/twentythird/`)
Sentence-by-sentence diff against the twenty-second seed; the notion table
with source statuses; the readings above; which of the twenty-second's claims
are about states and changes (no change), about results (re-examined), or
about the twenty-second's own sameness (re-proved or refuted).

### Phase 2 — `code/twentythird/` and `tests/`
- raising; the normal form; a check that the equivalence generated by the
  seed's three clauses, found by search on small states, is exactly the
  normal form's classes;
- the exploration: the twenty-second's at 5 terms and 8 rounds, 3 terms and
  10, 2 terms and 24, grouped into results; the round of each result against
  its cost by formula; the frontier; a full attempt log at 2 terms and 3
  rounds with each outcome's result here;
- the cost: descent, search over `g` in a box, the two- and three-term closed
  forms, the lower bounds, compared with each other and with the rounds;
- the states asserting the fewest: per result, those reached at its round;
  checked against the characterization; the four-term witness;
- per change within the bound, performed on a state asserting the fewest: the
  cost moves by at most one, the parity changes; the witnesses of item 2;
- an independent count of the results by terms and cost for at most three
  terms (from the loops, two-way sums and three-term sum, with the closed-form
  cost), and the two-term closed form, against the exploration; for four and
  five terms, completeness from the twenty-second's own certificate and the
  proof that every result's states asserting the fewest are twenty-second
  results within the bound;
- comparisons: the twenty-second's results merged (how many into each), the
  ninth's exploration grouped (C-E′), the seventh's embedded;
- the map back and its smallest "none"; reachability against search; the
  exchange; the readings C-H2, C-J2, C-J3 at a small bound;
- property witnesses for "what does not follow";
- deterministic evidence writer with `--check`; the Lean report writer.

### Phase 3 — `lean4_core/Twentythird/`
Targets, in order:
1. Raising (`St.raise`, many raisings), its excess, the generated sameness
   (`Gen3`) and the criterion (`Same3`: equally many terms and excesses
   differing by `g(x) − g(y)`), both directions; raising every term is pairs
   asserted together (C-H2).
2. The nothing criterion: the sums kept by `Same3`; `Same3` with the state
   asserting nothing exactly when the loop, two-way and three-term sums are
   zero; the twenty-second's criterion (excess zero); the witnesses of item 1.
3. The cost: the fewest changes to a result is the fewest `phi` among its
   states; the lower bound by loops and two-way sums; equality with two terms;
   the three-term witness; the parity; a change from a state asserting the
   fewest raises the cost by at most one; adding a term to another state can
   raise it by `2k + 1`.
4. The states asserting the fewest: plain; the two-term characterization; the
   four-term witness.
5. Mapping: the witnesses for the seventh (`ofR`), the ninth, the
   twenty-second and the first; the merge of any map carrying additions; the
   map back (a relation, no choice), its answers on mapped states, "none" on
   the smallest results, and no "none" below cost 4.
6. Reachability (the criterion re-proved for `Same3`), the exchange, the
   failure of the twenty-second's `step_of_same`.
7. Rewriting: the full sameness in every writing. Attempted once; if it does
   not close, proved in the paper and marked "not in Lean".
`#print axioms` for every theorem the paper cites, in
`lean4_core/Twentythird/Axioms.lean`, reported by
`code/lean_report_twentythird.py` into `evidence/twentythird/lean_axioms.txt`.

### Phase 4 — `evidence/twentythird/`
Generated, hashed, regenerated and compared with `--check`. Every earlier
derivation's `--check` re-run to confirm its evidence still regenerates.

### Phase 5 — `paper/twentythird/`
`paper.md` (findings; every use of an earlier derivation cited with its
re-check; the answers to the task's questions: the twenty-second's nothing
question, which results here are the result asserting nothing, what shows
each other is not, the fewest changes, which states assert the fewest, the
mapping and the map back, what the merge loses, and which of the
twenty-second's results — cost, reachability, exchange — hold here and where
they do not; final section: nearest known results and differences, the only
place where outside names appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit (no push).

## Stopping conditions (twenty-third derivation)

The run stops when AL1–AL10 hold, or when a blocker is hit.

- AL1 Every notion in `paper/twentythird/paper.md` has one recorded source
  status.
- AL2 Every claim in `paper/twentythird/claim_ledger.md` has evidence, or is
  open; the ledger has the columns ID, statement, status, evidence, axiom
  report, re-check, falsifier.
- AL3 C-H1/C-H2/C-H3, C-J1/C-J2/C-J3, C-E/C-E′ and C-R are kept or eliminated
  by a cited proof; every non-isomorphic result within the bound is kept.
- AL4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- AL5 `lake +leanprover/lean4:v4.33.1 -d lean4_core build` passes, its exit
  code read on its own line; no `sorry`, `admit` or declared axiom in
  `lean4_core/`; the axiom report lists only `propext` and `Quot.sound`.
- AL6 `python code/run_twentythird.py --check` matches; every earlier
  derivation's evidence still regenerates byte-identically.
- AL7 Every use of an earlier result is cited and re-checked (ledger column
  "re-check": no change, re-proved, imported, or computed again).
- AL8 The prose watchlist, `ci/check_vacuous_checks.py`,
  `ci/check_definitional_citations.py`, `ci/check_mutation_bite.py` (with a
  twenty-third panel covering every disagreement field) and
  `ci/check_axiom_citations.py` pass; every pinned hit of the paper is in its
  final section.
- AL9 The paper states which results are the result asserting nothing, what
  shows each other result is not, and which of the twenty-second's results
  (cost, reachability, exchange) hold here and where not.
- AL10 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: the twenty-second's explorations at their own bounds (5 terms and
  8 rounds, 3 and 10, 2 and 24), grouped; the ninth's for C-E′ at bounds that
  complete in minutes (declared); a full attempt log at 2 terms and 3 rounds;
  reachability among the results of 3 terms and 4 rounds; the readings at 2
  terms. Any run that does not complete in minutes here has its rounds
  lowered first, then its terms; the bounds used are declared in the paper;
  the frontier is exported exactly; completeness within the bound is
  certified; the two-term round counts are proved in closed form for every
  round, so the seed's 100 rounds are given by formula, not listed.
- Rounds: at most 100; no change is invented.
- Lean targets 1–6 required; target 7 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `derivation/twentythird`; commits only, no push.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question; a tool refused
by the session's permissions (as happened once at the start of this run,
before this plan was written: writes, `python` and `lake` were refused until
the operator allowed them). Should `lake` try to fetch anything, the build is
stopped and the Lean claims are marked open.

## How to run (twenty-third derivation)

From the repository root:
- `python -m pytest`, then `python code/xry/gate.py coverage.json`,
  `python -m mypy`, `python ci/check_prose_watchlist.py`,
  `python ci/check_vacuous_checks.py`,
  `python ci/check_definitional_citations.py`,
  `python ci/check_mutation_bite.py`, `python ci/check_axiom_citations.py`;
- `python code/run_twentythird.py` writes `evidence/twentythird/`;
  `python code/run_twentythird.py --check` compares with a fresh
  regeneration;
- `lake +leanprover/lean4:v4.33.1 -d lean4_core build`, then read the exit
  code on its own line; `python code/lean_report_twentythird.py` builds and
  writes `evidence/twentythird/lean_axioms.txt`.

---

# Twenty-fourth derivation (`prompt/twentyfourth/`) — plan and stopping conditions

Written before any other work of the twenty-fourth derivation, as
`prompt/twentyfourth/prompt.md` requires. Inputs: `prompt/twentyfourth/prompt.md`
and `prompt/twentyfourth/seed_prompt.md`. The parent is the twenty-third
(`prompt/twentythird/seed_prompt.md`, `paper/twentythird/`,
`code/twentythird/`, `lean4_core/Twentythird/`, `evidence/twentythird/`); its
own parents — the twenty-second, and through it the ninth, the seventh, the
eighth and the first — are cited through it. The other derivations are not
inputs; the twenty-fifth (`prompt/twentyfifth/`) is a sibling started from the
same point and is not an input either. Everything above stays in force
(isolation, no network, `prompt/` untouched, `.lake/` never committed,
bookkeeping rules 1–4, the evidence-module coverage gate, the `ci/` gates).
Rule 5 of this task: every earlier result used is cited, its proof re-checked
from this seed, and the ledger's re-check column says how — *no change*,
*re-proved*, *imported* (a `lean4_core/Twentythird` or
`lean4_core/Twentysecond` theorem used as it stands, its statement mentioning
nothing this seed changes), or *computed again*. This derivation and its
sibling land on one branch: in the files they share (`CLAUDE.md`,
`lean4_core/lakefile.toml`, `ci/check_mutation_bite.py`,
`ci/check_axiom_citations.py`, `ci/check_definitional_citations.py`, an earlier
derivation's `change_log.md`) this derivation only adds; nothing already there
is reordered, reworded or reformatted.

## What differs in the seed

Against the twenty-third seed (`diff`), one sentence changes and one is
added. The list of changes gains a fifth kind: "A change is exactly one of:
identifying two terms; removing an assertion; adding a term; adding an
assertion; filling one term." Added after the sentence on identifying: "A
filled term `x` balances when `xrx` and `xsx` are asserted equally often; for
every result, record which filled terms balance." Every other sentence is the
twenty-third's, the sameness sentence and the raising sentence included. The
seed does not say what filling does beyond making a term filled, and the
sameness sentence says nothing of filled terms.

## Readings

- **C-F1 (chosen). Filling.** Filling `x` makes `x` filled and changes
  nothing asserted: a state is the twenty-third's state (terms, a
  multiplicity for each ordered pair in each relation) with a set of filled
  terms among its terms. Filling a filled term changes nothing and is not a
  change, as removing what is not asserted is not (9:C5⁗). Unchosen C-F1′ (it
  is a change whose outcome is its start): the same results at the same
  rounds (to prove), so eliminated.
- **C-F2 (unchosen, kept, computed).** A term is filled a number of times,
  each filling raising it by one; "filled" is filled at least once. It gives
  different results (a term filled twice); computed at a small bound (count,
  cost) and compared.
- **C-F3 (unchosen, to be eliminated by proof).** Filling `x` also asserts
  `xrx` and `xsx` once each. That is a pair asserted together, so its outcome
  is C-F1's result (to prove in Lean) and the results and rounds are C-F1's.
- **C-F4 (unchosen, kept, computed).** Filling `x` makes it balance, adding
  `xrx` or `xsx` until they are asserted equally often. Expected: the same
  results and the same fewest changes as C-F1 (the potential below), other
  outcomes of single changes; computed at a small bound.
- **C-S (chosen). Filled terms and the sameness.** A rewriting carries the
  filled terms with the terms; pairs asserted together and raising touch no
  filled term; two results that differ in which terms are filled are two
  results (no clause of the sameness sentence joins them). Set aside: filled
  terms kept off the result as a record of the sequence that reached it —
  refused by "for every result, record which filled terms balance", which
  needs the filled terms of a result.
- **C-I1 (chosen). Identifying.** The one term is filled when either term
  was ("replaces both by one term": the one term stands for both).
  **C-I2** (filled only when both were) and **C-I3** (never filled) are
  unchosen, kept and computed. Expected: the same results and the same fewest
  changes under all three; which result an identification reaches, how far it
  moves the cost, and reachability differ (under C-I1 a result with a filled
  term never reaches one without; under C-I2 and C-I3 it can).
- **C-B (chosen). Balance and its record.** `x` balances when
  `M_r(x, x) = M_s(x, x)`. Expected: the same in every state of the result and
  in every writing (a loop's excess is kept by the sameness, 23:D2), so
  balance belongs to the result. The record: for every filled term of the
  result, at its least writing, whether it balances; with it the numbers of
  filled terms that balance and that do not. The twenty-third's record (terms,
  and the assertions in `r` and in `s` of a state asserting the fewest,
  23:C-R) is kept beside it: G11 is unchanged.
- **C-N (chosen). "A result with nothing asserted on as many terms"** (the
  task's words): as many terms and the same filled terms, nothing asserted;
  the question is then about the assertions. Unchosen C-N0 (nothing asserted
  and nothing filled): every result with a filled term is then not such a
  result; kept and answered alongside.
- **C-K (chosen). "The terms that keep a result from being the one asserting
  nothing"** (the task's words, for the twenty-third): the smallest sets of
  terms on which the result, restricted, is not the one asserting nothing —
  a loop, two terms, or three terms whose sum is not zero (23:D2).
- **C-O (chosen). Order of the attempts.** Filling adds no term and no
  assertion, so it comes with the changes that add nothing: identifications,
  removals in `r`, in `s`, fillings, a term, additions in `r`, in `s`.
  Expected: the order within a round changes no result and no round (only the
  attempt log).
- **The twenty-third's C-E, C-X, C-R** are kept: changes are performed on
  states — the twenty-second's plain states, now with their filled terms, at
  their least writing — and the results are formed afterwards. Unchosen C-E′
  (the ninth's states with filled terms, grouped) is computed at a small
  bound.

## Expected consequences, to be proved or refuted

1. **The twenty-third's question.** Its record shows *whether* a result is the
   one asserting nothing (it records no assertion exactly then) but not
   *which* terms keep it from being: `a b; ara` and `a b; arb` record the same
   (two terms, one `r`) and are kept by one term and by two terms together;
   `a b c; ara asb` and `a b c; arb bsa` record the same and are kept by one
   term and only by three terms together.
2. **Balance** belongs to the result. In the result with nothing asserted
   every filled term balances. A result that is not it is told apart from it
   by filled terms that do not balance exactly when some filled term has a
   loop whose excess is not zero. It cannot be told when every filled term
   balances: (a) a loop of non-zero excess only at unfilled terms — one filling
   away from being told; (b) every loop of excess zero — never, whatever terms
   are filled: what shows it is not the one asserting nothing is then two
   terms or three terms (23:D2).
3. **Fewest changes**: the twenty-third's cost plus the number of filled
   terms, `n + |F| + min_g Σ |e(x, y) + g(x) − g(y)|`. Lower bound: the
   twenty-second's `phi` plus the number of filled terms rises by at most one
   per change; upper bound: additions, then fillings. Shortest sequences:
   additions and fillings only, fillings interleaved; counted per result.
4. **Changes of a result.** Filling respects the sameness (performed on two
   states of one result it gives one result); adding a term still does not
   (23:D4, carried in by the embedding).
5. **Parity.** Every change of the twenty-third moves the cost by an odd
   number (23:D6). Here filling moves it by exactly one, and under C-I1
   identifying two filled terms moves it by an even number (`a b` both filled,
   cost 4, identified: `a` filled, cost 2). No change returns a state to its
   own result.
6. **Reachability.** Under C-I1 a result reaches another exactly when the
   other has a term or the first is empty, and the other has a filled term or
   the first has none: the twenty-third's criterion fails exactly on reaching
   a result with no filled term from one with a filled term. Under C-I2 and
   C-I3 the twenty-third's criterion holds.
7. **The exchange of the two relations**: a symmetry of results, cost,
   reachability and balance (it negates every loop's excess, keeping zero).
8. **Mapping an earlier seed in.** The twenty-third's results, with no term
   filled, map one to one, each change carried to a change of the same kind;
   so this seed makes no two of the twenty-third's results the same and the
   merge loses nothing. The map back: the twenty-third result of a result with
   no filled term, "none" otherwise; it returns the original on mapped
   results; the smallest result answered "none" is one term, filled, nothing
   asserted (cost 2), the only one at that cost. Beside it, the forgetting map
   (a result to the twenty-third result of its states) answers every result
   and carries each change to a change or to none (a filling). The
   twenty-second, the ninth, the seventh and the first do not map in one to
   one (23:D9, carried through the embedding).
9. **Counts.** Two-term results recording `t` assertions with `k` filled terms:
   `2t² + t + 1`, `4t² + 2`, `2t² + t + 1` for `k = 0, 1, 2` (`t ≥ 1`; one each
   for `t = 0`); the results of every round with at most two terms in closed
   form, so the seed's 100 rounds are given by formula; three terms from the
   loops, two-way sums and sum around with the filled terms, up to rewriting;
   four and five terms by listing.

## Layout

- `research/twentyfourth/` — reading notes and scratch (not evidence).
- `code/twentyfourth/` — typed Python. Imported where a result still applies:
  the twenty-second's state, `plain`, `canonical`, changes and `perform`; the
  twenty-third's `excess_table`, `normal_table`, raising, the cost by raising
  sets (`descend`, `fewest`, `record`, `least_tables`), the sums and the
  certificate, its grouped exploration for the comparison, its counts; the
  ninth's exploration for C-E′; `xry.orbits`, `fourth.state._rewritings`; the
  writers, `compare_evidence`, the Lean report runner. Defined afresh: the
  state with filled terms, its least writing and the mark of its result;
  filling and identifying under C-I1, C-I2, C-I3; the exploration of states and
  the grouping; the balance record and the told / not told classes; the cost;
  the independent counts with filled terms; the twenty-third mapped in and the
  two maps back; reachability; the readings C-F2, C-F3, C-F4, C-I2, C-I3,
  C-E′, C-N0; the statements; a `FillCheck` dataclass whose every disagreement
  field has an injection test and a mutation in a new panel of
  `ci/check_mutation_bite.py`. Launcher `code/run_twentyfourth.py`
  (`--check`); axiom report `code/lean_report_twentyfourth.py`, refusing any
  axiom other than `propext` and `Quot.sound`.
- `tests/test_twentyfourth_*.py`.
- `lean4_core/Twentyfourth/` — a library `Twentyfourth` in the existing
  package, importing `Twentythird` (and through it `Twentysecond`); the
  lakefile gains the library and a default target, appended (recorded in
  `paper/twentysecond/change_log.md`, since the lakefile is the
  twenty-second's).
- `evidence/twentyfourth/` — generated, with `MANIFEST.sha256`.
- `paper/twentyfourth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.
- `ci/check_axiom_citations.py` lists the twenty-fourth derivation;
  `ci/check_definitional_citations.py` gains its record notion (`fill`);
  `ci/check_mutation_bite.py` its panel.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the seed (`research/twentyfourth/`)
Sentence-by-sentence diff against the twenty-third seed; the notion table with
source statuses; the readings above; which of the twenty-third's claims are
about states and changes (no change), about results (re-examined), or about
its record (re-examined against the task's first question).

### Phase 2 — `code/twentyfourth/` and `tests/`
- the state with filled terms; least writing; the mark of a result (the
  twenty-third's mark with the filled terms carried by the same rewriting); a
  check that the equivalence generated by the seed's clauses on small states
  with filled terms, found by search, is exactly the classes of the mark;
- the exploration from the empty state, bounded in terms and rounds,
  attempting every change of every state reached (fewest additions first,
  C-O); frontier; grouping into results; shortest-sequence counts; a full
  attempt log at a small bound;
- per result: the round against the cost by formula; the balance record read
  from the mark against the loops of every state of the result reached; the
  told / not told class against the certificate; the twenty-third's record;
- per change within the bound: the cost moves by at most one from a state
  asserting the fewest; filling by exactly one; parity as item 5 says;
  filling respects the sameness;
- an independent count of the results by terms, filled terms and cost (closed
  form for at most two terms, invariants for three, listing for four and
  five) as the completeness certificate; the two-term closed form against the
  count and the run;
- comparisons: the results with no filled term against the twenty-third's
  grouped exploration at the same bounds (the same results at the same
  rounds); C-E′ at a small bound; the twenty-third's record classes holding
  results kept by different numbers of terms (item 1), computed;
- the map back and its smallest "none"; the forgetting map; reachability
  against search under C-I1, C-I2, C-I3; the exchange; the readings C-F2,
  C-F3, C-F4 at a small bound;
- property witnesses for "what does not follow";
- deterministic evidence writer with `--check`; the Lean report writer.

### Phase 3 — `lean4_core/Twentyfourth/`
Targets, in order:
1. The model: a state with filled terms (`FSt`: the twenty-second's `St` and
   a filled predicate), well-formedness, the number of filled terms, the five
   changes under C-I1 (`Step24`, `Reach24`); the twenty-third's states with no
   term filled (`ofSt`) and each of their changes carried (`Step.toStep24`).
2. The sameness (`Same24`: the twenty-third's `Same3` and the same filled
   terms), an equivalence; one to one on the embedded states, at a fixed
   writing and in every writing; balance a mark of the result; filling
   respects the sameness; C-F3's outcome is C-F1's result.
3. The questions: the twenty-third's record witnesses (item 1) and "it records
   no assertion exactly for the result asserting nothing"; `told_iff` (item 2);
   every filled term balances in the result asserting nothing; the witnesses
   of each class that cannot be told.
4. The cost: the potential rises by at most one per change; the upper bound;
   the fewest changes exactly (`cost24`); filling moves it by one; the parity
   witness; no change returns a state to its own result.
5. Reachability under C-I1 (a filled term never goes away; the criterion both
   ways) and a C-I2 witness that it can; the exchange.
6. The map back (returns the original on mapped results; "none" exactly with
   a filled term; smallest "none" at cost 2, `a` filled) and the forgetting map
   (changes carried to changes or to none; what it loses).
7. Rewriting: the sameness and the cost in every writing. Attempted once; if
   it does not close, proved in the paper and marked "not in Lean".
`#print axioms` for every theorem the paper cites, in
`lean4_core/Twentyfourth/Axioms.lean`, reported by
`code/lean_report_twentyfourth.py` into
`evidence/twentyfourth/lean_axioms.txt`.

### Phase 4 — `evidence/twentyfourth/`
Generated, hashed, regenerated and compared with `--check`. Every earlier
derivation's `--check` re-run to confirm its evidence still regenerates.

### Phase 5 — `paper/twentyfourth/`
`paper.md` (findings; every use of an earlier derivation cited with its
re-check; the answers to the task's questions: whether the twenty-third's
record shows which terms keep a result from being the one asserting nothing;
which results filled terms that do not balance tell apart from a result with
nothing asserted, which they cannot, and the fewest changes to each result;
the map in, the map back, what a merge loses; which of the twenty-third's
results — cost, reachability, the exchange — hold here and where they do not;
final section: nearest known results and differences, the only place where
outside names appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit (no push).

## Stopping conditions (twenty-fourth derivation)

The run stops when AM1–AM10 hold, or when a blocker is hit.

- AM1 Every notion in `paper/twentyfourth/paper.md` has one recorded source
  status.
- AM2 Every claim in `paper/twentyfourth/claim_ledger.md` has evidence, or is
  open; the ledger has the columns ID, statement, status, evidence, axiom
  report, re-check, falsifier.
- AM3 C-F1/C-F1′/C-F2/C-F3/C-F4, C-S, C-I1/C-I2/C-I3, C-B, C-N/C-N0, C-K, C-O
  and C-E/C-E′ are kept or eliminated by a cited proof; every non-isomorphic
  result within the bound is kept.
- AM4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- AM5 `lake +leanprover/lean4:v4.33.1 -d lean4_core build` passes, its exit
  code read on its own line and not through a pipe; no `sorry`, `admit` or
  declared axiom in `lean4_core/`; the axiom report lists only `propext` and
  `Quot.sound`.
- AM6 `python code/run_twentyfourth.py --check` matches; every earlier
  derivation's evidence still regenerates byte-identically.
- AM7 Every use of an earlier result is cited and re-checked (ledger column
  "re-check": no change, re-proved, imported, or computed again).
- AM8 The prose watchlist, `ci/check_vacuous_checks.py`,
  `ci/check_definitional_citations.py`, `ci/check_mutation_bite.py` (with a
  twenty-fourth panel covering every disagreement field) and
  `ci/check_axiom_citations.py` pass; every pinned hit of the paper is in its
  final section.
- AM9 The paper states which results filled terms that do not balance tell
  apart from a result with nothing asserted, which they cannot, the fewest
  changes to each result, and which of the twenty-third's results (cost,
  reachability, exchange) hold here and where not.
- AM10 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: on terms and rounds together. Targets: 5 terms and 7 rounds, 3
  terms and 9, 2 terms and 16; the twenty-third's grouped exploration at the
  same bounds for the comparison; a full attempt log at 2 terms and 3 rounds;
  reachability among the results of 2 terms and 4 rounds under each
  identification reading; the readings at 2 terms and 6 rounds. Any run that
  does not complete in minutes here has its rounds lowered first, then its
  terms; the bounds used are declared in the paper; the frontier is exported
  exactly; completeness within the bound is certified by the independent
  count; the two-term round counts are proved in closed form for every round,
  so the seed's 100 rounds are given by formula, not listed.
- Rounds: at most 100; no change is invented.
- Lean targets 1–6 required; target 7 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `derivation/twentyfourth`; commits only, no push.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question; a tool refused
by the session's permissions. Should `lake` try to fetch anything, the build
is stopped and the Lean claims are marked open.

## How to run (twenty-fourth derivation)

From the repository root:
- `python -m pytest`, then `python code/xry/gate.py coverage.json`,
  `python -m mypy`, `python ci/check_prose_watchlist.py`,
  `python ci/check_vacuous_checks.py`,
  `python ci/check_definitional_citations.py`,
  `python ci/check_mutation_bite.py`, `python ci/check_axiom_citations.py`;
- `python code/run_twentyfourth.py` writes `evidence/twentyfourth/`;
  `python code/run_twentyfourth.py --check` compares with a fresh
  regeneration;
- `lake +leanprover/lean4:v4.33.1 -d lean4_core build`, then read the exit
  code on its own line; `python code/lean_report_twentyfourth.py` builds and
  writes `evidence/twentyfourth/lean_axioms.txt`.

---

# Twenty-fifth derivation (`prompt/twentyfifth/`) — plan and stopping conditions

Written before any other work of the twenty-fifth derivation, as
`prompt/twentyfifth/prompt.md` requires. Inputs: `prompt/twentyfifth/prompt.md`
and `prompt/twentyfifth/seed_prompt.md`. The parent is the twenty-third
(`prompt/twentythird/seed_prompt.md`, `paper/twentythird/`,
`code/twentythird/`, `lean4_core/Twentythird/`, `evidence/twentythird/`); its
own parents — the twenty-second, and through it the ninth, the seventh, the
eighth and the first — are cited through it. The twenty-fourth derivation is a
sibling started at the same time and is not an input; nor is any other
derivation. Everything above stays in force (isolation, no network, `prompt/`
untouched, `.lake/` never committed, bookkeeping rules 1–4, the
evidence-module coverage gate, the `ci/` gates). Rule 5 of this task: every
earlier result used is cited, its proof re-checked from this seed, and the
ledger's re-check column says how — *no change*, *re-proved*, *imported* (a
`lean4_core/Twentythird` or `lean4_core/Twentysecond` theorem used as it
stands, its statement mentioning nothing this seed changes), or *computed
again*. Files other derivations share (`CLAUDE.md`,
`lean4_core/lakefile.toml`, `ci/check_mutation_bite.py`,
`ci/check_axiom_citations.py`, an earlier derivation's `change_log.md`) are
only added to: nothing already there is reordered, reworded or reformatted.

## What differs in the seed

Against the twenty-third seed (`diff`): the list of the kinds of change gains
a fifth, "filling three different terms", and one sentence is added: "Three
filled terms `x`, `y`, `z` balance when, going from `x` to `y` to `z` and back
to `x`, as many assertions are written with `r` as with `s`, each counted as
often as it is asserted; for every result, record which filled terms
balance." Every other sentence is the twenty-third's, the sameness sentence
(with raising) included. So states gain what is filled, there are five kinds
of change, and every result carries a record of which of its filled terms
balance. The seed does not say what filling does beyond making three terms
filled; that silence is where the readings below come from.

## Readings

- **C-F1 (chosen). Filling.** A state carries its filled triples; filling
  three different terms of the state makes them a filled triple and changes
  nothing else. Filling a triple already filled changes nothing, so it is not
  a change (as removing what is not asserted is not, 9:C5⁗). **C-F2
  (unchosen, kept):** filling leaves the state as it was, the filled triple
  being recorded on the change only; expected (to prove) to give the
  twenty-third's results at the twenty-third's rounds.
- **C-O1 (chosen). Which way round.** A filled triple keeps the order in which
  its terms are gone round: `x, y, z` is `y, z, x` and `z, x, y` (the same way
  round), and `x, z, y` is another filled triple. Balance is read going round
  that way. Unchosen, kept and computed: **C-O2** three terms as a set,
  balancing both ways round; **C-O3** a set, balancing either way round;
  **C-O4** every starting term a different filled triple.
- **C-B1 (chosen). What is gone along.** Going from `x` to `y` goes along
  `xry` and `xsy`; the triple balances when `e(x, y) + e(y, z) + e(z, x) = 0`,
  `e` the excess `M_r − M_s` (the twenty-third's sum around three terms).
  **C-B2 (unchosen, kept, computed):** the assertions between `x` and `y`
  either way; the triple balances when the three two-way sums add up to zero.
- **C-M1 (chosen).** A triple is filled or not. **C-M2 (unchosen, computed):**
  each filling counted, like a multiplicity.
- **C-I1 (chosen). Identifying.** "Identifying two terms replaces both by one
  term": in every filled triple too; a filled triple left without three
  different terms is no longer a filled triple of three different terms and
  is dropped; two that become one are one. **C-I2 (unchosen, computed):**
  every filled triple naming either term is dropped. **C-I3 (unchosen,
  computed):** the triples left without three different terms are kept.
- **C-A (chosen). The order of attempts.** Filling adds no term and no
  assertion, so it is attempted with the changes that add nothing:
  identifications, removals in `r`, in `s`, fillings, a term, additions in
  `r`, in `s`. Unchosen: fillings last. Expected (to prove): the same results
  at the same rounds.
- **C-R (chosen). What is recorded.** The twenty-third's record (the terms,
  and the assertions in `r` and in `s` of a state asserting the fewest; a
  filled triple is neither a term nor an assertion) and, as the seed adds, the
  result's filled triples, each marked as balancing or not. Unchosen: filled
  triples counted among what a result adds to what is given (a record only).
- **The task's words.** "A result with nothing asserted on as many terms": the
  twenty-third's result asserting nothing, here with whatever triples are
  filled. "Which of its terms keep it from being the same as" that result
  (chosen): a set of terms keeps it when the result read on those terms alone
  is not the one asserting nothing on them; the terms that keep it are the
  least such sets (one term with a loop, two terms, three terms: 23:D2).
  Unchosen: every term in some such set. "Told from one that is by filled
  terms that do not balance": the records of which filled terms balance
  differ.
- **Inherited without change:** 23:C-inh, 22:C-J1, 23:C-H1 (raising touches no
  filled triple), 23:C-X (a change of a result is a change of one of its
  states), 23:C-E (explore states, form the results afterwards), the bound on
  terms and rounds (9:C8′). Each is re-checked against the added sentence.

## Expected consequences, to be proved or refuted

1. **The record is a record of the result.** The sum around a filled triple is
   kept by rewriting (which carries the filled triples), by pairs asserted
   together and by raising (23:D2), by going round from another term, and is
   negated by exchanging the two relations; so which filled triples balance is
   the same on every state of a result and survives the exchange.
2. **The twenty-third's question.** Its record (terms, assertions in `r`, in
   `s`) shows *whether* a result is the one asserting nothing (it records no
   assertion exactly then) but not *which* terms keep it from being so:
   `a b c; ara bsb`, `a b c; arb bsc` and `a b c; arb bsa` record the same
   (three terms, one assertion in each relation), and are kept by one term, by
   two terms and by three terms respectively.
3. **Told and not told.** A result asserting nothing balances every filled
   triple; so a result is told from one asserting nothing by filled terms that
   do not balance exactly when one of its filled triples does not balance.
   Not told: every result with no filled triple (all results with at most two
   terms among them); a loop is never gone along, so a result differing from
   nothing only at loops is never told; a two-way sum can be seen one way
   round and not the other (`a b c; arb`). Blind results (no filling could
   tell them): with at most two terms, all; with three and four terms, those
   whose sums around every three terms, both ways round, are zero — some with
   a non-zero two-way sum; with five terms or more, exactly those differing
   from nothing only at loops. With every loop and two-way sum zero, the filled
   triples tell every such result exactly when their sums around give every
   sum around (a rank condition on the filled triples; the triples through one
   term are enough; with four terms, any three of the four sets of three).
   What the record shows of the terms that keep a result: every filled triple
   that does not balance is such a set of terms; loops and unfilled triples
   are not shown.
4. **Fewest changes.** The twenty-third's cost plus the number of filled
   triples: `n + min_g Σ |e(x, y) + g(x) − g(y)| + |F|`. Lower bound: `phi`
   plus the filled triples rises by at most one per change; upper bound:
   additions, then the fillings.
5. **What of the twenty-third holds.** Its cost, exactly on the results with
   no filled triple; "every change changes the cost by an odd number" fails
   (identifying two terms of a filled triple: `a b c` filled, cost 4, to
   `a b`, cost 2); "no change returns a state to its own result" and "a
   change from a state asserting the fewest raises the cost by at most one"
   hold; reachability holds under C-I1 (identifying down to one term drops
   every filled triple) and fails under C-I3; the exchange holds.
6. **Mapping an earlier seed in.** The twenty-third maps one to one: a result
   with no filled triple, each of its changes carried to the same change. The
   twenty-second, the ninth, the seventh and the first do not (23:D9 through
   that map). The map back gives the twenty-third result of a result with no
   filled triple and "none" otherwise; it returns the original on every mapped
   result; the smallest result it answers "none" on is `a b c` with one filled
   triple and nothing asserted (cost 4), unique up to writing. No two
   twenty-third results are made one here, so no merge loses anything; what
   forgetting the filled triples loses (the filled triples and their record)
   is recorded.

## Layout

- `research/twentyfifth/` — reading notes and scratch (not evidence).
- `code/twentyfifth/` — typed Python. Imported where a result still applies:
  the state, `canonical`, `rewrite`, `swap`, `empty`, `excess`, `plain`,
  `written` (twenty-second, ninth), raising, the mark of a result, the sums
  around, the certificate, the cost and the states asserting the fewest
  (twenty-third), the twenty-third's exploration and counts for the
  comparison, `xry.orbits`, the writers, `compare_evidence`, the Lean report
  runner. Defined afresh: filled triples and their normal form, the state with
  filled triples, the five kinds of change, the balance record, the mark of a
  result here, the exploration of states with filled triples and the grouping
  into results, the cost, told and blind results, the rank condition on filled
  triples, the counts, the twenty-third embedded and the map back,
  reachability, the unchosen readings, the statements, and a `*Check`
  dataclass whose every disagreement field has an injection test and a
  mutation in a new panel of `ci/check_mutation_bite.py`. Launcher
  `code/run_twentyfifth.py` (`--check`); axiom report
  `code/lean_report_twentyfifth.py`, refusing any axiom other than `propext`
  and `Quot.sound`.
- `tests/test_twentyfifth_*.py`.
- `lean4_core/Twentyfifth/` — a library `Twentyfifth` in the existing package,
  importing `Twentythird` (and through it `Twentysecond`); the lakefile gains
  the library and the default target (added only; recorded in
  `paper/twentysecond/change_log.md`, the lakefile being the twenty-second's).
- `evidence/twentyfifth/` — generated, with `MANIFEST.sha256`.
- `paper/twentyfifth/` — `paper.md`, `claim_ledger.md`, `change_log.md`.
- `ci/check_axiom_citations.py` lists the twenty-fifth derivation.

## Plan

### Phase 0 — this section, committed alone.

### Phase 1 — reading the seed (`research/twentyfifth/`)
Sentence-by-sentence diff against the twenty-third seed; the notion table with
source statuses; the readings above; which of the twenty-third's claims are
about states and changes of the four kinds (no change or imported), about its
results (re-examined), or about its cost and record (re-proved or refuted).

### Phase 2 — `code/twentyfifth/` and `tests/`
- filled triples, the state, the five kinds, identifying under C-I1; the mark
  of a result (the twenty-third's normal table with the filled triples, least
  over the rewritings); balance and the record; a check that balance is the
  same on every state of a result reached;
- the exploration: states (plain state and filled triples, least writing)
  explored from the empty state, every change fewest additions first, bounded
  in terms and rounds, grouped into results afterwards; the round of a result
  against its cost by formula; the frontier; a full attempt log;
- per change within the bound: the cost moves as the formula says; a change
  from a state asserting the fewest raises it by at most one; the witnesses of
  the parity failure;
- an independent count of the results by terms and cost (tables of excesses
  and sets of filled triples, grouped by the mark, not by the exploration);
  with at most two terms the twenty-third's closed form;
- told and blind: on every result reached, told exactly when a filled triple
  does not balance; the blind results with three, four and five terms listed
  and checked against their description; the rank condition on the sets of
  filled triples up to rewriting (exact rational arithmetic), checked against
  a search over small excesses;
- the twenty-third's question: its records against the least sets of terms
  that keep a result, on every twenty-third result of a run;
- the twenty-third embedded: its results within the bound are exactly the
  results with no filled triple, at the same rounds; the map back and its
  smallest "none"; the seventh's pair still merged;
- reachability against search (C-I1, and C-I3 at a small bound); the exchange;
- the unchosen readings C-F2, C-O2, C-O3, C-O4, C-B2, C-M2, C-I2, C-I3 and the
  order of attempts at a small bound;
- property witnesses for "what does not follow";
- deterministic evidence writer with `--check`; the Lean report writer.

### Phase 3 — `lean4_core/Twentyfifth/`
Targets, in order:
1. The model: filled triples (three terms, the way round), their normal form
   (starting from the least term), the state (`St` and its filled triples),
   well-formedness, the five operations, `Step25`, `Reach25`; well-formedness
   kept; the twenty-third's states embedded with no filled triple, every change
   carried to the same change.
2. Balance: the sum around a filled triple kept by going round from another
   term, by the twenty-third's sameness (imported `Same3.around`), negated by
   the exchange; the sameness here; the record the same on every state of a
   result; a result asserting nothing balances every filled triple; told
   exactly when a filled triple does not balance; the witnesses: a loop never
   seen, a two-way sum seen one way round, a blind result with three terms and
   a non-zero two-way sum; with five terms or more, blind only at loops; with
   loops and two-way sums zero, the triples through one term decide.
3. The cost: the twenty-third's cost plus the filled triples (both bounds);
   the parity failure; a change from a state asserting the fewest raises it by
   at most one; no change returns a state to its own result.
4. The twenty-third's question: the three witnesses record the same and are
   kept by one, two and three terms; the record shows whether a result is the
   one asserting nothing.
5. Mapping: the embedding one to one and carrying changes; the other seeds of
   the line not one to one (through the twenty-third's witnesses); the map
   back, what it returns on mapped results, its smallest "none".
6. Reachability (the criterion re-proved with filled triples) and the
   exchange.
7. Rewriting filled triples: the full sameness in every writing, the cost in
   every writing, the embedding one to one in every writing. Attempted once;
   if it does not close, proved in the paper and marked "not in Lean".
`#print axioms` for every theorem the paper cites, in
`lean4_core/Twentyfifth/Axioms.lean`, reported by
`code/lean_report_twentyfifth.py` into `evidence/twentyfifth/lean_axioms.txt`.

### Phase 4 — `evidence/twentyfifth/`
Generated, hashed, regenerated and compared with `--check`. Every earlier
derivation's `--check` re-run to confirm its evidence still regenerates.

### Phase 5 — `paper/twentyfifth/`
`paper.md` (findings; every use of an earlier derivation cited with its
re-check; the answers to the task's questions: whether the twenty-third's
record shows which terms keep a result from being the one asserting nothing,
which results filled terms that do not balance tell from one asserting nothing
and which they cannot, the fewest changes to each result, the mapping, the map
back and what a merge loses, and which of the twenty-third's results — cost,
reachability, exchange — hold here and where they do not; final section:
nearest known results and differences, the only place where outside names
appear), `claim_ledger.md`, `change_log.md`.

### Phase 6 — audit against "Done", commit (no push).

## Stopping conditions (twenty-fifth derivation)

The run stops when AN1–AN11 hold, or when a blocker is hit.

- AN1 Every notion in `paper/twentyfifth/paper.md` has one recorded source
  status.
- AN2 Every claim in `paper/twentyfifth/claim_ledger.md` has evidence, or is
  open; the ledger has the columns ID, statement, status, evidence, axiom
  report, re-check, falsifier.
- AN3 C-F1/C-F2, C-O1–C-O4, C-B1/C-B2, C-M1/C-M2, C-I1–C-I3 and the order of
  attempts are kept or eliminated by a cited proof; every non-isomorphic
  result within the bound is kept.
- AN4 `python -m pytest` passes; `python code/xry/gate.py coverage.json`
  reports ≥ 95 % line and ≥ 95 % branch over all of `code/` and every
  evidence module fully covered; `python -m mypy` passes.
- AN5 `lake +leanprover/lean4:v4.33.1 -d lean4_core build` passes, its exit
  code read on its own line; no `sorry`, `admit` or declared axiom in
  `lean4_core/`; the axiom report lists only `propext` and `Quot.sound`.
- AN6 `python code/run_twentyfifth.py --check` matches; every earlier
  derivation's evidence still regenerates byte-identically.
- AN7 Every use of an earlier result is cited and re-checked (ledger column
  "re-check": no change, re-proved, imported, or computed again).
- AN8 The prose watchlist, `ci/check_vacuous_checks.py`,
  `ci/check_definitional_citations.py`, `ci/check_mutation_bite.py` (with a
  twenty-fifth panel covering every disagreement field) and
  `ci/check_axiom_citations.py` pass; every pinned hit of the paper is in its
  final section.
- AN9 The paper states which results filled terms that do not balance tell
  apart from a result with nothing asserted and which they cannot, the fewest
  changes to each result, and which of the twenty-third's results (cost,
  reachability, exchange) hold here and where not.
- AN10 Shared files were only added to (checked with `git diff` before each
  commit that touches them).
- AN11 `git status` clean; `prompt/` unchanged; `.lake/` untracked.

Bounded effort:
- Bounds: planned 4 terms with 7 rounds, 3 terms with 9 rounds, 2 terms with
  24 rounds (no filling is possible there: the twenty-third's two-term
  results), and 5 terms with 7 rounds if it completes in minutes; a full
  attempt log at 3 terms and 5 rounds (the smallest bound with a filling);
  reachability among the results of 3 terms and 5 rounds; the unchosen
  readings at 3 terms with 6 rounds; the rank condition on every set of
  filled triples up to rewriting with at most 5 terms. Any run that does not
  complete in minutes here has its rounds lowered first, then its terms; the
  bounds used are declared in the paper; the frontier is exported exactly;
  completeness within the bound is certified by the independent count.
- Rounds: at most 100; no change is invented.
- Lean targets 1–6 required; target 7 attempted once.
- At most two review passes over paper and ledger after the first draft.
- Branch: `derivation/twentyfifth`; commits only, no push.

Blockers (stop and report): anything that would need the network, a file
outside the repository, a change to `prompt/`, or a question; a tool refused
by the session's permissions. Should `lake` try to fetch anything, the build
is stopped and the Lean claims are marked open.

## How to run (twenty-fifth derivation)

From the repository root:
- `python -m pytest`, then `python code/xry/gate.py coverage.json`,
  `python -m mypy`, `python ci/check_prose_watchlist.py`,
  `python ci/check_vacuous_checks.py`,
  `python ci/check_definitional_citations.py`,
  `python ci/check_mutation_bite.py`, `python ci/check_axiom_citations.py`;
- `python code/run_twentyfifth.py` writes `evidence/twentyfifth/`;
  `python code/run_twentyfifth.py --check` compares with a fresh
  regeneration;
- `lake +leanprover/lean4:v4.33.1 -d lean4_core build`, then read the exit
  code on its own line; `python code/lean_report_twentyfifth.py` builds and
  writes `evidence/twentyfifth/lean_axioms.txt`.
