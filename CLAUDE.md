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
