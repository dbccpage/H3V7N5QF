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
