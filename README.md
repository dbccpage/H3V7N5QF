# H3V7N5QF

Genesis-Ongoing: 25 blind finite derivations from small edits of one seed,
each recording what follows and what does not.

Each derivation starts from a short seed about terms, assertions `xry` and a
fixed list of changes. It is carried out blind: only this repository is used,
the body of each paper uses only the seed's words, and nothing is steered
toward a known theory. Every notion is recorded as given, chosen, derived,
computed, refuted or open. Every alternative that is not eliminated by a proof
is kept. The results are Python computations written to `evidence/`, Lean 4
theorems with `#print axioms` reports, and a claim ledger per derivation that
names, for each claim, its evidence and what would falsify it.

---

## Part of a three-repository programme

This is the second of three public repositories by the same author. They use
different methods and make different kinds of claim. This section says how
they connect, and where the connection is a recorded gap and not a
derivation.

| Repository | Role |
|---|---|
| [**19L57G1**](https://github.com/dbccpage/19L57G1), Genesis | A blind, sealed, finite derivation from an opaque seed, and the point where it stops: the minimum response is tied across readings L and F. |
| **H3V7N5QF** (this repository), Genesis-Ongoing | 25 further blind derivations, each from its own seed, on terms, assertions and a short list of changes: obstruction and answer, fewest changes, counted assertions, two relations, an admission gate, and three operator-targeted climbing rounds. |
| [**theory_of_finite_quantum_mechanics**](https://github.com/dbccpage/theory_of_finite_quantum_mechanics), finite QM | A derivation graph of 880 nodes in 34 stages. It starts from the inert inscription `<>`, passes through Pre-Genesis, Genesis, S(n) and MSS-N, the witnessed-difference programme (WDP), L1 and L1 to L2, and asks how far finite exact constructions reach toward finite QM. Every node carries a status and an evidence grade E0 to E4. |

**How this repository relates to Genesis.** It continues the method, not the
code. It shares the bookkeeping discipline, the claim ledger with falsifiers,
local gates, and a prose-watchlist gate that was ported from 19L57G1
(`paper/second/change_log.md`, item 15). Its code and Lean do not import
19L57G1. The seed is a different one. A comparison of the two event languages
is in `meta/immune_system/genesis_correspondence.md`, outside any derivation.
It is a table of chosen analogies, refuted identifications and open bridges,
and it identifies nothing.

**How it connects to finite QM.** At finite QM commit `5bb9635` (2026-10-22),
16 nodes of the derivation graph cite this repository. 14 are in the GENESIS
stage, 1 is in COMPUTATION and 1 is in WDP. 12 are `PROVED_LEAN`, 2 are
`OPEN`, 1 is `COMPUTATIONALLY_CHECKED` and 1 is `DEFINITION`.

| Finite QM node | Status | What it records |
|---|---|---|
| `PG-GEN-IRREFLEXIVE-DISTINCT` | `PROVED_LEAN` | First: `a` and `b` are two terms, and `bra` is independent. |
| `PG-GEN-ONGOING-OBSTRUCTION` | `PROVED_LEAN` | First: exactly two kinds of change are obstructed. |
| `PG-GEN-ONGOING-FEWEST-CHANGES` | `PROVED_LEAN` | First: the closed formula for the fewest changes. |
| `PG-GEN-REWRITING-COMMUTATION` | `PROVED_LEAN` | Lean in the second derivation's library: changes commute with injective rewriting of terms. |
| `PGW-GO-REACH-CEILING` | `PROVED_LEAN` | First: every finite legal state with a term is a result. |
| `PGW-GO-CONTRACTION-STEP2-STEP3` | `PROVED_LEAN` | Second and third: striking changes from the base seed. |
| `PGW-GO-MULTIPLICITY-MONOTONE` | `PROVED_LEAN` | Fourth: counted assertions never fall along a sequence. |
| `PGW-GO-TWO-RELATIONS-SWAP` | `PROVED_LEAN` | Eighth and ninth: a second relation, and the exchange of the two. |
| `PGW-GO-LEFTOVER-UNBOUNDEDNESS` | `PROVED_LEAN` | Tenth and sixteenth: admitting a recorded leftover does not terminate. |
| `PGW-GO-ADMISSION-GATE` | `DEFINITION` | Fifteenth: reaching a result does not admit it. |
| `PG-GEN-SAMENESS-REFINEMENTS` | `COMPUTATIONALLY_CHECKED` | Sameness readings: excess, plain and together arrays, cancellation cost, bounded two-term rewriting orbits. |
| `PGW-GO-H1-CANCELLATION-EXCESS` | `PROVED_LEAN` | Twenty-second (climbing round H1). |
| `PGW-GO-H2-STATE-RAISING-GAUGE` | `PROVED_LEAN` | Twenty-third (climbing round H2). |
| `PGW-GO-H3-TWIN-FILLS-HOLONOMY` | `PROVED_LEAN` | Twenty-fourth and twenty-fifth (climbing round H3). |
| `COMP-C2-STEP3-NOT-WORD-STEP` | `OPEN` | No word encoding of the second derivation's states (its `Step3`) under which each move is a word step is proved or claimed. |
| `PGW-WDP-BRIDGE-ONGOING-TO-WINDOW` | `OPEN` | The step from the climbing rounds into the WDP window is a recorded gap. |

The route from the H3 node into `PGW-WDP-BRIDGE-ONGOING-TO-WINDOW` is
`GAP_NO_DERIVATION`. None of the 25 papers states a derivation of a Born
rule, a complex field, an inner product or any other structure of finite QM.
The
finite QM graph cites this repository by a sibling path and not by a pinned
commit. 14 of the 16 nodes are grade E0 in finite QM's evidence map, which
means that map's checkout has no counted evidence file for them. Mostly that
is because the Lean and code they cite are here, not there. A name check of the 45 Lean references
finds 42 whose file exists here and whose last name component occurs in it.
That is a citation check. It is not a replay of the Lean and not a review that
each theorem states its node's claim. The other three cite
`lean4/Second/Rename.lean` under names that do not occur in this repository.

Finite QM [README](https://github.com/dbccpage/theory_of_finite_quantum_mechanics#readme)
and [evidence map](https://github.com/dbccpage/theory_of_finite_quantum_mechanics/blob/main/docs/evidence/README.md).
Its status page is built by a workflow in that repository for GitHub Pages and
is not published yet; [`docs/index.md`](https://github.com/dbccpage/theory_of_finite_quantum_mechanics/blob/main/docs/index.md)
there is its source.

This section is navigation for readers. It is not an input to any derivation,
and no derivation's seed, plan or paper refers to it.

---

## The first derivation

`prompt/seed_prompt.md` is the whole input, and it is short:

* Terms are written with letters. An assertion is written `xry`.
* Given: `arb` is asserted, and for no term `x` may `xrx` be asserted.
  Whether `bra` is asserted is not given.
* A change is exactly one of: identifying two terms, removing an assertion,
  adding a term, adding an assertion.
* A change that makes some `xrx` asserted is obstructed. It must be answered
  by removing the obstruction or by building structure, and the change, the
  obstruction and the answer are recorded. A refused change is recorded and
  changes nothing.
* Attempt every change, fewest additions first, for 100 changes along each
  alternative. If the alternatives exceed what can be completed, declare a
  finite bound, export the exact frontier and prove what is complete within
  it. Any outcome is valid.

`paper/paper.md` section 0 states what followed, each item with its source
status in the ledger:

1. `a` and `b` are two terms. Whether `bra` is asserted is independent of what
   is given. There are exactly two legal states containing `arb`, and each is
   one change from the other. Both are kept.
2. Exactly two kinds of change can be obstructed: adding `xrx`, and
   identifying `x` and `y` while `xry` or `yrx` is asserted.
3. However obstructed changes are answered, the results are the same. The
   protocol of obstruction and answer adds records, not results.
4. The results are all finite legal states with at least one term. So a
   statement about the asserting holds in every result only if it holds in
   every finite legal state.
5. The fewest changes to a result is given by a closed formula, proved in
   Lean: terms plus assertions of the result, minus those of what is given,
   plus two for each given that the result has destroyed.
6. Identifying `a` and `b` cannot be undone.
7. 100 rounds cannot be listed. The declared bound is at most 5 terms under
   any rewriting and 4 terms with the names kept. Within it the exploration is
   complete, certified by an independent count, and the frontier is exported.

## The 25 derivations

Each later seed is an edit of an earlier one, and each derivation has its own
`prompt/<ordinal>/`, `code/<ordinal>/`, `tests/`, Lean library,
`evidence/<ordinal>/` and `paper/<ordinal>/` with `paper.md`, `claim_ledger.md`
and `change_log.md`. The title in the table is the paper's own heading. Of the
Lean libraries, those for derivations 1 to 21 are in `lean4/` (Mathlib), and
those for derivations 22 to 25 are in `lean4_core/` (no dependency). The first
is `lean4/H3V7N5QF/`.

| # | Paper title |
|---|---|
| 1 | What follows from `arb`, no `xrx`, and four kinds of change |
| 2 | What follows from `arb`, no `xrx`, and three kinds of change |
| 3 | What follows from `arb`, no `xrx`, and two kinds of change |
| 4 | What follows from `arb` once, no `xrx`, and assertions that are counted |
| 5 | What follows from `arb` once, no `xrx`, counted assertions, and four kinds of change |
| 6 | What follows from `arb` once, counted assertions, four kinds of change, and nothing forbidden |
| 7 | What follows from nothing: counted assertions, four kinds of change, and an empty beginning |
| 8 | What follows from `arb` once with a second relation `s`: counted assertions, four kinds of change, nothing forbidden |
| 9 | What follows from nothing with two relations: counted assertions, four kinds of change, and an empty beginning |
| 10 | What follows once every change records a leftover |
| 11 | What follows once a writing can collide terms it does not identify |
| 12 | What follows once identifying keeps a per-relation record |
| 13 | What follows once a coarser writing forgets which relation asserted |
| 14 | What follows once leftover is a writing that is not an assertion |
| 15 | What follows once reaching a result does not make it admitted |
| 16 | What follows once a recorded leftover feeds back into the state |
| 17 | What follows when `xrx` is not forbidden, and is still obstructed |
| 18 | What follows when a different writing is a different result |
| 19 | Identification in one chosen assertion |
| 20 | Fewest total changes first |
| 21 | An obstructed change is refused |
| 22 | Two relations, nothing given, and a pair asserted in both relations taken out: what follows |
| 23 | Two relations, nothing given, pairs asserted together taken out, and raising: what follows |
| 24 | Two relations, nothing given, raising, and filled terms: what follows |
| 25 | Two relations, nothing given, raising, and filled triples that balance: what follows |

Derivations 22 to 25 are the climbing track (rounds H1, H2 and the twin
rounds of H3). `meta/climbing/` holds the rubric, the frozen extension class
and the rulings. Every climbing seed was chosen by an operator with a target
in view, so their results are graded "blind (operator-targeted)".

## What is in it

The numbers below are counted from the tracked files at commit `9da2019`
(2026-10-17). They are inventory counts, not pass results.

| | |
|---|---|
| Derivations | 25: 25 seeds and tasks under `prompt/`, 25 papers, 25 claim ledgers, 25 change logs under `paper/` |
| Python | 318 files under `code/` (the package `code/xry`, one package per later derivation, and the generate, run and Lean-report launchers); 167 test files under `tests/`, 1150 tests collected |
| Lean 4 | 179 modules: 134 in `lean4/` (21 libraries, derivations 1 to 21) and 45 in `lean4_core/` (4 libraries, derivations 22 to 25) |
| Evidence | 646 files under `evidence/`, regenerated by `code/generate*.py` and `code/run_*.py` |
| Axioms | 2212 axiom reports in the 25 `evidence/**/lean_axioms.txt` files: 154 use no axiom, 143 use `propext`, 618 use `propext` and `Quot.sound`, and 1297 also use `Classical.choice`. No other axiom appears. |
| Gates | 5 scripts under `ci/`, described in `ci/OEWAS_GATES.md` |
| Outside the derivations | `research/` (56 files, not cited as evidence) and `meta/` (384 files, fenced review and proposal area) |

The 1297 reports that use `Classical.choice` are all in derivations 1 to 21.
The reports of derivations 22 to 25 (716 of the 2212) stay within
`{propext, Quot.sound}`.

## Reading order

* **A derivation's result** is `paper/<ordinal>/paper.md` (`paper/paper.md`
  for the first). Section 0, "Findings in brief", lists what follows. The
  final section, "Nearest known results, and how the findings differ", is the
  only place the paper names outside results.
* **The evidence for a claim** is `paper/<ordinal>/claim_ledger.md`. It lists
  each claim's ID, statement, status, evidence, axiom report and what would
  falsify it.
* **Why a thing was done** is `paper/<ordinal>/change_log.md`.
* **The contract** is `CLAUDE.md`. Each derivation's plan and stopping
  conditions were written before its other work, and each is a section of that
  file. `AGENTS.md` points to it.

## How to verify

Toolchains: Python with `pytest`, `pytest-cov`, `coverage` and `mypy`
(`pyproject.toml` is tool configuration only, nothing is installed from it),
and Lean `leanprover/lean4:v4.33.1` through [elan](https://github.com/leanprover/elan).
`lean4/` pins Mathlib at revision `0df444a360eaa60ab8c11dca51a86af692955474`;
`lean4_core/` has no dependency. Name the toolchain on every `lake` call, as
below, so that elan's default toolchain does not start rebuilding the shared
dependencies.

From the repository root:

```powershell
python -m pytest                              # tests with the combined 95% coverage floor
python code/xry/gate.py coverage.json         # line and branch rates, separately
python -m mypy                                # strict
python code/generate.py --check               # evidence/ matches a fresh regeneration
python code/run_twentyfifth.py --check        # the same, for the 25th; each derivation has its own
python ci/check_prose_watchlist.py            # outside words, by digest
python ci/check_vacuous_checks.py
python ci/check_definitional_citations.py
python ci/check_mutation_bite.py
python ci/check_axiom_citations.py
lake +leanprover/lean4:v4.33.1 -d lean4_core build      # derivations 22 to 25
lake +leanprover/lean4:v4.33.1 -d lean4 build           # derivations 1 to 21; fetches Mathlib
python code/lean_report_twentyfifth.py        # builds and rewrites the axiom report
```

`pytest` writes `coverage.json` through its configured options. The last
recorded results are in `paper/twentyfifth/change_log.md`, item 14: 1102 tests
passed, 99.83% line and 99.70% branch coverage, and every derivation's
`--check` exited 0. Those were local runs at the twenty-fifth derivation. They
were not re-run for this README, and the 1150 collected today is a different
count at a later commit.

The `ci/` gates exist because green coverage, typing and `lake build` can
coexist with an overclaiming paper. `ci/OEWAS_GATES.md` says what each gate
catches and what it cannot see. A gate is accepted only after it has failed on
the exact defect it targets and recovered when the defect was removed
(`tests/test_oewas_gates.py`).

There is no hosted CI for the derivations. The one workflow,
`.github/workflows/next-ten.yml`, runs on pull requests that touch
`meta/next_ten/`. A green result anywhere else is a local receipt.

## What this does not claim

* **No bridge to a known theory.** The papers use the seed's words. Each
  paper's final section names the nearest known results and how the findings
  differ. A name there is a comparison, not a derivation.
* **A theorem is about the chosen reading.** Where a seed is silent, a
  reading was chosen and the unchosen readings are listed, and where two
  readings give different results both are computed. A Lean theorem states
  something about the chosen model, and the ledger says which.
* **Counts hold within declared bounds.** Where the alternatives exceed what
  can be completed, a finite bound is declared and what is complete within it
  is proved. Beyond it the status is open.
* **Blindness is the operator's attestation.** Derivations 1 and 2 ran under
  enforced denial of network tools. Derivations 3 to 21 were isolated by
  instruction only, and a history leak in the first climbing round was found
  and repaired afterwards. `meta/climbing/blindness.md` records what could
  reach a run, what was repaired and what was left as found.
* **The climbing rounds do not show independent arrival.** Their seeds were
  chosen with a target in view. No paper and no file here claims that this
  repository reached any outside structure on its own.
* **`meta/` is not evidence.** It analyses the finished derivations and
  proposes future seeds. Its vocabulary is not an input to any derivation, and
  a row there is not an inherited theorem. `research/` is likewise not cited as
  evidence.
* **Gates prove receipts, not payloads.** A passing gate says what a command
  printed. It does not say the mathematics matches the prose; the ledger's
  falsifier column and the review in `meta/review/` address that.
* **Nothing here derives finite QM.** See the first section.

`prompt/` is never modified after a derivation starts, and `.lake/` is never
committed.
