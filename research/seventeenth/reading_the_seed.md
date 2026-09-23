# Reading the seventeenth seed against the base

Working notes for the seventeenth derivation (Phase 1). Nothing here is cited
as evidence. Every notion is exactly one of **given**, **chosen**, **derived**,
**computed**, **refuted**, **open**. Statuses marked *expected* are what Phase
2 and Phase 3 have to prove or refute; they are not yet claims.

Inputs: `prompt/seventeenth/prompt.md`, `prompt/seventeenth/seed_prompt.md`.
Parent: `prompt/seed_prompt.md`, `paper/paper.md`, `code/xry/`,
`lean4/H3V7N5QF/`. The sixteenth derivation is not the parent.

## The diff

`prompt/seventeenth/seed_prompt.md` against `prompt/seed_prompt.md`: one
bullet is deleted, nothing else.

    - For no term `x` may `xrx` be asserted.

The obstruction paragraph is unchanged, character for character. So a change
that makes some `xrx` asserted is still obstructed and must still be answered.

## Sentence by sentence

### Terms, assertions, what is given

Terms are written with letters. An assertion is written `xry`. Given: `arb`
is asserted. Whether `bra` is asserted is not given. **Given** (base G1–G3,
G5). The base's G4 is **refuted** as a given: the sentence is not in this
seed. "No `xrx`" is no longer a rule for every state.

### Four kinds

A change is exactly one of identifying two terms, removing an assertion,
adding a term, adding an assertion. Nothing else is a change. Identifying
replaces both by one term in every assertion. **Given** (base G6, G7). The
base's C5 (what is not a change) is kept: it does not use the ban.

### Obstruction

A change that makes some `xrx` asserted is obstructed. **Given** (base G8).
What "makes" covers is not fixed by the sentence once a state may already
assert `xrx`. Two readings, both kept:

- **M1** (chosen; the base's C7, and `xry.changes.obstruction`). The
  obstruction is the assertions that would become some `xrx`: for identifying
  `x` and `y`, those of `xry`, `yrx` that are asserted; for adding `xrx`,
  that assertion. An `xrx` already asserted does not obstruct an unrelated
  change.
- **M2** (unchosen, kept). A change is obstructed when its outcome asserts
  some `xrx`, whether the change just made it or it was already there.

*Expected.* On a state that asserts no `xrx`, M1 and M2 name the same
changes. The direction "related, hence the outcome asserts `xrx`" is the
base's `image_loop_iff` and does not use `Legal`. The converse, on a
loop-free state, is the base's `identification_obstructed_iff` with
loop-freeness of that state in place of the ban. On a state that asserts
`ara`, identifying two other terms with nothing between them is obstructed
under M2 and not under M1 (witness, to be computed).

### Answers

An obstructed change must be answered: remove the obstruction, or build
structure by further changes; declare which; record the change, the
obstruction, and the answer. A refused change is recorded and changes
nothing. **Given** (base G9, G10). The base's C7 fixed one reading and
dropped another because no state may hold `xrx`. The ban is gone, so both
readings are kept:

- **A-replace** (the base's C7). The obstructed change is not entered.
  Refusal changes nothing. Removing the obstruction is those removals, then
  the change. Building is additions only, as in `xry.changes.answers`. The
  exploration is `xry.explore`.
- **A-perform** (dropped by the base, kept here). The obstructed change is
  performed and its outcome is a result, then answered. Refusal still does
  not perform the change.

*Expected.* Under A-replace, from either beginning, every result asserts no
`xrx`. The predicate `has_xrx` is false on every reached result. The
obstruction rule reconstructs the ban's irreflexivity only together with
"do not enter an obstructed change". The base's results, rounds, and cost
survive on that set.

*Expected.* Under A-perform, `has_xrx` is true. Adding `ara` to what is
given, and identifying `a` with `b` while `arb` is asserted, each produce an
outcome that asserts `xrx`. Those outcomes were not results under the ban
(`Step.addAssertion` requires `x ≠ y`; `Step.identify` requires the two
terms unrelated; `St.Legal` forbids the diagonal). They are valid now
("any outcome is valid").

*Expected.* Remove-first and perform-first identifications end at the same
state (the base's `remove_obstruction_first_or_last`, which must be
re-checked). Only the perform-first path has an `xrx` in between. The base
theorem no longer shows that the intermediate is not a result.

*Expected.* The base cost is not a lower bound under A-perform. Identifying
`a` with `b` in what is given is one change. The outcome is one term
asserting `ara`. `xry.cost.cost` returns 3 without `bra` and 4 with `bra`
(size 2, destroyed givens `1 + m0`, given size `2 + m0`). One is not at
least that.

### Beginnings

What is given has the terms `a` and `b`, `arb` asserted, `bra` or not.
**Chosen** (base C2). The base's support for ignoring `ara` and `brb` was
that the ban forbade them. That support is gone. Unchosen, kept: a beginning
that also asserts `ara` or `brb`.

*Expected.* Under A-replace those beginnings are not results of the chosen
one (adding `xrx` is not entered). Under A-perform they are one addition
away. Both are computed.

### Sameness, rounds, bound

Two results that differ only in how their terms are written are the same
result. **Given** (base G12). Both readings of the base's C4 are kept
(ANCHORED and FREE). Rounds and the term bound are the base's C6 and C8,
applied to both explorations. **Chosen**, same words. 100 changes, no
invented change, frontier if the run is cut short. **Given** (base G13).
Any outcome is valid. **Given** (base G14). This sentence is what lets an
outcome that asserts `xrx` stand, once the ban is not there to withdraw it.

### What the base used the ban for

| Base claim | Rested on the ban? | Expected here |
|---|---|---|
| `Legal` as a filter on states | yes (G4) | not a given; `LoopFree` is a predicate |
| `given_distinct` (`a ≠ b`) | yes (`Legal`) | survives under A-replace, fails under A-perform |
| `adding_xrx_always_obstructed` | no (`¬ Legal` of the outcome) | survives, and does not by itself bar the outcome |
| `Step` (no diagonal, no related identification) | yes (the constructors) | the unobstructed fragment survives; A-perform adds the other steps |
| `Step.legal` | yes (hypothesis `Legal`) | re-proved as "unobstructed step from a loop-free state stays loop-free" |
| cost formula | the paths stay in `Legal` | survives under A-replace; not a lower bound under A-perform |
| `arb` gone once `a` and `b` are one term | the merged state may not assert `xrx` | survives under A-replace; the perform-first merge asserts `ara` |
| orbit count of legal states | counts states with no diagonal | the A-replace certificate; A-perform counts the diagonal too |
| D10, answers reach nothing new | the obstructed outcome is not a result | survives under A-replace only |

## What does not follow (expected witnesses)

- Every well-formed state asserts no `xrx`. Holds of every A-replace result;
  fails of the one-term state asserting `ara`.
- A-replace and A-perform have the same results. They do not: that state is
  in one and not the other.
- M1 and M2 disagree on a loop-free state. They do not, if the expected
  agreement is proved; they do disagree once `ara` is asserted.
- The base cost is the fewest changes once an obstructed change is performed.
  It is not, on the identification witness.
