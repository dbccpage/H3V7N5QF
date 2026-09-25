# The climbing track: rubric for proposing a rung

**Status:** chosen, outside the derivational seal, adopted 2026-09-24. It
governs which seed an operator may propose for the climbing track. It binds
no run: a run is bound by `CLAUDE.md` and its own `prompt.md`, and the
packet writes every rule a run must follow into that prompt. It is not a
theorem, and a rung that meets it proves nothing by meeting it.

## Why a second rubric

`meta/next_ten/rubric.md` scores edits on seven weighted axes. Three of
them (bounded computability, re-check economy and Lean feasibility) favour
edits that leave the states alone. Together with its rule that a seed uses
only its parent's words, this ranked the two candidates that would add a
new kind of state 22nd and 25th of 27, and neither entered the top ten
under any of the ±50 % weight changes. The record of the twenty-one
derivations points the other way:

- **Edits that changed the states or the steps opened new structure.** The
  fourth (multiplicity), the eighth (a second relation) and the sixteenth
  (admitted leftovers) each carry 125 to 149 Lean theorems and a new
  invariant: a count that never falls, the exchange of the two relations,
  growth without bound.
- **Edits that only kept a record beside the state did not.** The tenth
  through fifteenth have 27 to 34 theorems each. Their step relation is the
  ninth's, most of their theorems hold by definition, and review narrowed
  every one of those papers.

This track therefore has no weighted score. A proposed rung either meets
L1 to L5 below before launch, or it is not proposed. L6 follows the merge.

## The rule for one rung

**L1. One demand, in the parent's words.** A rung supplies exactly one
demand: something the parent seed's calculus cannot do. It is written in
the parent seed's own words, either as one seed sentence or as one question
in `prompt.md`. It names neither the answer nor any outside structure, and
it presupposes nothing. The twenty-first prompt's "how much smaller the
reachable set becomes" is the example of what is refused.

**L2. Exhaustion at the parent's level, by an invariant.** Before anything
is installed, the rung cites or proves that the parent's own changes cannot
meet the demand, by an invariant: a quantity every change moves in a known
way. The proof is in Lean. A bounded search that finds nothing is not
exhaustion. It is reported as *budget*, never as a proof that the demand
cannot be met.

**L3. The smallest member of a frozen extension class.** The added or
replaced sentences are the smallest member of an extension class that meets
the demand. The class is frozen (its SHA-256 is committed) before the rung's
seed is written. "Smallest" means the fewest sentences, then the fewest new
words. Unlike the demand, an extension sentence may add a word the parent
lacks, and it defines each such word where it adds it. Tied members are
all kept and run as sibling derivations on one
branch, as the nineteenth to twenty-first were. A member installed for any
other reason carries the record "not the smallest; chosen by the operator".
The class is an operator's input; it is recorded as *chosen*, and nothing
may claim that it was derived.

**L4. The states or the steps change.** Every added or replaced sentence
changes the states, the steps, or which results are the same, and the packet
names a witness: a new state, a new step, or two parent results that become
one. A sentence that only keeps a record beside the state is refused on this
track.

**L5. Lean with the small axiom set and no outside library.**

- Each rung's Lean lives in its own Lake package, `lean4_core/`, with no
  `require`. Each rung adds one library to it. Nothing is fetched, and no
  `.lake/` directory is shared with another checkout.
- Every theorem the paper cites has a `#print axioms` report that lies
  within `propext` and `Quot.sound`: no `Classical.choice`, no `sorry`, no
  `admit`, and no declared axiom. The rung's report writer refuses anything
  else. It does not reuse `code/xry/leanreport.py`, which accepts
  `Classical.choice`.
- The parents' Lean imports an outside library, so a parent result the rung
  uses is re-proved in `lean4_core/`, not imported. The ledger's re-check
  column says "re-proved".
- **The rung pair.** Every rung proves in Lean:
  1. *an embedding*: a map from the states of a named earlier seed into the
     rung's states that is one-to-one and carries steps to steps;
  2. *a read-back*: a map from the rung's states to that seed's states that
     may answer "none". Reading back an embedded state returns it. At least
     one rung state reads back to "none", and the rung names the smallest
     such state as its witness.

  If the rung makes parent results the same, it also records what each
  merge loses.

**L6. Ablation after the merge.** Once the rung has merged, strike or revert
each sentence of the new seed in turn and rerun the bounded exploration.
Record which kinds of result survive: exact, survivor, open or budget. This
is computed and cheap, and it is what this repository is for.

## The rung record

Each rung fills `meta/climbing/<rung>/record.md` after its run, with an
evidence path for every field:

| field | content |
|---|---|
| source | the earlier seed the pair of maps runs to |
| protected distinctions | what the embedding keeps apart (L5, map 1) |
| same-level attempts | the parent's changes, exhausted by the invariant of L2 |
| residual | the demand the parent cannot meet, typed |
| step preservation | the embedding carries steps to steps |
| rung pair | the embedding and the read-back, with the "none" witness |
| read-back check | read-back after embedding is the identity, in Lean and on the whole bounded exploration |
| cost | the rung's fewest-changes result, with its lower bound |
| smallest member | L3's verdict against the frozen class |

## Blindness and grading

- Every launch follows the clean-room steps in `meta/climbing/blindness.md`.
- Predictions are frozen as a SHA-256 before launch and scored verbatim
  afterwards. A miss is a result, not a failure.
- The seed, the prompt and the paper body use the parent's words. Outside
  words appear only in the paper's final section and in `meta/`.
- Every seed on this track is chosen by an operator with a target in view.
  So its results are graded "blind (operator-targeted)", and no paper or
  meta file may claim that the track arrived at an outside structure
  independently.

## Acceptance before merge (operator)

- The native gates of `CLAUDE.md`: pytest, `python code/xry/gate.py
  coverage.json`, `python -m mypy`, the four `ci/check_*.py` gates, and
  every evidence `--check`.
- `lake +leanprover/lean4:v4.33.1 -d lean4_core build`, with its exit code
  read on its own line and never piped.
- The strict axiom report of L5.
- The rung record is complete, and the predictions are scored.
- `prompt/` is unchanged, and the transcript audit is clean.
