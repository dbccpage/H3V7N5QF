# Candidate measure declared before selection

This measure is **chosen**, outside the derivational seal. It is a way to
choose which seeds to propose, not a theorem or a finding of a seed. A
candidate must change one or two complete sentences of a named parent seed,
using only that seed's vocabulary. A proposal is discarded before scoring if
it silently conflicts with “nothing else is a change,” uses an undefined
state field without saying how it is recorded, or predetermines an answer.

Each axis receives an integer 0–5, with higher always better:

| Axis | Weight | Meaning of 0 and 5 |
|---|---:|---|
| H: testable Phase-4 hypothesis and falsifier | 4 | No discriminating outcome; a concrete legal witness would refute a named correspondence |
| N: novelty in the seed-edit matrix | 3 | Repeats an existing edit; fills a missing joint edit or changes a previously fixed dimension |
| R: re-check economy | 2 | Requires most earlier claims rebuilt; an existing Lean/Python map carries nearly all unchanged claims |
| C: resistance to by-construction collapse | 4 | New notion sits off the result; it changes reachable states, paths, obstruction, or equivalence in a checkable way |
| M: bounded computability | 3 | No minutes-scale finite run identified; a 2–3-term/short-round run and independent count are plausible |
| G: Genesis bridge value | 2 | No precise primitive; directly probes a named primitive while keeping the seed blind |
| L: Lean feasibility without axioms | 2 | New formal infrastructure unlikely within a bounded run; explicit inductive state/step and at least one invariant look feasible |

Score is `4H + 3N + 2R + 4C + 3M + 2G + 2L` (maximum 100).
The two highest weights are testability and noncollapse because a proposal
that only renames an old result would not advance the audit. Ties are **kept**
and displayed at the same score; file ranks break no scientific tie.
Sensitivity means independently multiplying each one weight by 0.5 and 1.5,
re-ranking all candidates, and reporting which of the top ten change. The
candidate list and scores are in `candidates.json`, with the calculation in
`rank.py`. The top three or four are prototyped on existing code **before**
any complete `seed_prompt.md` is written; a prototype may lower a score or
drop a candidate, but its result is a bounded measurement, not a full
derivation.

## Prototype update and selection

`prototype.py` ran before any complete proposal seed was written. Its exact
bounded output is `prototype_results.json`. C19 has a two-change return from
the empty beginning through a bare one-term state; C21 loses a one-term
two-relation result at round 3. C06 was excluded because dropping only
the loop ban leaves the existing obstruction-answer rule in place: the
one-step loop-producing partial identification is still obstructed, so the
proposed edit does not decide whether it is performed. C08's one-term,
four-round result sets and per-round counts agreed with its parent; an
admission edge was refused but its target also had a direct-addition path.
Its H/C scores fell from 5/5 to 4/2. These are bounded observations; they
do not establish equality of the unbounded result sets.

The eligible top ten after that update are C19, C21, C09, C07, C01, C04,
C05, C25, C11, and C17. C11 and C17 share score 78, so both are retained;
the next eligible score is 77. `ranking.json` reports all 28 candidate
scores, the exclusion, and independent ±50 percent weight sensitivity. For
perturbations with a tie at the tenth-place threshold, it retains all tied
candidates in the sensitivity set and marks its size. The ten full proposal
packages were generated only after this prototype decision. Their seed
files preserve their parent bytes outside the exact substitutions in
`make_packages.py`, and each has `diff.patch`.
