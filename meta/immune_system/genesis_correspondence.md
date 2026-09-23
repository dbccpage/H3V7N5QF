# Genesis correspondence at one pinned read-only snapshot

This analysis is outside the derivational seal. Genesis was read through
`gh api` at `dbccpage/19L57G1@89fc568a61eb22100edf4070d40eb1449c350ed4`;
no Genesis file was copied here. Its README, `CLAUDE.md`, paper §§1–3 and
11–12, `paper/anti_skill_inbox.md`, `paper/skill_inbox.md`, the primitive,
transition, observation, trace, controller, higher-cell and refusal sources,
their named artifacts, and seven skills were read. A **chosen** analogy is
only a comparison. **Derived** needs a local theorem or a source-level proof;
**computed** is bounded; **refuted** has a witness; **open** requires a test.

## Event language and transition codebook

Genesis's event constructors are in
[`code/derivation/transition_alphabet.py`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/code/derivation/transition_alphabet.py)
and its primitive event model; its codebook has 13 declared classes and 12
effect signatures **relative to its chosen presentation**, not a native
contextual-congruence theorem. The local seed has four kinds of change; an
obstruction answer is a protocol around them. The following rows are
comparisons, not an identification of the alphabets.

| Genesis primitive | H3V7N5QF counterpart and limit | Status | Test that would sharpen it |
|---|---|---|---|
| `admitOcc` / `supplyOccurrence` | Adding a term increases the local supply, but a term is not a Genesis occurrence admitted by a controller | chosen analogy | Encode one local add-term step as a Genesis event and compare state effect under a specified translation |
| `admitWit` / `assertDifference` | Adding `xry` raises local multiplicity; in 15 reaching and admission are separate, and in 16 an admission can add an assertion | chosen analogy, derived separation via `Fifteenth/reaching_does_not_admit` | Define witness translation preserving multiplicity and admission outcome |
| `protect` / `retainDifference`, `protectObstructing` | The base ban on `xrx` is a static condition; it has no protection event or retention decoration | refuted as an event identity: 17 drops the ban while retaining obstruction wording, whereas base keeps it | A seed with protection as a change, and a state pair differing only by the protection record |
| `declareObs`, `refineCol`, `addCol` / `extendObservation`, `refineObservation` | 11's writing and 13's coarser writing are recorded views, not a dynamic observation-context language | open as a semantic bridge | Add a context that reads selected assertions and test profile separability under refinement |
| `refuse` / `recordRefusal` | 21 records refusal and leaves the state fixed; base also records refused changes | derived local behavior (`Twentyfirst/Refusal.lean`), chosen event analogy | Compare whole refusal traces, not just reached states |
| `setBudget` / `writeBudget` | The 100-round instruction and finite term bound constrain the *study*, not a performed change | refuted as a current seed event: no listed local kind writes a budget | Add a budget-bearing state and a budget-changing kind, then compare closures |
| `writeLicense` | No license field or change appears in any local seed | open extension; no current counterpart | Add a license record whose value changes which changes are allowed |
| `halt` / `absorbTerminal` | A finite frontier or an empty next round under a bound is not an absorbing state event; adding a term remains possible outside the bound | refuted as a current event identity, witnessed by the base `addTerm_legal` | Add explicit halt and show no later change from its outcome |
| `declareObstructing` / `declareObstructingQuiet` | The base obstruction test marks a would-be `xrx`; whether that can change independently of state is absent | chosen partial analogy | Candidate seed that changes the test by a change |
| `protectObstructingQuiet` | A local obstruction can be refused or answered, but no quiet/protection bit is stored | open | Add a stored quiet/protection response and compare identical state outcomes |

There are **two legal witnesses** against a unique event classification from
local state effects. In 16, removing an assertion then admitting its
leftover into the same relation returns exactly to the original state
(`remove_admit_same`), while adding that assertion directly changes the
state. In 21 a refusal changes no state, while adding a term does. The
operation record distinguishes each pair even where a state-only map forgets
it. A state quotient therefore cannot by itself recover Genesis's declared
event classes. The local four change kinds and Genesis's 13 presentation
classes have different definitions and cardinalities, so an isomorphism of
the declared alphabets is **refuted**.

## Observation, candidate primitives and controllers

Genesis
[`observe.py`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/code/derivation/observe.py)
defines an observation profile using the contexts into which a process can
be plugged and which results are derivable; separability is profile
inequality. H3V7N5QF's FREE/ANCHORED equivalence is rewriting of terms, 18
keeps written forms distinct, and 11 studies a possibly colliding writing.
These are **chosen analogies**, not observation-profile equivalences. The
two writings of a base orbit in 18 are one FREE result but two written
results; the `r`-only and `s`-only one-pair ninth states have the same
`r+s` coarse writing but are distinct ninth results (13). Thus at least
two legal observations yield different partitions. No profile equality is
forced by the local seeds. A proposed observation seed must specify the
contexts before claiming separability.

Genesis's
[`primitive_core.py`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/code/derivation/primitive_core.py)
defines nine candidates on a *declared finite universe* `n ≤ 3` with limited
retention, protection and operation decorations. The
[`implication matrix`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/artifacts/primitive_implication_matrix.json)
keeps `Bl`'s Prop-level locatedness implications open even though finite
decidable tables make `Bl` coincide extensionally with `A` there.

| Candidate | Local comparison | Status and boundary |
|---|---|---|
| W: the designated pair is asserted | Base `arb` is asserted at the beginning | given local sentence, chosen correspondence; not a claim about every later result under removal |
| A: W plus irreflexivity | Base legality excludes `xrx` | chosen structural match; Genesis's operation decorations are not local states |
| Bs: A plus symmetry | `bra` is independent of `arb`; even both between `a,b` would not make every pair symmetric | refuted as an identification. Witnesses: the two-term beginning with `arb`,`bra` has symmetry; add `arc` on a third term without `cra` and it fails |
| Bc: A plus cotransitivity | No seed imposes it | refuted as a consequence of local givens. Witnesses: a three-term strict total order of assertions satisfies it, while `arb` alone with a third term fails at that third term |
| Bl: A plus locatedness | Local finite tables are decidable, but no Prop-level locatedness theorem is transferred | open bridge, matching Genesis's explicit OPEN cells |
| C: W plus protection record | No local protection relation | open extension; static `xrx` ban is not that record |
| D: distinct designated names | Base `given_distinct` proves `a ≠ b`; 2/3 preserve it under their steps | derived local analogue, not equality of candidate predicates |
| E: irreducibility under a specified endofunction family | Local identification after removing `arb` merges `a,b`, but no Genesis-style chosen operation family is part of the state | open bridge; a family and its closure must be declared first |
| F: A plus retention and protection | Local seed has neither decoration | open extension; no finite implication is imported |

Genesis's
[`primitive_controller_category.json`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/artifacts/primitive_controller_category.json)
reports initiality refuted by constant simulations and a non-unique
controller family differing on refusal at a certified obstruction, within
its declared 1,024-object universe (128 live). The local base has multiple
answer records leading to the same set of results (`build_answer`,
`remove_obstruction_first_or_last`), and 21 chooses refusal alone. This is
a **chosen analogy** to policy variation. No local simulation morphisms or
controller category are defined, so local initiality and non-uniqueness are
**open**, not inherited from Genesis. A test would define controllers as
functions from attempted changes and state to recorded answer and result,
then define simulations and search for two distinct ones on a certified
obstruction.

## Equivariance, traces, higher cells, and refusal

| Genesis structure | Local evidence and missing part | Status |
|---|---|---|
| Renaming group action and equivariance | `Step9.rename`, `Reach9.rename`, `Ninth.proj_rename9`, `forget_rename8`, and `swap9_swap` prove the named local squares. Base O3's full every-writing cost theorem remains open in Lean | derived on those maps; open beyond them |
| Trace commutation, frames, idempotence | The base proves `remove_obstruction_first_or_last` for one critical pair; ninth swap is an involution. There is no general independent-step trace quotient. Removing a nonexistent assertion is not a change, so add/remove orders need not both be admissible | derived examples; refuted general commutation as an admissibility claim |
| Higher-cell boundary rule | Genesis [`higher_structure.py`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/code/derivation/higher_structure.py) and [`HigherStructure.lean`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/lean4/Derivation/HigherStructure.lean) admit a (k+1)-cell exactly above a complete unfilled k-boundary; two conventions work. Local `Reach` has path composition but no native higher-cell constructor or boundary-fill predicate | refuted as a current-model identity; open as a new seed, with both boundary readings retained |
| Refusal frontier and declaration | Genesis's tied minima at cost 2 in its [`refusal_frontier.json`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/artifacts/refusal_frontier.json) are presentation-specific. Local 21's refusal is recorded and changes nothing, and 15's admission is independent of reaching | derived local separation; open numerical comparison, no cost-2 claim imported |

Two witnesses show why a native 2-cell **does not follow** from local path
composition. In the third seed, adding a term then an assertion and doing
the two additions in the other order reach the same result where both are
legal (`two_sequences`, `evidence/third/`); in the base, remove-then-identify
and identify-then-remove do not have the same legal intermediate under the
ban. An equation between endpoints neither supplies a boundary-fill rule nor
guarantees the two orders are legal. The proposed next seeds must make such a
rule an explicit sentence and keep alternative boundary conventions.

Genesis's `skill-inbox`, `anti-skill-inbox`, `proof-tournament`,
`claims-audit`, `gates`, `inject`, and `pin` skills all state
`AuthorityEffect: None` at this pinned snapshot. They describe review
practices, not permissions or proof rules for this repository. The local
equivalents are the claim ledgers, axiom reports, CI detectors, mutation
injections, and frozen prompt policy (**chosen process analogy**). Which
specific detector grew after which defect is tested in `defect_incidence.md`;
the analogy alone does not prove learning.

The pinned skill sources are
[`skill-inbox`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/.claude/skills/skill-inbox/SKILL.md),
[`anti-skill-inbox`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/.claude/skills/anti-skill-inbox/SKILL.md),
[`proof-tournament`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/.claude/skills/proof-tournament/SKILL.md),
[`claims-audit`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/.claude/skills/claims-audit/SKILL.md),
[`gates`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/.claude/skills/gates/SKILL.md),
[`inject`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/.claude/skills/inject/SKILL.md),
and [`pin`](https://github.com/dbccpage/19L57G1/blob/89fc568a61eb22100edf4070d40eb1449c350ed4/.claude/skills/pin/SKILL.md).
