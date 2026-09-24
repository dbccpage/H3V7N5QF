# Derivation-by-derivation review

**Status (chosen):** this is an audit record outside the derivational seal,
not a new derivation. The inputs are the 21 local seeds and their parent diffs,
the 21 plans in `CLAUDE.md`, each paper, ledger, change log, evidence summary,
`code/**/evidence.py`, Lean sources, and committed axiom report. The
meta branch kept the baseline derivation tree when this audit was written;
references below to a repair mean the separately validated commit `e5d02dd`.
The PR branch later integrated that repair through `main`.
`reading_index.md` gives the exact seed diffs and
open ledger rows. The
`claim_audit.csv` indexes all **782** ledger rows with their status, evidence
cell, and line number on the baseline meta branch; `claim_audit_repair.csv`
keeps the corresponding repair-branch snapshot. Its path probe found no
blank evidence cell for a
derived/computed/refuted row and no unresolved path; this checks *reference
presence*, not the truth of the statement. `audit_ledger.py` is a citation
candidate probe, not a theorem counter. The pinned Lean build and the
regenerated axiom reports are the elaboration receipts.

The table records the semantic checks and the disposition of each seed edit.
`F###` points to the precise evidence and repair in `findings.md`. A blank
finding means this review found no *additional* defect; it is not a claim that
the derivation is complete beyond its stated finite bound.

| Derivation | Parent edit and retained alternative | Evidence / model check | Finding |
|---|---|---|---|
| Base | Four changes; `bra` both ways; FREE and ANCHORED sameness | Independent orbit census, cost formula, obstruction Lean model and stated open rewriting step checked against paper and ledger | — |
| Second | Remove assertion removal; both beginnings retained | `Step3.toStep` is a restriction, not a converse; carrying map and finite census rechecked | F003 |
| Third | Remove identification; both readings of obstruction response retained | `Step2.toStep3`, exact size increase, finite sequence lengths and census checked | F004 |
| Fourth | Count assertion multiplicity; simple states retain third's model | `ofSt`/`toSt` only inverse under stated simple/WF hypotheses; counted census and costs checked | F005, F013 |
| Fifth | Restore removal and identification on counted states | New cost and cycle claims checked against `Step5` and bounded search, not inherited from fourth's monotonicity | F006, F013 |
| Sixth | Drop ban and obstruction paragraph | Fifth embeds only on legal states; loops and one-term outcomes checked in own exploration | F007, F013 |
| Seventh | Empty beginning, no names | Naming a nonempty state requires a chosen term; the first step is separate; count and cost checks are own | F013 |
| Eighth | From seventh, add relation `s` and restore the `arb` beginning | Per-relation projection to sixth can stutter; own two-relation count differs from a product; given-attempt receipt checked | F008, F011, F013 |
| Ninth | Empty beginning/no names in eighth | Two routes via seventh/eighth are kept; projected steps may stutter; swap and count evidence checked | F002, F013 |
| Tenth | Add change-local leftover record | Chosen result/step model is ninth's by construction; parent comparison is disclosed as deterministic, while orbit count is independent; tagged reading kept | — |
| Eleventh | Add noninjective writing | Chosen state/step model is ninth's by construction; collision criterion and labeled alternative checked | — |
| Twelfth | Record assertions merged by identification | Chosen state/step model is ninth's by construction; relation-specific record and tagged alternative checked | — |
| Thirteenth | Add relation-forgetting coarse writing | Chosen state/step model is ninth's by construction; split count and coarse alternative checked | — |
| Fourteenth | Add nonassertion leftover writing | Chosen state/step model is ninth's by construction; tagged result reading and removal witnesses checked | — |
| Fifteenth | Add admission record independent of reaching | Chosen state/step model is ninth's by construction; tagged reading kept; literal availability receipt checked | F009, F012 |
| Sixteenth | Admit leftover, changing the state | Own `RSt`, `Step16`, potential, bounded count and record feedback; ninth projection has a step witness; both unchosen readings kept | F010 |
| Seventeenth | Strike `xrx` ban, keep obstruction wording | M1/M2 and replacement/performance readings all retained; base comparison is only on loop-free replacement results | F001 |
| Eighteenth | Written forms are distinct results | Written equality and orbit quotient compared; the directional and maximum excess fields support the paper's bounded numbers | — |
| Nineteenth | Identify only in one chosen assertion | Own `PStep`/`PReach`; P1/P2 attempt sets retained; no one-term result, confirmed by term-cardinality proof | — |
| Twentieth | Fewest total changes first | Two attempt orders use the same round/cap in the chosen reading; alternative global ranking has its own capped run | — |
| Twentyfirst | Refuse every obstructed change | Independent refusal exploration against the base closure, with answer membership checked against that closure | — |

## Cross-cutting tests of the defect panel

- **Vacuous checks and definitional citations:** the existing two CI gates and
  their mutation bites passed at baseline. The tenth–fifteenth papers and
  ledgers explicitly disclose the by-construction identity with the ninth;
  their parent comparison alone is not treated as independent evidence.
- **Numbers and directions:** the eighteenth's `rounds_below_the_base_cost`,
  `rounds_above_the_base_cost`, and `greatest_excess_over_the_base_cost` fields
  support the direction and maxima; the twentieth compares equal expansion
  caps; the nineteenth's `missing_names_one_term` and `extra` support its
  containment statement. These are bounded measurements, not unbounded
  theorems.
- **Evidence literals:** F011/F012 were changed from fixed values to model
  calls in `eighth/evidence.py` and `fifteenth/evidence.py`, with injection
  tests for both. Other literal zeroes reviewed here mark a structurally absent
  obstruction under seeds without the ban, or a round-zero cost, not a
  claimed differential count.
- **Axiom receipts:** ten own reports omitted cited Lean names (F001–F010).
  The compiled theorems exist in their parent or own libraries; the missing
  receipt was not a counterexample to the theorem. The repaired reports and
  a narrow citation/report gate have a real-line removal injection witness.
- **Ledger carry-forwards:** eight closed-item rows in six derivations had
  empty evidence cells (F013); they now cite the existing source or series.
  Four remaining empty evidence cells describe notions
  explicitly without an object in that seed; no live claim is hidden there.
- **Bounds and alternatives:** the first nine and sixteenth export bounded
  frontiers and independent counts. The seventeenth states where its closure
  is not independently counted; the eighteenth–twentyfirst state their
  smaller bounds and open claims. The chosen/unchosen readings remain in the
  papers and evidence, with no silent collapse found in this pass.

## What this audit does not establish

**Open:** path, coverage, mutation, and axiom receipts do not establish that
all 782 English statements are mathematical consequences of the seeds. A
counterexample would be one legal state or change sequence satisfying a seed
and falsifying a ledger statement; a supporting witness is a statement
with its Lean theorem or an exhaustive bounded census at the stated bound.
The repaired reports improve proof custody, not the scope of the theorems.
