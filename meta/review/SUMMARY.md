# Whole-repo review and next-ten summary

This report is outside the derivational seal. It records the local tree and
the precise scope of the checks, without treating a green gate as authority
for a paper claim. The starting local `main` and `origin/main` were both
`53b319a48f347b1a52e823ea7db46c79f8434c42`; remote freshness was not
queried because this task permits network reads only from Genesis.

## Findings and repairs

The 21 seeds, plans, papers, ledgers, change logs, evidence summaries,
evidence checks, Lean sources, and axiom reports are indexed in
`derivation_review.md` and `reading_index.md`. The 782 ledger rows received
a path/status audit, with the separate limits stated there. The review found
**10 major** axiom-receipt omissions (F001–F010) and **3 minor** evidence or
ledger-custody defects (F011–F013), across 11 derivations. No false Lean
theorem or critical proof-status error was established in this pass.

Local repair commit `e5d02ddab4373a7c35eb0eaafad7b9972234d01d`
prints the missing cited declarations in ten own axiom reports and regenerates
each report and manifest. The eighth and fifteenth receipts now compute two
previously literal fields from their models; injection tests force both to
change. Eight closed-item ledger rows now name their existing evidence.
`ci/check_axiom_citations.py` grew from the repeated receipt defect and has
an injection that removes a real second-derivation report line, observes a
failure, restores it, and observes a pass. This checks custody of a citation,
not the English meaning of the theorem.

The untouched-tree baseline passed all 51 native commands, including 935
tests, 99.78% line and 99.60% branch coverage under the gate, mypy, four CI
gates, the pinned Lean build, 21 evidence `--check` runs, and 21 axiom-report
writers (`baseline/summary.json`). The full post-repair suite passed **52/52**
commands at exact commit `e5d02dd`: 940 tests; coverage gate 99.78% line and
99.60% branch; mypy; five CI gates, including the new citation detector;
the pinned 3,160-job Lean build; all 21 evidence `--check` runs; and all 21
axiom-report writers (`repair_suite/summary.json`). No tracked source,
paper, evidence, gate, Lean, or prompt file drifted after the run. The
repair-branch run had only the preexisting untracked `AGENTS.md` and the
uncommitted `meta/` package, which was committed on the proposal branch.

## Correspondence results

- **Derived/computed:** On their stated well-formed domains, many named
  state and step maps preserve ungraded reachability; the 3→2→1 triangle,
  the 6/7/8/9 object diamonds, selected renaming squares, the ninth swap
  involution, and the `ofR ⊣ proj_r` ungraded reachability law have the
  proofs or finite checks cited in `../immune_system/correspondence.md`.
- **Refuted:** a state-only quotient retains distinct histories, projection
  preserves every path length, a total right-adjoint naming map exists at
  the empty state, and the local change alphabet is Genesis's declared
  event alphabet. Explicit witnesses and scope are in the correspondence
  and Genesis comparison.
- **Open:** a coherent 2-category for all 21 derivations, general
  commutation of seed edits, and a local controller category with Genesis's
  simulation structure. These require definitions and tests not supplied by
  the existing seeds. The defect chronology has incompatible review units;
  it cannot estimate a causal learning rate.

## Ten selected proposals

The declared weighted rubric, 28 scored candidates, all ±50% one-weight
sensitivity runs, four bounded prototypes, and exact parent-seed diff checks
are in `../next_ten/`. Each proposed seed changes one or two sentences and
remains outside `prompt/`.

| Rank | Candidate | Hypothesis tested |
|---:|---|---|
| 1 | C19 remove a bare term | Whether a nonempty result can return to the empty beginning |
| 2 | C21 cross-relation guard | Whether a guard breaks independent addition or is bypassed by identification |
| 3 | C09 given first change | Whether a given change shifts cost without a given assertion |
| 4 | C07 written refusal | Whether written sameness changes the recorded refusal outcomes |
| 5 | C01 refusal memory | Whether a refusal record changes later reachability |
| 6 | C04 written budget | Whether a state-carried budget changes reachable results |
| 7 | C05 two-term readings | Whether local readings differ from written and FREE sameness |
| 8 | C25 record order | Whether order-sensitive feedback changes admission paths |
| 9 | C11 two-step leftover | Whether a two-step answer adds outcomes beyond the one-step criterion |
| 10 | C17 swap as change | Whether making swap a change alters shortest paths and sequences |

C11 and C17 tie in the declared scoring; both are retained. The prototype
excluded C06 because its obstruction answer is underspecified and demoted
C08 after a bounded result-set comparison. No proposal has been installed or
run as a full derivation.

## Remaining boundary

The repair branch passed 52/52 native commands. The meta branch ran all 51
commands at `6f60a16`: 50 passed, while the parallel Lean build failed to
read existing Mathlib `.olean.private` files. Sequential builds of the ten
affected modules and a full pinned build then passed without source changes.
A clean retry at the same commit passed its first 39 commands before the user
stopped it. The final 11 report writers and status command had passed on the
first run; a single uninterrupted 51/51 retry was not completed. See
`meta_suite_first_summary.json` and `meta_suite_retry_summary.json` for exact
exit codes. The user subsequently requested commit, push, and PR publication.
`AGENTS.md` was present untracked before this work and is preserved as
user-owned. No file under `prompt/` changed; `.lake/` is not staged or
committed. No remote PR was opened when this summary was written.

After PR #43 merged as `460c6e623636f69f588f6f123d4974b1c6a3086c`,
the proposal branch integrated the new `main`. Both competing change-log
entries were kept as items 39 and 40. Relative to that `main`, its code,
evidence, Lean sources, and tests are identical; the focused citation,
package, paper-pin, and prose checks passed on the integrated tree. The
integration does not create a new full-suite receipt.
