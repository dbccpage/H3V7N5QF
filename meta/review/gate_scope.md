# What the green baseline and repair gates establish

**Status: chosen audit interpretation.** The baseline has 51 recorded command
exits at `53b319a48f347b1a52e823ea7db46c79f8434c42` plus the plan
commit; the repair suite adds the citation detector at
`e5d02ddab4373a7c35eb0eaafad7b9972234d01d`. Each log and exit code
is in `baseline/` or `repair_suite/`. A green exit is a reproducible receipt
for the command's own predicate, never a transfer of authority to a claim.

| Command family | What exit 0 checks | What it does not check |
|---|---|---|
| `pytest -n auto` and `code/xry/gate.py` | Executed test assertions; at least 95% line and branch coverage; every evidence module fully covered under the gate's rule | Untested states beyond declared bounds, proof of a paper claim, or independence of a test oracle |
| `mypy --strict` | Types of configured Python source and tests | Runtime behavior, mathematical completeness, or source status |
| Prose watchlist | Counts of the watched digests in tracked prose equal deliberate per-file pins | Unwatched vocabulary and semantic steering within ordinary words |
| Vacuous comparison gate | Its documented local alias/self-comparison shapes | All cross-module semantic equality or tautologies hidden in computation |
| Definitional citation gate | Its documented `rfl`/self-equality and notion-mismatch patterns in cited Lean source | All weak theorems or whether a non-definitional proof implies the English statement |
| Mutation bite gate | Every registered disagreement field in its present panel fires under its matched injection | Unregistered fields, other defect families, or a general mutation score |
| Citation/report gate, repair branch | Backticked local theorem/lemma citations appear in that derivation's regenerated report; real F003 line-removal injection bites | Unbackticked references, short-name collisions, or whether the cited theorem states the paper's claim |
| Pinned `lake build` | The local Lean package elaborates and builds at this toolchain and dependency snapshot | Correctness of the informal model, a paper's reading of the seed, or report completeness |
| Evidence `--check` (21) | Current generators reproduce tracked bytes at their declared finite bounds | Correctness of the generator, a larger bound, or an independent mathematical proof |
| Lean report writers (21) | The named `#print axioms` requests elaborate; dependencies remain within the allowed standard axioms and the source scan finds no forbidden tokens outside comments | Every cited name is present unless the separate citation detector runs, or that the theorem proves the English claim |
| Git status / prompt diff | Tracked source drift and changed prompt paths at this checkout | Ownership of untracked files, remote PR state, or whether a committed receipt was generated from the current head |

**What does not follow:** all English claims do not become true merely
because these gates pass. A model with an overbroad `PStep` can build in Lean
while representing more changes than the seed allows (`Nineteenth/Partial.lean`);
the third derivation's exact size theorem is a separately scoped claim about
its own `Step2`. Both are legal constructed models that pass their own Lean
checks, with different relationships to their seeds. The audit therefore
checks statement scope and counterexamples in addition to gate exits.
