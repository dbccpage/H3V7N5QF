# Change log

1. Plan and stopping conditions recorded in `CLAUDE.md` before other work
   (the prompt requires that commit on its own).
2. Reading of the seed against the base, in `research/seventeenth/`. Not
   evidence. Two readings of an obstructed change (enter it, or not) and
   two readings of "makes some `xrx`" are kept.
3. `code/seventeenth/` computes both readings. At 3 terms and 6 rounds the
   A-replace closure matches `xry.explore` and the base cost, and no result
   asserts `xrx`. The A-perform closure does: identifying `a` with `b` is
   one change whose outcome asserts `ara`, and the base cost of that outcome
   is greater than 1. A refusal changes nothing. Remove-then-identify and
   identify-then-remove end at the same state.

4. `lean4/Seventeenth/`: `LoopFree` is the base `Legal` as a predicate;
   `Step17` drops the ban's side-conditions; M1 and M2 agree on a loop-free
   state and differ on a state that already asserts `ara`; an unobstructed
   `Step17` on a loop-free state is a base `Step` and conversely; the base
   cost is the fewest changes along those steps; identifying `a` with `b` in
   what is given is one `Step17` whose outcome asserts `ara` and whose base
   cost is not that length; remove-then-identify and identify-then-remove
   end at the same state, and the second path's intermediate asserts `ara`;
   `rename` for an injective rewriting. Not yet built: `lake` checked the
   pinned packages out again and is rebuilding them, so the exit code is not
   in hand.

cycle: wrote the Lean library (`Step17`, the embedding, the A-perform witness, answers, rename) and the lakefile target; next get `lake build` green, then the paper, the ledger, and `evidence/seventeenth/`.

5. Paper, ledger, and the evidence frontier. Both unchosen beginnings
   (`ara`, `brb`) are checked. `code/seventeenth/leanreport.py` writes the
   axiom report and has not been run: this Lake rejects `-j`, so the build
   is one process with `LEAN_NUM_THREADS=4`, still compiling dependencies.

cycle: wrote the paper, the ledger, the frontier and the report writer; pytest, the coverage gate, mypy, the prose watchlist, the three ci gates and evidence `--check` are green; next read the single lake exit and, if it is 0, write `lean_axioms.txt` and open nothing further until that file is committed.

cycle: left the one `lake build Seventeenth` running (Mathlib oleans advancing, about 1294 of 8311 at 05:19; did not start a second build); next read that process's exit and, if it is 0, write `evidence/seventeenth/lean_axioms.txt` and close O1.

cycle: the same lake process was still compiling Mathlib (oleans 1599 of 8311 at 05:36, newest `Algebra/Star/StarProjection.olean`; did not start a second build); next read that process's exit and, if it is 0, write `evidence/seventeenth/lean_axioms.txt` and close O1.

cycle: the same lake process was still compiling Mathlib (oleans 1905 of 8311 at 05:56, newest `LinearAlgebra/AffineSpace/Midpoint.olean`; did not start a second build); next read that process's exit and, if it is 0, write `evidence/seventeenth/lean_axioms.txt` and close O1.

cycle: the same lake process was still compiling Mathlib (oleans 2229 of 8311 at 06:16, newest `RingTheory/MatrixPolynomialAlgebra.olean`; did not start a second build); next read that process's exit and, if it is 0, write `evidence/seventeenth/lean_axioms.txt` and close O1.

cycle: the same lake process was still compiling Mathlib (oleans 2549 of 8311 at 06:36, newest `FieldTheory/IntermediateField/Adjoin/Algebra.olean`; did not start a second build); next read that process's exit and, if it is 0, write `evidence/seventeenth/lean_axioms.txt` and close O1.
