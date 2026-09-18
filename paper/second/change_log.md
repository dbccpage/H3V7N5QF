# Change log, second derivation

Each material change, and its reason. Newest last. Commits are on the branch
the run started on (`second-derivation`); nothing is pushed.

1. **`CLAUDE.md` gained the second derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/second/prompt.md`. The first derivation's plan above it is
   unchanged.

2. **Layout: a new package `code/second/` that imports from `code/xry/`; no
   first-derivation module is modified.** Reason: the task allows changes to
   the first derivation's files only to correct defects. What is reused is
   imported (states, sameness, the counts, the writers, the attempt records);
   what the seed changes is defined afresh (the list of changes, the answers,
   the exploration, the cost, the counts of results, reachability, the
   invariant). `second.changes.changes` builds the list directly and a test
   checks it equals the first derivation's list without its removals;
   `second.changes.perform` refuses a removal.

3. **Every obstructed attempt records "remove the obstruction: impossible: no
   change un-asserts an assertion".** Reason: the seed asks to declare and
   record the answer; under this seed that answer exists in name only (R3),
   and the record says so rather than silently omitting it.

4. **The exploration is also run with identifications left out, and the two
   are compared.** Reason: D10 claims that additions alone reach every result
   in the same round; the comparison is its computed check.

5. **Bounds: ANCHORED files exported at 4 terms, with a counts-only census at
   5 terms.** Reason: an ANCHORED run at 5 terms takes about a minute and
   passes every check, but its per-result and frontier files would have about
   90 000 rows per alternative; the census keeps the completeness certificate
   and the cost check at 5 terms without those files. Its frontier is counted,
   not exported; the paper says so (C8, §6).

6. **Lean: a second library `Second` in the same Lake package; the second
   seed's changes are a new inductive `Step3` with an embedding into the
   first's `Step`.** Reason: the embedding is the formal form of the task's
   rule 5 — every first-derivation theorem about changes that is cited is
   restricted through it, and the restriction is itself a theorem. The
   lakefile of the first derivation gained the library target and a default
   target; that edit is recorded in `paper/change_log.md` (item 20) as the
   task requires for a first-derivation file.

7. **Plan target 5 (rewriting) was reached**: `Step3.rename`, `Reach3.rename`,
   `size_rename`, and with them `result_iff_A/B` and
   `fewest_changes3_every_writing_A/B` for every writing. The first
   derivation's open item 1:O3 is thereby closed for the changes of this seed;
   the first derivation's files are not changed, so its ledger still lists it.

8. **The "if" direction of D12 for carrying maps that merge terms is proved on
   paper and left open in Lean (O3).** Reason: it needs, after the
   identifications along the map, the extension of a one-to-one map on a
   finite set of terms to a rewriting of all terms; the one-to-one case and the
   additions are in Lean, the merging step is not. Bounded effort as planned.

9. **Two test expectations written during the run were wrong and were
   corrected; one correction became a claim.** (a) A directed 4-cycle has no
   carrying map onto a directed 3-cycle (the test now uses a 6-cycle, which
   has one). (b) With `bra` given, "passing on" holds in no result; the test
   had expected a witness. (b) was added to the paper as D15 and R7. Reason for
   recording: the second changed what the paper claims.

10. **Lean proof repairs without change of statement.** `cases` patterns must
    not name the index variable of `Step3`; `| refl s` must be `| refl`; a
    reverse `rw` whose pattern is a metavariable application was replaced by
    `show … from` rewrites; `simpa` was told to unfold `St.addTerm`; two `rw`
    closures were replaced by `omega` / `simp`. No statement changed.

11. **Two log files of the background runs (`.generate_second.log`,
    `.generate_second_check.log`) were deleted before the commit.** Reason:
    they are not evidence (they hold no numbers the summary lacks) and are not
    regenerable by a committed command.
