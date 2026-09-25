# H3 "twin fills": launch packet

**Status:** prepared 2026-09-25. Both seeds and tasks are installed byte
for byte:

- 3A, "fill one", as `prompt/twentyfourth/`;
- 3B, "fill three", as `prompt/twentyfifth/`.

**Not launched.** By ruling D2 (`../rulings.md`) the twins are siblings:
two runs in parallel from one snapshot, landed on one branch. The operator
launches after this install merges, with §6 below, which applies
`../launch.md` to two clones. This packet is chosen apparatus, outside the
seal.

| file | role | SHA-256 (LF bytes) |
|---|---|---|
| `3a_fill_one/seed_prompt.md` | 3A seed, installed as `prompt/twentyfourth/seed_prompt.md` | `ebbf2fb621125898aa28ef13f7c9a12f1ddac81f52b15d6ea4cf004e805cf89a` |
| `3a_fill_one/prompt.md` | 3A task, installed as `prompt/twentyfourth/prompt.md` | `835a1074af291750c63ea95e014bc0b368e1d67a196318c1a5dc4474890f7ee5` |
| `3a_fill_one/prediction.md` | 3A frozen prediction, native words only | `dbbc9d39707c4c74bdd4e8e53a8dd31daca795b9e66a5c2bed1c8bd077e3d1d9` (committed first) |
| `3b_fill_three/seed_prompt.md` | 3B seed, installed as `prompt/twentyfifth/seed_prompt.md` | `79a757575547a15ab29fce9d83efa081d04c75f76034ca15a5533449b324507b` |
| `3b_fill_three/prompt.md` | 3B task, installed as `prompt/twentyfifth/prompt.md` | `57dbecc1a88896072cfee9a2d98fb009cd3fe4fdfb0f31253cfd60579df7b3d5` |
| `3b_fill_three/prediction.md` | 3B frozen prediction, native words only | `7aff4f0ea1cd3b680db13496c79284420948a7890e586c2a10611e0aae8acc4f` (committed first) |

This checkout converts line endings, so check a digest against the committed
blob (`git show HEAD:<path> | sha256sum`), not the working file.

## 1. The edits

The parent of both twins is the twenty-third seed
(`prompt/twentythird/seed_prompt.md`, `84eda219…`). Each twin applies one
member of the frozen class (`../extension_class.md`, `6b0929a6…`):

- The class says the new kind "joins the list". It is appended as the
  list's last kind, with its first letter lowercased to match the list's
  other kinds. That is the only change to the class's text.
- The class's "Adds" sentence goes at the end of the paragraph that lists
  the changes, after the sentence on identifying. The class does not say
  where it goes; the operator placed it, as H2's raising sentence was
  placed.

```diff
-A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.
+A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion; filling one term. Nothing else is a change. Identifying two terms replaces both by one term in every assertion. A filled term `x` balances when `xrx` and `xsx` are asserted equally often; for every result, record which filled terms balance.
```

```diff
-A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.
+A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion; filling three different terms. Nothing else is a change. Identifying two terms replaces both by one term in every assertion. Three filled terms `x`, `y`, `z` balance when, going from `x` to `y` to `z` and back to `x`, as many assertions are written with `r` as with `s`, each counted as often as it is asserted; for every result, record which filled terms balance.
```

The first diff is 3A (`twentyfourth`), the second 3B (`twentyfifth`).
Every other sentence is the twenty-third's.

## 2. The demand, shared by both twins

Both tasks carry the same sentence:

> In the twenty-third, does what is recorded for a result show which of its
> terms keep it from being the same as a result with nothing asserted on as
> many terms; and here, which results that are not the same as such a result
> can be told from one that is by filled terms that do not balance, which
> cannot, and what are the fewest changes to each result?

## 3. Licence check (`../rubric.md`)

| rule | how H3 meets it |
|---|---|
| L1, one demand in the parent's words | The sentence of §2, identical in both tasks. Its first half asks the parent's question in the parent's words. The second half asks about this seed in its own words, "filled" and "balance", and gives no answer. |
| L2, exhaustion at the parent's level | *The residual:* the twenty-third's survivors. No raising makes a survivor the same as nothing: every raising keeps the loops, returns and sums around three terms (the twenty-third's D2: `Same3.loop`, `Same3.twoWay`, `Same3.around`, `same3_nothing_iff`, in Lean). *The record:* the twenty-third records only counts. Its results `a b; brb` and `a b; bra` both record two terms, one in `r` and none in `s` (`evidence/twentythird/results_bound2_rounds24.csv`), yet one is shown by a loop and the other by a return. **Recorded plainly:** this second half rests on the seed's record sentence and a computed pair, not on a Lean theorem. |
| L3, the smallest member of the frozen class | Only the three fills record a check that can tell a survivor apart. Each is two sentences, and "fill one" adds the fewest new words, so **3A installs the smallest member.** **3B, recorded:** "not the smallest; chosen by the operator" (ruling D2). **Twin exception, recorded:** L3 runs siblings only for tied members, and these twins are not tied. They are siblings by ruling D2, to compare the smallest member's order with an order chosen from outside. This is the same kind of recorded exception the author accepted for H2. |
| L4, states or steps change | Each member's first sentence adds a change, filling, and a part of the state, what is filled. Witnesses: `a` against `a` with `a` filled (3A); `a b c` against `a b c` with the three filled (3B). **Recorded plainly:** each member's second sentence, taken alone, only defines a reading and keeps a record beside the state, which L4 refuses for a sentence on its own. The class was frozen with each member as one unit (D5), and D2 names these members. |
| L5, Lean and the rung pair | Two libraries in the one `lean4_core/` package, `Twentyfourth` and `Twentyfifth`, one per twin, each importing `Twentythird`. Unlike H2, the rung pair is expected to hold, with the twenty-third as source. The embedding is "nothing filled", with each change carried to the same change. The map back answers "none" on a result with a filling. The smallest "none" is `a` filled (two changes) for 3A and `a b c` filled (four changes) for 3B. **Twin note:** each twin adds its own library, so the shared `lakefile.toml` line is joined when landing (§6.4). |
| L6, ablation after the merge | For each twin: strike the new kind from the list, then strike the balance sentence, and rerun the bounded exploration. |

## 4. The tasks

Each `prompt.md` follows H2's task, with these differences:

- The parent is the twenty-third, and the inputs are its line.
- The sibling is named and excluded as an input.
- The demand is §2's sentence.
- It asks the run to relate the seed to the twenty-third's *results*, since
  the twenty-third's states are not one to one with its results. "Where
  this seed makes … the same" becomes "If this seed makes … the same", so
  the task does not presuppose a merge.
- It says that both twins land on one branch. So the run only adds to shared
  files and appends its plan to the end of `CLAUDE.md`.
- It keeps H2's instruction to run the final gates in the foreground and
  wait for them.

It names no outside structure and gives no answer.

## 5. The frozen predictions

`3a_fill_one/prediction.md` holds A0 to A9, and `3b_fill_three/prediction.md`
holds B0 to B8, in native words.

- **A0, B0:** the parent's question, with a witness.
- **A1, B1:** balance is kept by the sameness.
- **A2:** filling changes the states.
- **A3, B3:** what a filling tells, what it cannot, and the survivors
  never told apart.
- **A4:** identifying brings returns onto a loop, never a sum around three
  terms.
- **B2, A6:** the readings each run must keep.
- **B4:** identifying inside a filled triple.
- **A5, B5:** fewest changes, and the cheapest told-apart result: three
  changes for 3A, at least five for 3B.
- **A7, B6:** the exchange.
- **A8, B7:** the rung pair.
- **A9, B8:** the order, from each side.

**The order test (ruling D2), predicted from A9 and B8:** the two orders
disagree.

- Filling one term tells apart the cheapest survivors (`a; ara`, three
  changes) and reads loops only.
- Filling three terms tells apart, under the direct reading, the survivors
  whose loops and returns cancel (`a b c; arb bsa`), and reads no loop.
- Each tells apart survivors the other never does. Neither tells apart a
  survivor on two terms (`a b; arb`), nor returns that cancel around three
  terms (`a b c; arb bra bsc csb`).

**A draft claim was dropped before freezing.** An earlier hand draft said
that on three terms, with assertions only one way round, three filled terms
balance exactly when the result is the same as nothing. That is false.
`a b c; arb bsc` balances going `a, b, c` (one in `r`, one in `s`), yet its
return between `a` and `b` sums to 1.

## 6. Launch and landing, in parallel

`<n>` is `twentyfourth` for 3A (clone `C:/wt/h3-d24`) and `twentyfifth` for
3B (clone `C:/wt/h3-d25`). The commands are PowerShell. Both runs start from
one snapshot.

### 6.0 Before the snapshot: the committed digests

```powershell
$R = "C:/Users/a343o/source/repos/H3V7N5QF"
git -C $R fetch origin
git -C $R show origin/main:meta/climbing/h3_twin_fills/3a_fill_one/prediction.md | sha256sum    # dbbc9d39…
git -C $R show origin/main:meta/climbing/h3_twin_fills/3b_fill_three/prediction.md | sha256sum  # 7aff4f0e…
git -C $R show origin/main:meta/climbing/extension_class.md | sha256sum                          # 6b0929a6…
git -C $R show origin/main:prompt/twentyfourth/seed_prompt.md | sha256sum                        # ebbf2fb6…
git -C $R show origin/main:prompt/twentyfifth/seed_prompt.md | sha256sum                         # 79a75757…
```

### 6.1 One snapshot, two branch names

```powershell
$R = "C:/Users/a343o/source/repos/H3V7N5QF"
$M = git -C $R rev-parse origin/main
$env:GIT_INDEX_FILE = Join-Path $env:TEMP "h3-snapshot.index"
git -C $R read-tree $M
git -C $R rm -r -q -f --cached meta
$T = git -C $R write-tree
Remove-Item $env:GIT_INDEX_FILE; Remove-Item Env:GIT_INDEX_FILE
$S = git -C $R commit-tree $T -m "Snapshot"
git -C $R branch snapshot/twentyfourth $S
git -C $R branch snapshot/twentyfifth $S
"main $M -> snapshot $S"
```

### 6.2 Two history-free clones

```powershell
foreach ($t in @(@{n = "twentyfourth"; C = "C:/wt/h3-d24"}, @{n = "twentyfifth"; C = "C:/wt/h3-d25"})) {
  $n = $t.n; $C = $t.C
  git clone --depth 1 --no-tags --single-branch --branch "snapshot/$n" "file:///C:/Users/a343o/source/repos/H3V7N5QF" $C
  git -C $C remote remove origin
  git -C $C switch -c "derivation/$n"
  git -C $C branch -D "snapshot/$n"
  git -C $C reflog expire --expire=now --all
  git -C $C gc -q --prune=now
  git -C $C config user.name H3V7N5QF
  git -C $C config user.email run@localhost
  git -C $C log --all --format="%h %s"                        # must print one line: <S> Snapshot
  if (git -C $C ls-files meta) { throw "meta/ tracked in ${C}: do not launch" }
  if (Test-Path "$C/meta") { throw "meta/ present in ${C}: do not launch" }
}
```

### 6.3 Launch: two PowerShell windows at once

Window 1 (3A):

```powershell
$n = "twentyfourth"; $C = "C:/wt/h3-d24"
Set-Location $C
$env:CLAUDE_CODE_DISABLE_AUTO_MEMORY = "1"
$cfg = Get-Content "$C/.claude/settings.json" -Raw | ConvertFrom-Json
$allow = ($cfg.permissions.allow -join ",")
$deny = ($cfg.permissions.deny -join ",")
& "C:\Users\a343o\AppData\Roaming\Claude\claude-code\2.1.281\claude.exe" -p "Begin from prompt/$n/prompt.md." --model claude-opus-5-5 --setting-sources project --strict-mcp-config --disable-slash-commands --no-chrome --output-format stream-json --verbose --allowedTools $allow --disallowedTools $deny *> "C:/wt/h3-$n.transcript.jsonl"
"exit: $LASTEXITCODE"
```

Window 2 (3B): the same lines, with the first line
`$n = "twentyfifth"; $C = "C:/wt/h3-d25"`.

These are `../launch.md` §3's flags, unchanged. The settings object is named
`$cfg`, so it cannot overwrite a snapshot id held in `$S` in the same window.

### 6.4 Landing both on one branch

```powershell
$R = "C:/Users/a343o/source/repos/H3V7N5QF"
$L = "C:/wt/h3-twins-land"
git -C $R fetch C:/wt/h3-d24 derivation/twentyfourth:refs/heads/run/twentyfourth
git -C $R fetch C:/wt/h3-d25 derivation/twentyfifth:refs/heads/run/twentyfifth
git -C $R fetch origin
git -C $R worktree add -b derivation/twentyfourth-twentyfifth $L origin/main
git -C $L cherry-pick "snapshot/twentyfourth..run/twentyfourth"
$A = git -C $L rev-parse HEAD
git -C $R range-diff "snapshot/twentyfourth..run/twentyfourth" "origin/main..$A"          # every line "="
git -C $L cherry-pick "snapshot/twentyfifth..run/twentyfifth"
git -C $R range-diff "snapshot/twentyfifth..run/twentyfifth" "$A..derivation/twentyfourth-twentyfifth"
```

- **The first twin lands as in `../launch.md`.** If it conflicts, `main`
  moved: stop and report.
- **The second twin is expected to conflict** in the files both runs
  register in: `CLAUDE.md` (both append), `lean4_core/lakefile.toml`,
  `ci/check_mutation_bite.py`, `ci/check_axiom_citations.py`, and an earlier
  derivation's `change_log.md`.
- **Resolving it.** `git -C $L diff --name-only --diff-filter=U` must list
  only those files. Join both sides: keep every line or list entry either
  run added, the twenty-fourth's first, and change nothing else. Then run
  `git -C $L add <file>` and `git -C $L cherry-pick --continue`.
- **Any other conflicted path:** run `git -C $L cherry-pick --abort`, stop
  and report. Do not resolve a conflict inside a run's own files.
- **Reading the range-diff.** The second one shows `=` for every commit, or
  `!` only for hunks in those files. The pull request lists each joined
  hunk.
- **Gates on the joined tip.** Before pushing, run every gate in both tasks'
  "Done" in the foreground in `$L`. That includes
  `lake +leanprover/lean4:v4.33.1 -d lean4_core build`, with its exit code
  read on its own line, and both `code/run_<n>.py --check`. Each run passed
  its gates alone, but only the joined tip shows the two together.
- **Push.** `git -C $L push -u origin derivation/twentyfourth-twentyfifth`.
  Have a second model review both runs, and open one pull request. Its body
  lists both runs' original commit ids beside the new ones.
- **After the merge.** Delete `snapshot/twentyfourth`,
  `snapshot/twentyfifth`, `run/twentyfourth` and `run/twentyfifth`. Remove
  both clones and the landing worktree.

## 7. After the runs

1. Audit both transcripts from outside: no web, server or messaging tool
   call, no read outside the clone, and no outside words in the seed, task
   or paper body.
2. Score A0 to A9 and B0 to B8 verbatim. Write the order test's verdict in
   `score.md` here, from the two papers.
3. Fill each twin's rung record (`../rubric.md`).
