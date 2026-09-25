# Launch and landing template (from H2 on)

**Status:** chosen operator procedure, adopted 2026-09-26 after the H1
history leak (`blindness.md`). A rung's packet fills in `<n>` (the ordinal,
for example `twentythird`), the clone path `<C>` and the model. The commands
are PowerShell and run from any directory outside the repository.

A run starts in a clone of a one-commit snapshot. Nothing reachable from it
carries an operator message, a `meta/` path, or the path of the source
repository. The run's commits are then replayed onto `main`.

## 1. Snapshot

```powershell
$R = "C:/Users/a343o/source/repos/H3V7N5QF"
git -C $R fetch origin
$M = git -C $R rev-parse origin/main
$env:GIT_INDEX_FILE = Join-Path $env:TEMP "h3-snapshot.index"
git -C $R read-tree $M
git -C $R rm -r -q -f --cached meta
$T = git -C $R write-tree
Remove-Item $env:GIT_INDEX_FILE; Remove-Item Env:GIT_INDEX_FILE
$S = git -C $R commit-tree $T -m "Snapshot"
git -C $R branch snapshot/<n> $S
"main $M -> snapshot $S"
```

- The temporary index leaves the main checkout's own index and files alone.
- Do **not** build the tree by piping `git ls-tree` into `git mktree` in
  PowerShell. The pipe appends CR to every name and silently corrupts the
  tree; this was tested on 2026-09-26.
- Record `$M` and `$S` for the pull request.

## 2. History-free clone

```powershell
$C = "<C>"
git clone --depth 1 --no-tags --single-branch --branch snapshot/<n> "file:///C:/Users/a343o/source/repos/H3V7N5QF" $C
git -C $C remote remove origin
git -C $C switch -c derivation/<n>
git -C $C branch -D snapshot/<n>
git -C $C reflog expire --expire=now --all
git -C $C gc -q --prune=now
git -C $C config user.name H3V7N5QF
git -C $C config user.email run@localhost
git -C $C log --all --format="%h %s"                          # must print one line: <S> Snapshot
if (git -C $C ls-files meta) { throw "meta/ tracked: do not launch" }
if (Test-Path "$C/meta") { throw "meta/ present: do not launch" }
```

## 3. Launch (headless)

```powershell
Set-Location $C
$env:CLAUDE_CODE_DISABLE_AUTO_MEMORY = "1"
& "C:\Users\a343o\AppData\Roaming\Claude\claude-code\2.1.281\claude.exe" -p "Begin from prompt/<n>/prompt.md." --model claude-opus-5-5 --setting-sources project --strict-mcp-config --disable-slash-commands --no-chrome --output-format stream-json --verbose --disallowedTools "WebFetch,WebSearch" *> "C:/wt/h3-<n>.transcript.jsonl"
"exit: $LASTEXITCODE"
```

The transcript lands outside both repositories. The flags are H1's; see
`h1_cancellation/packet.md` §6 for what each does.

## 4. Landing

```powershell
git -C $R fetch $C derivation/<n>:refs/heads/run/<n>
git -C $R worktree add -b derivation/<n> "C:/wt/h3-<n>-land" origin/main
git -C "C:/wt/h3-<n>-land" cherry-pick "snapshot/<n>..run/<n>"
git -C $R range-diff "snapshot/<n>..run/<n>" "origin/main..derivation/<n>"   # every line "="
git -C $R diff --stat run/<n> derivation/<n> -- . ":(exclude)meta"           # empty if main has not moved
git -C "C:/wt/h3-<n>-land" push -u origin derivation/<n>
```

- The replayed commits keep the run's author and messages. The committer
  and the commit ids change, so the pull request body lists the run's
  original ids beside the new ones.
- If `main` moved after the snapshot and the cherry-pick conflicts, stop
  and report. Do not resolve a conflict inside a run's files.
- After the merge, delete `snapshot/<n>` and `run/<n>` and remove the clone.

## Tested, 2026-09-26

The test used a throwaway snapshot of `90f4479` (tree `1b8aee96…`, the same
from Git Bash and from the PowerShell commands above) and the clone steps of
§2:

- `git log` and `git log --all` each printed exactly one line,
  `2b36371 Snapshot`.
- There was one ref, no reflog, no remote, no file under `meta/` tracked or
  on disk, and no trace of the source path in `.git/`.
- Two commits made in the clone (a `CLAUDE.md` append and a new file) were
  fetched and cherry-picked onto `origin/main` with no conflict.
  `git range-diff` showed both as `=`, and the tip's tree equalled the
  clone's tip outside `meta/`.
- The throwaway refs, worktree and clone were removed.
