# H1 "cancellation": launch packet

**Status:** prepared 2026-09-24. On 2026-09-25 the author adopted the six
decisions of §8 as written (`../rulings.md`). The seed and task are
installed as `prompt/twentysecond/`, byte for byte. The class is frozen.
Launch waits only for the install to merge. This packet is chosen
apparatus, outside the seal. The files a run will see (`seed_prompt.md`,
`prompt.md`) use only the parent seed's words and this repository's own.

| file | role | SHA-256 (LF bytes) |
|---|---|---|
| `seed_prompt.md` | the seed, to install as `prompt/twentysecond/seed_prompt.md` | `dd6ea130764ddc6336ba4e21adcac1493cfca11312574dabf25c9859cddefd04` |
| `prompt.md` | the task, to install as `prompt/twentysecond/prompt.md` | `a09505016125a4d53a653ebbfb53aef34cff86b846756f34b08e80197409fc3d` |
| `prediction.md` | the frozen prediction, native words only | `97dd4116eb49f6a9a595c5fc2a81d8d298fb36a36e8065f2f438cf6758999ed4` (also in `prediction.sha256`) |

This checkout converts line endings, so check a digest against the committed
blob, not the working file:
`git show HEAD:meta/climbing/h1_cancellation/prediction.md | sha256sum`.

## 1. The one sentence

The parent is the ninth seed (`prompt/ninth/seed_prompt.md`, SHA-256
`7231e4280445abcc74f5fc22e5c741178cae507854d93af49878404fc1a9d135`): two
relations, multiplicities, nothing given, the four kinds of change, no ban.
One sentence is replaced; nothing else changes.

```diff
-Two results that differ only in how their terms are written are the same result.
+Two results that differ only in how their terms are written, or only by an `xry` and an `xsy` asserted together, are the same result.
```

## 2. Licence check against the rubric (`meta/climbing/rubric.md`)

| rule | how H1 meets it |
|---|---|
| L1, one demand in the parent's words | The task asks: "In the ninth, can an addition undo an earlier addition? Can it here?" It uses seed words only, and the answer is asked for, not given. |
| L2, exhaustion by an invariant | The ninth's D4: every change moves the size by exactly one, so additions only ever raise it and no addition is undone. The run must re-prove this in `lean4_core/`, since it cannot import the ninth's library. |
| L3, the smallest member of the frozen class | "cancel" is one replaced sentence. "raise" also lets an addition undo earlier ones (on two terms, adding `xry` then `ysx` is one raising), but it needs two sentences. By inspection, no other member of the draft class meets the demand. **Precondition:** the class must be frozen first (D5). |
| L4, states or steps change | Witness: on two terms, the ninth's results "`xry` and `xsy` once each" and "nothing asserted" become one result. |
| L5, Lean with the small axiom set and the rung pair | The task requires a Lake package with no `require`, a report writer that refuses any axiom other than `propext` and `Quot.sound`, and the pair of maps: one to one in, a map back that may answer "none". |
| L6, ablation after the merge | Once H1 merges: strike or revert the changed sentence and each sentence it interacts with (sameness, removal, the record), and rerun the bounded exploration. |

## 3. The task

`prompt.md` follows the ninth task's layout, with four differences:

- It names only the ninth's line as inputs.
- It carries the demand as a question and requires the pair of maps.
- It moves the Lean work to a package with no outside library, under the
  small axiom set.
- It tells the run to commit and not push.

It carries none of the phrasing listed in `meta/climbing/blindness.md`: no
path this repository lacks, and no presupposed answer.

## 4. The frozen prediction

`prediction.md` holds nine predictions, P1 to P9, in native words: sameness
by *difference* per ordered pair, and the plain form (P1); the readings the
run must keep (P2); fewest changes equal to the *spread* (P3); the demand
answered (P4); the step law surviving for the *signed total* and failing for
the spread, with a witness where it drops 5 to 2 (P5); the exchange (P6);
reachability (P7); round-by-round correspondence with the ninth (P8); and
the pair of maps, with the smallest "none" witness and the loss per merge
(P9). The central claim is P1, P3 and P5 together: counts with a sign, one
plain member per result, and the parts that remain once opposite
assertions cancel.

## 5. The rung record, as expected

To be filled from evidence after the run, in `record.md`:

| field | expected |
|---|---|
| source | the seventh (one relation, multiplicities, nothing given) |
| protected distinctions | every seventh result stays different: multiplicities read as differences, one to one |
| same-level attempts | the ninth's additions, exhausted by the size invariant (the ninth's D4, re-proved) |
| residual | an addition that undoes an earlier addition |
| step preservation | each of the seventh's changes is carried to a change here |
| rung pair | in: multiplicities as differences. Back: "none" on a difference below zero. Witness: one term asserting `xsx` once. |
| read-back check | Lean, and the whole bounded exploration |
| cost | fewest changes equal the spread (P3) |
| smallest member | "cancel", by sentence count against the frozen class |

## 6. Launch, with isolation

*H1 ran with the steps below. From H2 on, `../launch.md` replaces steps 3 and 4 with a history-free clone, because a worktree exposes commit messages (`../blindness.md`).*

The decisions are adopted and P0 is merged. The commands are PowerShell. In
Git Bash, prefix the `sparse-checkout` line with `MSYS_NO_PATHCONV=1`, or
the `/meta/` pattern is rewritten into a Windows path. This was tested on
2026-09-24.

1. **Install (done).** `seed_prompt.md` and `prompt.md` are installed byte
   for byte as `prompt/twentysecond/`, where `.gitattributes` keeps them
   LF, with the digests above. `paper/change_log.md` item 42 logs the
   install. The watchlist pin counts both files.
2. **Freeze.** After the install merges, confirm three things:
   - `git show origin/main:meta/climbing/h1_cancellation/prediction.md | sha256sum`
     matches `prediction.sha256`;
   - the same holds for `extension_class.md` and `extension_class.sha256`;
   - `git show origin/main:prompt/twentysecond/seed_prompt.md | sha256sum`
     is `dd6ea130…`.
3. **Worktree, omitting `meta/`:**

   ```powershell
   git -C C:/Users/a343o/source/repos/H3V7N5QF fetch origin
   git -C C:/Users/a343o/source/repos/H3V7N5QF worktree add -b derivation/twentysecond C:/wt/h3-d22 origin/main
   git -C C:/wt/h3-d22 sparse-checkout set --no-cone '/*' '!/meta/'
   if (Test-Path C:/wt/h3-d22/meta) { throw "meta/ present: do not launch" }
   ```

   Do not link `lean4/.lake` to another checkout. The run's Lean package
   has no dependency, so it needs none. In this worktree the watchlist sets
   aside the pins of the `meta/` files it does not hold, and passes.
4. **Launch (headless Claude, from the worktree root):**

   ```powershell
   Set-Location C:/wt/h3-d22
   $env:CLAUDE_CODE_DISABLE_AUTO_MEMORY = "1"
   & "C:\Users\a343o\AppData\Roaming\Claude\claude-code\2.1.281\claude.exe" -p "Begin from prompt/twentysecond/prompt.md." --model claude-opus-5-5 --setting-sources project --strict-mcp-config --disable-slash-commands --no-chrome --output-format stream-json --verbose --disallowedTools "WebFetch,WebSearch" *> C:/wt/h3-d22.transcript.jsonl
   "exit: $LASTEXITCODE"
   ```

   What each part does:

   - The binary is 2.1.281; the one on `PATH` is too old for the model.
   - `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1` keeps memory off. The settings
     also say `autoMemoryEnabled: false`.
   - `-p` runs headless. The prompt comes right after it, so no list-taking
     flag can swallow it. In this mode a tool outside the allow list is
     refused, never asked about.
   - `--setting-sources project` loads only the tracked
     `.claude/settings.json`, with its deny list, and no user settings or
     plugins.
   - `--strict-mcp-config` with no `--mcp-config` loads no outside server.
   - `--disable-slash-commands` turns off every skill.
   - `--disallowedTools`, last, repeats the two web denials.
   - The transcript is written outside the worktree, so the run cannot read
     or commit it. It is what the audit in §7 reads.

   **Probed 2026-09-25** with this binary and these flags in a sparse
   worktree, using a cheap model and throwaway prompts. The project
   settings loaded (15 allow rules, 47 deny rules), and `git ls-remote
   origin` was refused by a deny rule. The following ran: `python`,
   `python -m pytest`, `python -m mypy`, `python code/xry/gate.py`, `lake`
   with the pinned toolchain, `git status`, `git log`, the Write tool,
   `git add` and `git commit`. `python -c "…"` was refused: headless mode
   will not approve inline interpreter code, so a run writes its scripts
   to files.

   If another runner is used, it reads `AGENTS.md`, which points to
   `CLAUDE.md`. Its own network switch must be off, and its grade records
   how isolation was enforced.
5. **During the run,** nothing is sent to the session. The run asks no
   questions.

## 7. After the run

1. Audit the transcript from outside the worktree. There must be no web,
   server or messaging tool call and no read outside `C:/wt/h3-d22`. The
   seed, prompt and paper body must carry no outside words; the watchlist
   census must match its pin.
2. Push: `git -C C:/wt/h3-d22 push -u origin derivation/twentysecond`. Have
   a second model review the run. Open the pull request against `main`.
3. Run the operator acceptance of `meta/climbing/rubric.md` at the exact
   head.
4. Score P1 to P9 in `score.md` and fill `record.md`, both in this folder.
5. Run the L6 ablations as a separate, later packet.

**Cost** (by the earlier estimate, not measured): 3 to 6 agent hours, a
full local suite of about 90 minutes, about 2 hours of meta work, and 1 to
1.5 author hours.

## 8. Decisions (adopted by the author as written, 2026-09-25)

| # | decision | recommendation |
|---|---|---|
| D1 | Adopt a fence for the outside level table's vocabulary, a clause that no paper or meta file claims this track reached any outside structure independently (every climbing seed is operator-targeted), and watchlist digests for that table's key terms. | Adopt the clause now, in `meta/README.md`. Keep the table's vocabulary and the comparison rows out of this repository, with the table's owner, and add only the digests here. Also make the watchlist scan `prompt/` with a pin, so prompts like the sixteenth to twenty-first are counted. |
| D2 | For the first fills (round 3), use the licence order (the smallest fill that tells a survivor apart), the outside table's order (the three-term fill first), or both as twin siblings. | Both, as twins on one branch. Their comparison is the only direct test of whether the licence order matches the table's. |
| D3 | The H1 parent: the ninth (no ban, loops allowed; the cleanest signed counts) or the fifth (one relation, the ban kept; closer to cells with distinct ends). | The ninth, as packeted: one sentence, and loops keep the smallest witnesses small. Record the fifth as the unchosen variant. It needs a sentence letting a multiplicity fall below zero, and it changes round 3's prediction. |
| D4 | In round 2, accept that adding a term breaks the raising sameness (growth creates survivors), or fix the set of terms during repair with a finite-letters sentence. | Accept it for H2: this calculus's own growth is data. The run expands results and forms the classes afterwards. Run the fixed-term-set variant as an L6 sibling, because any later question about whether survivors run out needs a fixed set of terms. |
| D5 | Freeze the extension class (`meta/climbing/extension_class.md`), including whether native rungs aim at results needing division plus further supplied arithmetic laws. | Freeze it with H1's launch, once each member's sentence is written out in full. H1 needs only "cancel" to be in it. Exclude that arithmetic band from native rungs, and leave it to supplied encodings. |
| D6 | The clean-room protocol, and what to do with `AGENTS.md`. | Adopt the protocol in `meta/climbing/blindness.md`. `AGENTS.md` is handled in the P0 change: the stale untracked copy moved out of the checkout, and a tracked pointer to `CLAUDE.md` was added. Confirm both. |
