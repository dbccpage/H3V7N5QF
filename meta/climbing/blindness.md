# Blindness restored for later derivations (2026-09-24)

**Status:** chosen record, outside the derivational seal. It states what
could reach a blind run from outside, what was repaired, and what was left
as found. It is not evidence for any paper.

## Repaired

| what leaked | repair |
|---|---|
| Since commit `f255ba5` (2026-09-18 15:05), `.claude/settings.json` allowed the web tools, outside servers and inter-session messages, and denied nothing. The first and second derivations ran under enforced denial; the third through twenty-first were isolated by instruction only. | The deny list of `cb99d93` is restored, plus `git ls-remote`, `git submodule`, `uvx`, `elan` and `python -m pip`. Web fetch and search, outside servers, inter-session messages and agent listing leave the allow list and are denied. Reads outside the working directory are blocked. Connectors and project servers are off. |
| `CLAUDE.md`, which every Claude run loads, ended with the 2026-09-23 review plan and its outside and analogy vocabulary. | The section moved verbatim to `meta/review/plan_2026-09-23.md`. `CLAUDE.md` ends with a short procedural note on isolation instead. |
| `ci/OEWAS_GATES.md`, which the gates' docstrings and the sixteenth prompt point runs to, closed with two sections of analogy and one outside structural term. | The two sections moved verbatim to `meta/review/detector_design_notes.md`; one sentence in the introduction is reworded. |
| The docstring of `ci/check_prose_watchlist.py` named another repository. | Reworded. |
| An untracked `AGENTS.md` in the main checkout (268,976 bytes, 2026-09-23 15:03) was `CLAUDE.md` at `44a35ce` with only its first line changed (checked byte for byte, ignoring CR). A run reading it would see an older contract. | Moved out of the checkout to `C:/wt/_stale/H3V7N5QF_AGENTS.md.stale-2026-09-23` (SHA-256 `ee0a8cfb78bd03fadbe15e2c3e7cf7a3d8cdc88619165eb86c152bf5168cc56f`); its content is recoverable from `44a35ce` in any case. A tracked `AGENTS.md` now only points to `CLAUDE.md`, so it cannot go stale. |

The watchlist pin was regenerated for these moves only. `paper/change_log.md`
item 41 logs the change.

## Found and left as found

| where | what | why it stays |
|---|---|---|
| `prompt/sixteenth/` to `prompt/twentyfirst/`, `prompt.md` | Phrasing carried from outside this repository: "by exhaustive enumeration over a declared finite candidate space", "quotient only under an implemented isomorphism" and "strongest defensible terminal result" (sixteenth to twenty-first). "The repository's five-file pattern (`docs/index/topics.md`)", a path this repository does not have (seventeenth to twenty-first). Outside words in the task paragraphs: self-loop and irreflexivity (seventeenth), relabelling and orbit (eighteenth). The twenty-first asks "how much smaller the reachable set becomes", which presupposes the answer; the run refuted it. | `prompt/` is read-only (`CLAUDE.md`, base section), and these runs are finished, so their prompts are records. Later prompts are written from the packet template in `meta/climbing/`, which carries none of this. |
| `paper/change_log.md` item 40; `paper/second/change_log.md` item 15 | Name another repository and the review area's vocabulary. A run that reads its parent's change log sees them. | Change logs are append-only. The author may leave them or add a dated note. |
| `ci/check_prose_watchlist.py` scope | `prompt/` was excluded, so nothing above was counted. | **Resolved 2026-09-25** (ruling D1): `prompt/` is counted under a pin, so these prompts' hits are on the census. |
| `meta/next_ten/*/prompt.md`, `meta/next_ten/make_packages.py` | Eleven citations of the missing `docs/index/topics.md`. | Those packages are being run in open pull request #45; the fix belongs after it lands. **Resolved 2026-09-25:** #45 has merged, so the packages are records and their text stays. `meta/next_ten/README.md` carries a dated note: the path does not exist here, what it referred to, and what to read instead. |
| git history | A run in a worktree that omits `meta/` can still read it with `git show` or `git log -p`. **This happened in H1 (PR #48):** the run's `git log --stat` showed operator commit messages from #46 and #47, which summarize the rubric and the rulings, and file names under `meta/climbing/`. It did not show the prediction's content. | **Fixed 2026-09-26.** From H2 on, a run starts in a clone of a one-commit snapshot: no parent, a neutral message, and main's tree without `meta/`. From its HEAD no operator message and no `meta/` path can be reached (see `launch.md`, tested). |
| deny patterns | Shell deny patterns match command prefixes. A script (for example Python's `urllib`) can still open a connection, and `lake` fetches a missing dependency by itself. | The climbing track removes the `lake` case (its Lean package has no dependency). The rest rests on instruction. |

## The clean-room launch, for every later derivation

The full commands are in `launch.md`. In outline:

1. The author installs the seed and task under `prompt/<n>/` through a pull
   request.
2. The operator freezes the predictions: the SHA-256 of the prediction file
   is committed before the run. The plaintext stays in `meta/`, and nothing
   of `meta/` reaches the run.
3. **A history-free clone (from 2026-09-26).** The operator makes a
   snapshot commit whose tree is `main`'s tree without `meta/`. It has no
   parent and the message "Snapshot". The operator clones it at depth 1,
   one branch, no tags. The clone's remote is removed and its reflog
   emptied, so the clone records neither the source path nor any operator
   message. No junction to another checkout's `.lake/`.
4. The session starts with project settings only, no outside servers, no
   skills and no browser tools. Its transcript is written outside the
   repository.
5. The run commits on its branch in the clone and cannot push.
6. **Landing.** The operator fetches the run's branch into the main
   repository and cherry-picks the run's commits (snapshot..tip) onto a
   branch from `origin/main`. `git range-diff` must show every commit as
   equal (`=`). The replayed tip's tree equals the run's tip outside `meta/`
   when `main` has not moved. The operator pushes, has a second model review
   the run, and opens the pull request, with the run's original commit ids
   in its body.
7. The transcript is audited from outside. The run's seed, prompt and paper
   body carry no outside vocabulary. Outside words appear only in the
   paper's final section.

**What is left.** The run's `CLAUDE.md` and the base change log are
`main`'s, so their operator notes are visible; they are kept neutral. A
command could still reach a path outside the clone if the run guessed it.
That rests on instruction.
