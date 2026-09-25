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
| `ci/check_prose_watchlist.py` scope | `prompt/` is excluded, so nothing above is counted. | Whether the watchlist should scan `prompt/` is an author decision (see the H1 packet's decision table). |
| `meta/next_ten/*/prompt.md`, `meta/next_ten/make_packages.py` | Eleven citations of the missing `docs/index/topics.md`. | Those packages are being run in open pull request #45; the fix belongs after it lands. |
| git history | A run in a worktree that omits `meta/` can still read it with `git show` or `git log -p`. | Blind by instruction on this point. A stronger fix is a run repository without that history; not done. |
| deny patterns | Shell deny patterns match command prefixes. A script (for example Python's `urllib`) can still open a connection, and `lake` fetches a missing dependency by itself. | The climbing track removes the `lake` case (its Lean package has no dependency). The rest rests on instruction. |

## The clean-room launch, for every later derivation

1. The author installs the seed and task under `prompt/<n>/` through a pull
   request, as before.
2. The operator freezes the predictions: commit the SHA-256 of the
   prediction file before the run. The plaintext stays in `meta/`, which the
   run's worktree omits.
3. A fresh worktree from `origin/main`, with a sparse checkout that omits
   `meta/`. No junction to another checkout's `.lake/`.
4. The session starts with project settings only, no outside servers, no
   skills, and no browser tools. Each packet gives the exact command.
5. The run commits on its branch and does not push. The operator pushes,
   has a second model review the run, and opens the pull request.
6. The transcript is audited from outside the worktree. The run's seed,
   prompt and paper body carry no outside vocabulary. Outside words appear
   only in the paper's final section.
