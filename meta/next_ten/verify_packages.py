"""Check every proposal against its exact parent bytes and declared edit site."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

from make_packages import DETAILS, EDITS, HERE, ROOT

EDIT_SENTENCES = {
    "C19": 2, "C21": 1, "C09": 2, "C07": 1, "C01": 1,
    "C04": 1, "C05": 2, "C25": 2, "C11": 1, "C17": 2,
}
OUTSIDE_WORDS = ("morphism", "functor", "category", "genesis", "immune", "antibody", "darwinian", "lamarckian")
REQUIRED_PROMPT_HEADINGS = ("## Task", "## Folders", "## Gates", "## Done")
REQUIRED_PLAN_HEADINGS = ("## Reading and alternatives", "## Rule-5 re-check", "## Phases", "## Bounds and stopping")


def main() -> None:
    items: list[dict[str, object]] = json.loads((HERE / "candidates.json").read_text(encoding="utf-8"))
    by_id = {str(item["id"]): item for item in items}
    ranking = json.loads((HERE / "ranking.json").read_text(encoding="utf-8"))
    selected: list[str] = ranking["top_ten"]
    assert len(selected) == 10 and set(selected) == set(DETAILS) == set(EDIT_SENTENCES)
    rows = []
    for rank, ident in enumerate(selected, 1):
        item = by_id[ident]
        parent = ROOT / "prompt" / str(item["parent"]) / "seed_prompt.md"
        folder = HERE / f"{rank:02d}-{item['slug']}"
        original = parent.read_bytes()
        old, new = (part.encode("utf-8") for part in EDITS[ident])
        edited = (folder / "seed_prompt.md").read_bytes()
        assert original.count(old) == 1
        assert edited == original.replace(old, new, 1), ident
        assert 1 <= EDIT_SENTENCES[ident] <= 2
        assert all(word not in edited.decode("utf-8").lower() for word in OUTSIDE_WORDS)
        diff = (folder / "diff.patch").read_text(encoding="utf-8")
        assert diff.startswith(f"--- prompt/{item['parent']}/seed_prompt.md\n")
        assert f"+++ meta/next_ten/{folder.name}/seed_prompt.md\n" in diff
        prompt = (folder / "prompt.md").read_text(encoding="utf-8")
        plan = (folder / "plan.md").read_text(encoding="utf-8")
        why = (folder / "why.md").read_text(encoding="utf-8")
        assert all(heading in prompt for heading in REQUIRED_PROMPT_HEADINGS)
        assert all(heading in plan for heading in REQUIRED_PLAN_HEADINGS)
        assert "**Falsifier:**" in why and "**Hypothesis, open:**" in why
        rows.append({
            "rank": rank, "id": ident, "parent": str(item["parent"]),
            "edited_sentences": EDIT_SENTENCES[ident],
            "unchanged_bytes_verified": True,
            "seed_words_only": True,
            "files": sorted(path.name for path in folder.iterdir() if path.is_file()),
        })
    prompt_status = subprocess.run(
        ["git", "status", "--porcelain", "--", "prompt/"], cwd=ROOT,
        capture_output=True, check=True,
    ).stdout.decode("utf-8", errors="replace").strip()
    assert not prompt_status, prompt_status
    output = {"packages": rows, "prompt_tree_touched": bool(prompt_status)}
    path = HERE / "package_checks.json"
    path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(f"verified {len(rows)} exact parent edits and complete proposal packages")


if __name__ == "__main__":
    main()
