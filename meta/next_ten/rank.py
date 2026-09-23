"""Apply the declared rubric and show independent ±50% weight sensitivity."""

from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
WEIGHTS = (4, 3, 2, 4, 3, 2, 2)
AXES = ("H", "N", "R", "C", "M", "G", "L")


def ranked(items: list[dict[str, object]], weights: tuple[float, ...]) -> list[tuple[str, float]]:
    rows = []
    for item in items:
        scores = item["scores"]
        assert isinstance(scores, list) and len(scores) == 7
        assert all(isinstance(v, int) and 0 <= v <= 5 for v in scores)
        rows.append((str(item["id"]), sum(w * v for w, v in zip(weights, scores, strict=True))))
    return sorted(rows, key=lambda row: (-row[1], row[0]))


def main() -> None:
    items: list[dict[str, object]] = json.loads((HERE / "candidates.json").read_text(encoding="utf-8"))
    assert len(items) >= 25 and len({str(x["id"]) for x in items}) == len(items)
    assert all((HERE.parents[1] / "prompt" / str(x["parent"]) / "seed_prompt.md").is_file()
               if x["parent"] != "base" else (HERE.parents[1] / "prompt" / "seed_prompt.md").is_file()
               for x in items)
    all_scores = ranked(items, tuple(map(float, WEIGHTS)))
    eligible = [item for item in items if "prototype_rejected" not in item]
    baseline = ranked(eligible, tuple(map(float, WEIGHTS)))
    cutoff = baseline[9][1]
    assert baseline[10][1] != cutoff, "cutoff tie: keep all tied candidates and revise the proposal count"
    kept = {id_ for id_, _ in baseline[:10]}
    perturbations = []
    for i, axis in enumerate(AXES):
        for factor in (0.5, 1.5):
            variant = list(map(float, WEIGHTS))
            variant[i] *= factor
            order = ranked(eligible, tuple(variant))
            variant_cutoff = order[9][1]
            top = {id_ for id_, score in order if score >= variant_cutoff}
            perturbations.append({
                "axis": axis,
                "factor": factor,
                "entered": sorted(top - kept),
                "left": sorted(kept - top),
                "cutoff_tie": order[9][1] == order[10][1],
                "retained_at_cutoff": len(top),
            })
    output = {
        "weights": dict(zip(AXES, WEIGHTS, strict=True)),
        "candidates": len(items),
        "prototype_rejected": [str(item["id"]) for item in items if "prototype_rejected" in item],
        "all_scores": [{"id": id_, "score": score} for id_, score in all_scores],
        "ranked": [{"id": id_, "score": score} for id_, score in baseline],
        "top_ten": [id_ for id_, _ in baseline[:10]],
        "sensitivity": perturbations,
    }
    (HERE / "ranking.json").write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
