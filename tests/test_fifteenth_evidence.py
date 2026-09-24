from __future__ import annotations

import json
from pathlib import Path

import pytest

from ninth.explore import explore as explore_ninth
from ninth.state import DState, empty
from fifteenth import __main__ as cli
from fifteenth import evidence
from fifteenth.admission import admitted_record, not_admitted_record
from fifteenth.changes import admission_counts
from fifteenth.evidence import (
    Plan,
    admissions_ok,
    compare_with_ninth,
    ninth_ok,
    run_tag,
    tagged_ok,
    write_all,
    write_given,
    write_run,
    write_tagged,
)
from fifteenth.explore import explore
from fifteenth.invariants import check_admissions

SMALL = Plan(
    bound=3,
    rounds=4,
    deep_bound=2,
    deep_rounds=3,
    two_term_rounds=4,
    log_bound=2,
    log_rounds=2,
    tagged_bound=2,
    tagged_rounds=4,
)


def test_plan() -> None:
    assert Plan().bound == 3 and Plan().rounds == 6 and Plan().tagged_bound == 2
    assert Plan().runs() == ((3, 6), (3, 5), (2, 8)) and SMALL.runs() == ((3, 4), (2, 3), (2, 4))
    assert run_tag(3, 4) == "bound3_rounds4"


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    runs = summary["runs"]
    tagged = summary["tagged"]
    given = summary["given"]
    assert isinstance(runs, dict) and isinstance(tagged, dict) and isinstance(given, dict)
    assert given["r_and_s_same_admission"] and given["admission_not_assertion"] and given["reaching_does_not_admit"]
    for tag, run in runs.items():
        assert cli.run_ok(run), tag
        assert run["results_that_reach_what_is_given"] == 1
        assert "is_admitted" not in run["admission_statements_holding_of_every_result"]
        assert "is_not_admitted" in run["admission_statements_holding_of_every_result"]
    assert tagged_ok(tagged)
    assert tagged["one_term_not_admitted_cost"] == 1
    admitted_cost = tagged["one_term_admitted_cost"]
    assert admitted_cost is not None and int(str(admitted_cost)) > 1
    names = {p.name for p in tmp_path.iterdir()}
    assert "given.json" in names and "tagged.json" in names and "summary.json" in names
    assert "attempts_bound2_rounds2.jsonl" in names
    given_doc = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given_doc["the_first_change_does_not_admit"]
    assert given_doc["r_and_s_same_admission"]
    two = runs["bound2_rounds4"]
    assert two["two_term_rounds_equal_closed_form"] is True
    assert two["admissions"]["reaching_never_admits"] is True


def test_check_admissions_reports_disagreements(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 2, 4)
    edges = check_admissions(expl)
    assert edges.checked > 0 and not edges.reaching_admits and not edges.cannot_admit
    assert not edges.assertion_records and not edges.kind_records
    assert not edges.of_relation and not edges.cross_relation_disagree
    assert edges.not_admitted == edges.checked and edges.admitted == 0
    monkeypatch.setattr("fifteenth.explore.admission_of_reaching", lambda _s: admitted_record())
    forced = check_admissions(expl)
    assert forced.reaching_admits
    monkeypatch.setattr("fifteenth.explore.admission_of_reaching", evidence.admission_of_reaching)
    # A relation-dependent record makes an asymmetric result disagree with its
    # r/s exchange, so the cross-relation check fires.
    from fifteenth.admission import admitted_record as _adm, not_admitted_record as _nadm

    monkeypatch.setattr(
        "fifteenth.invariants.admission_of_reaching",
        lambda s: _adm() if s.total_r > s.total_s else _nadm(),
    )
    assert check_admissions(expl).cross_relation_disagree
    monkeypatch.setattr("fifteenth.invariants.admission_of_reaching", evidence.admission_of_reaching)
    monkeypatch.setattr("fifteenth.invariants.can_admit", lambda _s: False)
    assert check_admissions(expl).cannot_admit
    monkeypatch.setattr("fifteenth.invariants.can_admit", lambda _s: True)
    monkeypatch.setattr("fifteenth.admission.Admission.is_assertion", lambda self: True)
    assert check_admissions(expl).assertion_records
    monkeypatch.setattr("fifteenth.admission.Admission.is_assertion", lambda self: False)
    monkeypatch.setattr("fifteenth.invariants.admission_is_a_kind", lambda _r: True)
    assert check_admissions(expl).kind_records
    monkeypatch.setattr("fifteenth.invariants.admission_is_a_kind", lambda _r: False)
    monkeypatch.setattr("fifteenth.admission.Admission.is_of_relation", lambda self, rel: True)
    assert check_admissions(expl).of_relation


def test_admission_counts_can_count_admitted(monkeypatch: pytest.MonkeyPatch) -> None:
    total, admitted, refused = admission_counts(empty())
    assert total == 1 and admitted == 0 and refused == 1
    monkeypatch.setattr("fifteenth.changes.admission_of_reaching", lambda _s: admitted_record())
    total, admitted, refused = admission_counts(empty())
    assert admitted == 1 and refused == 0


def test_compare_with_ninth_notices(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore(empty(), 2, 3)
    good = compare_with_ninth(expl)
    assert ninth_ok(good) and good["same_results"]
    real = explore_ninth

    def drop_empty(start: DState, bound: int, rounds: int, keep_log: bool = False) -> object:
        got = real(start, bound, rounds, keep_log=keep_log)
        got.depth = {s: r for s, r in got.depth.items() if s.n != 0}
        return got

    monkeypatch.setattr(evidence, "explore_ninth", drop_empty)
    bad = compare_with_ninth(expl)
    assert not ninth_ok(bad) and bad["missing_results"] == [] and bad["extra_results"]
    real_seq = evidence.count_shortest_sequences

    def bump(expl_):  # type: ignore[no-untyped-def]
        got = real_seq(expl_)
        first = next(iter(got))
        got = dict(got)
        got[first] = got[first] + 1
        return got

    monkeypatch.setattr(evidence, "count_shortest_sequences", bump)
    monkeypatch.setattr(evidence, "explore_ninth", real)
    seq = compare_with_ninth(expl)
    assert seq["sequence_disagreements"]
    monkeypatch.setattr(evidence, "count_shortest_sequences", real_seq)
    shallow = explore(empty(), 3, 1)
    assert compare_with_ninth(shallow)["explored_equals_independent_count"]
    expl2 = explore(empty(), 2, 3)
    gone = next(s for s in list(expl2.depth) if s.n == 0)
    expl2.depth.pop(gone)
    lost = compare_with_ninth(expl2)
    assert not ninth_ok(lost) and lost["missing_results"] == [gone.key()]
    assert not lost["explored_equals_independent_count"]
    fake = dict(good)
    fake["round_disagreements"] = ["shifted"]
    assert not ninth_ok(fake)


def test_tagged_and_admissions_ok_can_fail() -> None:
    assert not tagged_ok(
        {
            "more_results_than_the_ninth": False,
            "tagged_cost_exceeds_size": True,
            "one_term_not_admitted_cost": 1,
            "one_term_size": 1,
            "one_term_admitted_cost": 2,
        }
    )
    assert not tagged_ok(
        {
            "more_results_than_the_ninth": True,
            "tagged_cost_exceeds_size": True,
            "one_term_not_admitted_cost": 1,
            "one_term_size": 1,
            "one_term_admitted_cost": None,
        }
    )
    assert not tagged_ok(
        {
            "more_results_than_the_ninth": True,
            "tagged_cost_exceeds_size": True,
            "one_term_not_admitted_cost": 1,
            "one_term_size": 1,
            "one_term_admitted_cost": 1,
        }
    )
    assert not admissions_ok(
        {
            "split_agrees": False,
            "checked": 1,
            "reaching_never_admits": True,
            "reaching_admits": [],
            "cannot_admit": [],
            "assertion_records": [],
            "kind_records": [],
            "of_relation": [],
            "cross_relation_disagree": [],
        }
    )
    assert not admissions_ok(
        {
            "split_agrees": True,
            "checked": 1,
            "reaching_never_admits": False,
            "reaching_admits": [],
            "cannot_admit": [],
            "assertion_records": [],
            "kind_records": [],
            "of_relation": [],
            "cross_relation_disagree": [],
        }
    )
    assert admissions_ok({"checked": 0})


def test_write_run_two_term_formula_can_fail(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "two_term_round_count", lambda _r: -1)
    run = write_run(tmp_path, 2, 3, SMALL)
    assert run["two_term_rounds_equal_closed_form"] is False
    assert not cli.run_ok(run)
    deep = write_run(tmp_path, 3, 3, SMALL)
    assert deep["two_term_rounds_equal_closed_form"] is None


def test_write_tagged_and_given(tmp_path: Path) -> None:
    given = write_given(tmp_path)
    tagged = write_tagged(tmp_path, 2, 4)
    assert given["r_and_s_same_admission"]
    assert tagged_ok(tagged)
    assert (tmp_path / "given.json").is_file() and (tmp_path / "tagged.json").is_file()
    assert not_admitted_record().written() == "not-admitted"


def test_given_admission_availability_uses_the_model(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    write_given(tmp_path)
    original = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert original["can_admit_empty"] and original["can_admit_one"]
    monkeypatch.setattr(evidence, "can_admit", lambda state: state.n == 0)
    write_given(tmp_path)
    altered = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert altered["can_admit_empty"] and not altered["can_admit_one"]


def test_main_writes_and_checks(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    out = tmp_path / "evidence" / "fifteenth"
    argv = [
        "--out",
        str(out),
        "--bound",
        "2",
        "--rounds",
        "4",
        "--deep-bound",
        "2",
        "--deep-rounds",
        "3",
        "--two-term-rounds",
        "4",
        "--log-bound",
        "2",
        "--log-rounds",
        "2",
        "--tagged-bound",
        "2",
        "--tagged-rounds",
        "4",
    ]
    assert cli.main(argv) == 0
    capsys.readouterr()
    assert cli.main(argv + ["--check"]) == 0
    out2 = capsys.readouterr().out
    assert "check: identical" in out2
    (out / "given.json").write_text("{}", encoding="utf-8")
    assert cli.main(argv + ["--check"]) == 1
