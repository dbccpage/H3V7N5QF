"""Focused regressions for the operator runner, without running its heavy jobs."""

from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import run_baseline
import run_full_suite as suite


class CommandCoverageTests(unittest.TestCase):
    def test_current_plan_checks_all_25_evidence_families(self) -> None:
        planned = dict(suite.commands())
        self.assertEqual(len([name for name in planned if name.startswith('evidence_')]), 25)
        for ordinal in ('twentysecond', 'twentythird', 'twentyfourth', 'twentyfifth'):
            self.assertEqual(planned['evidence_' + ordinal],
                             [sys.executable, f'code/run_{ordinal}.py', '--check'])

    def test_current_plan_reports_all_25_axiom_families(self) -> None:
        planned = dict(suite.commands())
        self.assertEqual(len([name for name in planned if name.startswith('axioms_')]), 25)
        self.assertEqual(planned['axioms_twentyfifth'],
                         [sys.executable, 'code/lean_report_twentyfifth.py'])

    def test_current_plan_builds_both_pinned_lean_roots(self) -> None:
        planned = dict(suite.commands())
        for root, label in (('lean4', 'lean_build'), ('lean4_core', 'lean_core_build')):
            pin = (run_baseline.ROOT / root / 'lean-toolchain').read_text(encoding='utf-8').strip()
            self.assertEqual(planned[label], ['lake', '+' + pin, '-d', root, 'build'])

    def test_current_plan_includes_existing_citation_check_once(self) -> None:
        names = [name for name, _ in suite.commands()]
        self.assertEqual(names.count('axiom_citations'), 1)
        self.assertEqual(len(names), len(set(names)))

    def test_planned_python_entrypoints_exist(self) -> None:
        for name, argv in suite.commands():
            if argv[0] == sys.executable and argv[1] != '-m':
                self.assertTrue((run_baseline.ROOT / argv[1]).is_file(), name)
            if name.startswith('evidence_'):
                self.assertEqual(argv[-1], '--check')

    def test_each_current_launcher_is_included_exactly_once(self) -> None:
        planned = [argv[1] for _, argv in suite.commands() if argv[0] == sys.executable]
        launchers = [run_baseline.ROOT / 'code' / 'generate.py', run_baseline.ROOT / 'code' / 'lean_report.py']
        for pattern in ('generate_*.py', 'run_*.py', 'lean_report_*.py'):
            launchers.extend((run_baseline.ROOT / 'code').glob(pattern))
        for launcher in launchers:
            self.assertEqual(planned.count(launcher.relative_to(run_baseline.ROOT).as_posix()), 1)

    def test_main_executes_and_records_the_current_plan(self) -> None:
        plan = suite.commands()
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            with patch.object(sys, 'argv', ['run_full_suite.py', '--out', str(out)]), \
                    patch.object(suite, 'git', return_value='test-head'), \
                    patch('run_full_suite.subprocess.run', return_value=subprocess.CompletedProcess([], 0)) as run, \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(suite.main(), 0)
            self.assertEqual([call.args[0] for call in run.call_args_list], [argv for _, argv in plan])
            summary = json.loads((out / 'summary.json').read_text(encoding='utf-8'))
            self.assertEqual([row['name'] for row in summary['commands']], [name for name, _ in plan])
            self.assertIn('finished_utc', summary)

    def test_historical_baseline_plan_remains_21_families(self) -> None:
        names = [name for name, _ in run_baseline.commands()]
        self.assertEqual(len([name for name in names if name.startswith('evidence_')]), 21)
        self.assertNotIn('lean_core_build', names)


if __name__ == '__main__':
    unittest.main()
