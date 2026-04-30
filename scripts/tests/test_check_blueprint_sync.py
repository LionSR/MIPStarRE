#!/usr/bin/env python3
"""Regression tests for scripts/check_blueprint_sync.py."""

from __future__ import annotations

import runpy
import sys
import unittest
from pathlib import Path
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import blueprint_leanok_axioms  # noqa: E402


class CheckBlueprintSyncWrapperTests(unittest.TestCase):
    def _run_wrapper(self, argv: list[str]) -> tuple[int | None, list[list[str]]]:
        script = SCRIPT_DIR / "check_blueprint_sync.py"
        calls: list[list[str]] = []

        def fake_main() -> int:
            calls.append(sys.argv[1:].copy())
            return 7

        old_argv = sys.argv.copy()
        try:
            sys.argv = [str(script), *argv]
            with mock.patch.object(blueprint_leanok_axioms, "main", fake_main):
                with self.assertRaises(SystemExit) as cm:
                    runpy.run_path(str(script), run_name="__main__")
            return cm.exception.code, calls
        finally:
            sys.argv = old_argv

    def test_injects_ci_for_legacy_callers(self) -> None:
        code, calls = self._run_wrapper(["--skip-axiom-check"])

        self.assertEqual(code, 7)
        self.assertEqual(calls, [["--skip-axiom-check", "--ci"]])

    def test_does_not_duplicate_explicit_ci_flag(self) -> None:
        code, calls = self._run_wrapper(["--ci", "--skip-axiom-check"])

        self.assertEqual(code, 7)
        self.assertEqual(calls, [["--ci", "--skip-axiom-check"]])


if __name__ == "__main__":
    unittest.main()
