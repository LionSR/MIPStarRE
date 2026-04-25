#!/usr/bin/env python3
"""Regression tests for scripts/lean_linter_warning_report.py."""

from __future__ import annotations

import json
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from lean_linter_warning_report import (  # noqa: E402
    LeanWarning,
    main,
    parse_warnings,
    render_text_report,
    report_dict,
)


class LeanLinterWarningReportTests(unittest.TestCase):
    def test_parse_uses_followup_linter_note_for_category(self) -> None:
        log = textwrap.dedent(
            """\
            MIPStarRE/LDT/Foo.lean:10:4: warning: declaration uses 'sorry'
            Note: This linter can be disabled with `set_option linter.unusedVariables false`
            MIPStarRE/LDT/Bar.lean:20:8: warning: try 'simp' instead of 'simpa'
            """
        )
        self.assertEqual(
            parse_warnings(log),
            [
                LeanWarning(
                    path="MIPStarRE/LDT/Foo.lean",
                    line=10,
                    column=4,
                    category="unusedVariables",
                    message="declaration uses 'sorry'",
                    raw="MIPStarRE/LDT/Foo.lean:10:4: warning: declaration uses 'sorry'",
                ),
                LeanWarning(
                    path="MIPStarRE/LDT/Bar.lean",
                    line=20,
                    column=8,
                    category="other",
                    message="try 'simp' instead of 'simpa'",
                    raw="MIPStarRE/LDT/Bar.lean:20:8: warning: try 'simp' instead of 'simpa'",
                ),
            ],
        )

    def test_parse_falls_back_to_known_linter_name_in_message(self) -> None:
        log = "MIPStarRE/LDT/Foo.lean:7:1: warning: try 'simp' instead of 'simpa'; linter.unnecessarySimpa\n"
        warnings = parse_warnings(log)
        self.assertEqual(len(warnings), 1)
        self.assertEqual(warnings[0].category, "unnecessarySimpa")

    def test_report_dict_and_text_report_count_categories(self) -> None:
        warnings = parse_warnings(
            textwrap.dedent(
                """\
                MIPStarRE/A.lean:1:1: warning: linter.flexible: declaration uses flexible syntax
                MIPStarRE/B.lean:2:1: warning: linter.flexible: declaration uses flexible syntax
                """
            )
        )
        self.assertEqual(report_dict(warnings)["category_counts"], {"flexible": 2})
        rendered = render_text_report(warnings)
        self.assertIn("warnings found: 2", rendered)
        self.assertIn("  - flexible: 2", rendered)

    def test_cli_writes_reports_and_count_output(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            log_path = root / "lean.log"
            json_path = root / "report.json"
            text_path = root / "report.txt"
            output_path = root / "github-output.txt"
            log_path.write_text(
                "MIPStarRE/LDT/Foo.lean:3:5: warning: linter.style.setOption: set_option command should appear after imports\n",
                encoding="utf-8",
            )
            self.assertEqual(
                main(
                    [
                        "--log",
                        str(log_path),
                        "--json",
                        str(json_path),
                        "--text",
                        str(text_path),
                        "--count-output",
                        str(output_path),
                    ]
                ),
                0,
            )
            report = json.loads(json_path.read_text(encoding="utf-8"))
            self.assertEqual(report["warning_count"], 1)
            self.assertEqual(report["category_counts"], {"style.setOption": 1})
            self.assertIn("warnings found: 1", text_path.read_text(encoding="utf-8"))
            self.assertIn("warning_count=1", output_path.read_text(encoding="utf-8"))
            self.assertIn("actionable_warnings=true", output_path.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
