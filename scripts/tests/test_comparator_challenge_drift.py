#!/usr/bin/env python3
"""Regression tests for comparator challenge drift checking."""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "comparator" / "check_challenge_drift.py"
PR_CI = REPO_ROOT / ".github" / "workflows" / "pr-ci.yml"
README = REPO_ROOT / "scripts" / "comparator" / "README.md"

_spec = importlib.util.spec_from_file_location("check_challenge_drift", SCRIPT)
assert _spec is not None and _spec.loader is not None
check_challenge_drift = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(check_challenge_drift)


class ComparatorChallengeDriftTests(unittest.TestCase):
    def test_clean_closure_rows_keeps_only_four_column_tsv_rows(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            raw = root / "closure.tsv"
            clean = root / "closure.clean.tsv"
            raw.write_text(
                "\n".join(
                    [
                        "noise from an unexpected diagnostic",
                        "Decl\tMIPStarRE/Foo.lean\t1\t2",
                        "too\tmany\tcolumns\tfor\tthis\trow",
                        "Generated\tMIPStarRE/Bar.lean\tNORANGE\tNORANGE",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )

            check_challenge_drift.clean_closure_rows(raw, clean)

            self.assertEqual(
                clean.read_text(encoding="utf-8"),
                "Decl\tMIPStarRE/Foo.lean\t1\t2\n"
                "Generated\tMIPStarRE/Bar.lean\tNORANGE\tNORANGE\n",
            )

    def test_pr_ci_runs_drift_guard_after_lean_build_for_comparator_changes(self) -> None:
        workflow = PR_CI.read_text(encoding="utf-8")
        self.assertIn("comparator: ${{ steps.filter.outputs.comparator }}", workflow)
        self.assertIn("- 'scripts/comparator/**'", workflow)
        self.assertIn("needs.changes.outputs.comparator == 'true'", workflow)
        build = workflow.index("lake build MIPStarRE.LDT.Test.AxiomAudit")
        guard = workflow.index("python3 scripts/comparator/check_challenge_drift.py --root .")
        self.assertLess(build, guard)

    def test_readme_documents_update_command_and_footer_source(self) -> None:
        readme = README.read_text(encoding="utf-8")
        self.assertIn("python3 scripts/comparator/check_challenge_drift.py --root . --update", readme)
        self.assertIn("challenge_footer.lean", readme)
        self.assertIn("MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean", readme)


if __name__ == "__main__":
    unittest.main()
