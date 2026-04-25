#!/usr/bin/env python3
"""Regression tests for scripts/audit_readme_freshness.py."""

from __future__ import annotations

import json
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from audit_readme_freshness import (  # noqa: E402
    PathReference,
    audit_ldt_submodule_count,
    audit_readme,
    audit_toolchain_versions,
    extract_path_references,
    main,
    missing_path_references,
    read_lakefile_mathlib_rev,
    render_json_report,
    render_text_report,
)


def _make_repo(root: Path, readme_text: str) -> Path:
    """Create a minimal repository fixture for README audits."""
    (root / "MIPStarRE" / "LDT" / "Basic").mkdir(parents=True)
    (root / "MIPStarRE" / "LDT" / "Pasting").mkdir(parents=True)
    (root / "docs").mkdir()
    (root / "docs" / "CONTRIBUTING.md").write_text("docs\n")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.28.0\n")
    (root / "lakefile.toml").write_text(
        textwrap.dedent(
            """\
            name = "Fake"

            [[require]]
            name = "mathlib"
            scope = "leanprover-community"
            rev = "v4.28.0"
            """
        )
    )
    readme = root / "README.md"
    readme.write_text(readme_text)
    return readme


class ExtractPathReferencesTests(unittest.TestCase):
    def test_extracts_markdown_links_and_inline_code_paths(self) -> None:
        text = textwrap.dedent(
            """\
            See [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md).
            The active source is `MIPStarRE/LDT/` and `lean-toolchain`.
            Ignore Lean names like `MIPStarRE.LDT.Basic` and `lake build`.
            ```bash
            lake env lean MIPStarRE/Missing.lean
            python3 ./scripts/audit_readme_freshness.py --readme ./README.md
            cat MIPStarRE.lean
            ```
            """
        )
        self.assertEqual(
            extract_path_references(text),
            [
                PathReference("docs/CONTRIBUTING.md", 1, "markdown-link"),
                PathReference("docs/CONTRIBUTING.md", 1, "inline-code"),
                PathReference("MIPStarRE/LDT/", 2, "inline-code"),
                PathReference("lean-toolchain", 2, "inline-code"),
                PathReference("MIPStarRE/Missing.lean", 5, "fenced-code"),
                PathReference("scripts/audit_readme_freshness.py", 6, "fenced-code"),
                PathReference("README.md", 6, "fenced-code"),
                PathReference("MIPStarRE.lean", 7, "fenced-code"),
            ],
        )


    def test_resolves_nested_tree_entries_in_fenced_blocks(self) -> None:
        text = textwrap.dedent(
            """\
            ```text
            MIPStarRE/
            ├── Quantum/
            │   └── Measurement.lean
            └── LDT/
                └── Basic/
            ```
            """
        )
        self.assertEqual(
            extract_path_references(text),
            [
                PathReference("MIPStarRE/", 2, "fenced-code"),
                PathReference("MIPStarRE/Quantum/", 3, "fenced-tree"),
                PathReference("MIPStarRE/Quantum/Measurement.lean", 4, "fenced-tree"),
                PathReference("MIPStarRE/LDT/", 5, "fenced-tree"),
                PathReference("MIPStarRE/LDT/Basic/", 6, "fenced-tree"),
            ],
        )

    def test_missing_path_references_reports_only_absent_paths(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "docs").mkdir()
            (root / "docs" / "CONTRIBUTING.md").write_text("ok\n")
            refs = [
                PathReference("docs/CONTRIBUTING.md", 3, "inline-code"),
                PathReference("docs/MISSING.md", 4, "inline-code"),
            ]
            self.assertEqual(
                missing_path_references(root, refs),
                [{"path": "docs/MISSING.md", "line": 4, "kind": "inline-code"}],
            )

    def test_generated_blueprint_decls_path_is_allowed_missing(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            refs = [PathReference("blueprint/lean_decls", 9, "fenced-code")]
            self.assertEqual(missing_path_references(root, refs), [])


class LayoutAuditTests(unittest.TestCase):
    def test_ldt_submodule_count_flags_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "MIPStarRE" / "LDT" / "Basic").mkdir(parents=True)
            (root / "MIPStarRE" / "LDT" / "Pasting").mkdir(parents=True)
            report = audit_ldt_submodule_count(
                root,
                "└── LDT/                   # Low individual degree test (13 submodules)\n",
            )
            self.assertEqual(report["actual"], 2)
            self.assertEqual(report["mismatches"], [{"line": 1, "count": 13}])

    def test_ldt_submodule_count_accepts_current_count(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "MIPStarRE" / "LDT" / "Basic").mkdir(parents=True)
            (root / "MIPStarRE" / "LDT" / "Pasting").mkdir(parents=True)
            report = audit_ldt_submodule_count(
                root,
                "└── LDT/                   # Low individual degree test (2 submodules)\n",
            )
            self.assertEqual(report["mismatches"], [])


class ToolchainAuditTests(unittest.TestCase):
    def test_toolchain_version_audit_flags_hardcoded_mismatches(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            readme = _make_repo(
                root,
                "Toolchain: Lean 4.27.0 and Mathlib v4.27.0.\n",
            )
            report = audit_toolchain_versions(root, readme.read_text())
            self.assertEqual(
                report["mismatches"],
                [
                    {"tool": "Lean", "line": 1, "mentioned": "4.27.0", "expected": "4.28.0"},
                    {"tool": "Mathlib", "line": 1, "mentioned": "v4.27.0", "expected": "v4.28.0"},
                ],
            )

    def test_no_hardcoded_versions_is_clean(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            readme = _make_repo(
                root,
                "Toolchain: See `lean-toolchain` and `lakefile.toml`.\n",
            )
            report = audit_toolchain_versions(root, readme.read_text())
            self.assertEqual(report["hardcoded_mentions"], [])
            self.assertEqual(report["mismatches"], [])

    def test_lakefile_mathlib_rev_normalizes_missing_v_prefix(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            readme = _make_repo(root, "Toolchain: Mathlib v4.28.0.\n")
            (root / "lakefile.toml").write_text(
                textwrap.dedent(
                    """\
                    [[require]]
                    name = "mathlib"
                    rev = "4.28.0"
                    """
                )
            )
            report = audit_toolchain_versions(root, readme.read_text())
            self.assertEqual(report["mathlib_rev"], "v4.28.0")
            self.assertEqual(report["mismatches"], [])

    def test_lakefile_mathlib_rev_is_order_insensitive(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "lakefile.toml").write_text(
                textwrap.dedent(
                    """\
                    [[require]]
                    rev = "4.28.0"
                    name = "mathlib"
                    scope = "leanprover-community"

                    [[lean_lib]]
                    name = "NotMathlib"
                    """
                )
            )
            self.assertEqual(read_lakefile_mathlib_rev(root), "v4.28.0")


class EndToEndAuditTests(unittest.TestCase):
    def test_audit_readme_json_text_and_cli(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            readme = _make_repo(
                root,
                textwrap.dedent(
                    """\
                    # Fake
                    See [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md).
                    └── LDT/ # Low individual degree test (2 submodules)
                    Toolchain: See `lean-toolchain` and `lakefile.toml`.
                    """
                ),
            )
            report = audit_readme(root, readme)
            self.assertFalse(report.is_flagged)
            json_payload = json.loads(render_json_report(report))
            self.assertFalse(json_payload["flagged"])
            self.assertIn("README freshness audit", render_text_report(report))
            self.assertEqual(
                main(["--root", str(root), "--readme", "README.md", "--fail-on-stale"]),
                0,
            )

    def test_cli_fail_on_stale_returns_nonzero(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(
                root,
                "└── LDT/ # Low individual degree test (13 submodules)\n",
            )
            self.assertEqual(main(["--root", str(root), "--fail-on-stale"]), 1)


if __name__ == "__main__":
    unittest.main()
