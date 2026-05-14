#!/usr/bin/env python3
"""Regression tests for scripts/audit_new_proof_obligation_metadata.py."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from audit_new_proof_obligation_metadata import (  # noqa: E402
    _changed_lines_from_diff,
    _metadata_reason,
    find_metadata_findings,
    main,
)


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True, stdout=subprocess.PIPE)


def _make_repo(root: Path) -> Path:
    _git(root, "init")
    _git(root, "config", "user.email", "test@example.com")
    _git(root, "config", "user.name", "Test User")
    (root / "MIPStarRE" / "LDT").mkdir(parents=True)
    return root


def _commit_base(root: Path) -> None:
    _write(root / "MIPStarRE" / "LDT" / "Base.lean", "namespace MIPStarRE.LDT\n")
    _git(root, "add", ".")
    _git(root, "commit", "-m", "base")


class DiffLineTests(unittest.TestCase):
    def test_changed_lines_from_diff(self) -> None:
        diff = (
            "diff --git a/MIPStarRE/LDT/Foo.lean b/MIPStarRE/LDT/Foo.lean\n"
            "+++ b/MIPStarRE/LDT/Foo.lean\n"
            "@@ -0,0 +4,2 @@\n"
            "+def FooBridge : Prop := True\n"
            "+def Bar : Nat := 0\n"
        )
        self.assertEqual(
            _changed_lines_from_diff(diff),
            {"MIPStarRE/LDT/Foo.lean": {4, 5}},
        )


class MetadataTests(unittest.TestCase):
    def test_source_marker_and_paper_label_passes(self) -> None:
        doc = "/-- **Source:** Paper statement `\\label{lem:foo}`. -/"
        self.assertIsNone(_metadata_reason(doc))

    def test_plain_paper_label_needs_role_marker(self) -> None:
        doc = "/-- Paper statement `\\label{lem:foo}`. -/"
        self.assertIsNotNone(_metadata_reason(doc))

    def test_unfaithful_marker_needs_elimination(self) -> None:
        doc = (
            "/-- **Unfaithful:** This uses `FooBridge`; see issue #1579 and "
            "`\\label{lem:foo}`. -/"
        )
        self.assertIn("planned discharge", _metadata_reason(doc) or "")

    def test_proof_obligation_with_issue_and_elimination_passes(self) -> None:
        doc = (
            "/-- **Proof obligation:** This is internal to the proof of "
            "`\\label{lem:foo}`.  See issue #1579.  Elimination: prove it "
            "from the paper hypotheses. -/"
        )
        self.assertIsNone(_metadata_reason(doc))


class GitAuditTests(unittest.TestCase):
    def test_new_bridge_without_metadata_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _commit_base(root)
            _write(
                root / "MIPStarRE" / "LDT" / "Foo.lean",
                (
                    "namespace MIPStarRE.LDT\n\n"
                    "/-- Generic prose. -/\n"
                    "structure FooBridge where\n"
                    "  h : True\n"
                ),
            )
            _git(root, "add", ".")
            findings = find_metadata_findings(root, base="HEAD")
            self.assertEqual(len(findings), 1)
            self.assertEqual(findings[0].declaration.name, "FooBridge")

    def test_new_source_marked_bridge_passes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _commit_base(root)
            _write(
                root / "MIPStarRE" / "LDT" / "Foo.lean",
                (
                    "namespace MIPStarRE.LDT\n\n"
                    "/-- **Source:** This is the faithful encoding of "
                    "`\\label{lem:foo}`. -/\n"
                    "structure FooBridge where\n"
                    "  h : True\n"
                ),
            )
            _git(root, "add", ".")
            self.assertEqual(find_metadata_findings(root, base="HEAD"), [])

    def test_new_conditional_theorem_without_metadata_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _commit_base(root)
            _write(
                root / "MIPStarRE" / "LDT" / "Foo.lean",
                (
                    "namespace MIPStarRE.LDT\n\n"
                    "/-- Generic prose. -/\n"
                    "theorem main_ofObligations : True := by\n"
                    "  trivial\n"
                ),
            )
            _git(root, "add", ".")
            findings = find_metadata_findings(root, base="HEAD")
            self.assertEqual(len(findings), 1)
            self.assertEqual(findings[0].declaration.name, "main_ofObligations")

    def test_new_proof_obligation_theorem_with_metadata_passes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _commit_base(root)
            _write(
                root / "MIPStarRE" / "LDT" / "Foo.lean",
                (
                    "namespace MIPStarRE.LDT\n\n"
                    "/-- **Proof obligation:** Internal construction for "
                    "`\\label{lem:foo}`.  See issue #1579.  Elimination: "
                    "prove it from the paper hypotheses. -/\n"
                    "theorem main_ofObligations : True := by\n"
                    "  trivial\n"
                ),
            )
            _git(root, "add", ".")
            self.assertEqual(find_metadata_findings(root, base="HEAD"), [])

    def test_existing_bridge_is_not_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _write(
                root / "MIPStarRE" / "LDT" / "Foo.lean",
                (
                    "namespace MIPStarRE.LDT\n\n"
                    "/-- Generic prose. -/\n"
                    "structure FooBridge where\n"
                    "  h : True\n"
                ),
            )
            _git(root, "add", ".")
            _git(root, "commit", "-m", "base")

            path = root / "MIPStarRE" / "LDT" / "Foo.lean"
            path.write_text(path.read_text() + "\n-- Proof-only edit.\n", encoding="utf-8")
            self.assertEqual(find_metadata_findings(root, base="HEAD"), [])

    def test_staged_addition_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _commit_base(root)
            _write(
                root / "MIPStarRE" / "LDT" / "Foo.lean",
                (
                    "namespace MIPStarRE.LDT\n\n"
                    "/-- Generic prose. -/\n"
                    "def FooResidual : Prop := True\n"
                ),
            )
            _git(root, "add", ".")
            findings = find_metadata_findings(root, staged=True)
            self.assertEqual(len(findings), 1)
            self.assertEqual(findings[0].declaration.name, "FooResidual")

    def test_main_warn_only_returns_zero_on_finding(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _commit_base(root)
            _write(
                root / "MIPStarRE" / "LDT" / "Foo.lean",
                (
                    "namespace MIPStarRE.LDT\n\n"
                    "/-- Generic prose. -/\n"
                    "def FooPackage : Prop := True\n"
                ),
            )
            _git(root, "add", ".")
            with redirect_stdout(StringIO()), redirect_stderr(StringIO()):
                self.assertEqual(
                    main(["--root", str(root), "--base", "HEAD", "--warn-only"]),
                    0,
                )
                self.assertEqual(
                    main(["--root", str(root), "--base", "HEAD", "--ci"]),
                    1,
                )


if __name__ == "__main__":
    unittest.main()
