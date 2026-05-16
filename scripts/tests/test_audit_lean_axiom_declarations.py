"""Regression tests for scripts/audit_lean_axiom_declarations.py."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from audit_lean_axiom_declarations import run_audit  # noqa: E402


def write_lean(root: Path, text: str) -> None:
    """Create a minimal LDT Lean file for an audit fixture."""
    path = root / "MIPStarRE" / "LDT" / "Fixture.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


class LeanAxiomDeclarationAuditTests(unittest.TestCase):
    def test_accepts_ordinary_sorry(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(root, "theorem gap : True := by\n  sorry\n")

            result = run_audit(root)

        self.assertEqual(result.scanned_files, 1)
        self.assertEqual(result.findings, ())

    def test_flags_axiom_command(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(root, "axiom hiddenBridge : True\n")

            result = run_audit(root)

        self.assertEqual(len(result.findings), 1)
        self.assertEqual(result.findings[0].command, "axiom")
        self.assertEqual(result.findings[0].name, "hiddenBridge")

    def test_flags_primed_axiom_name(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(root, "axiom hiddenBridge' : True\n")

            result = run_audit(root)

        self.assertEqual(len(result.findings), 1)
        self.assertEqual(result.findings[0].command, "axiom")
        self.assertEqual(result.findings[0].name, "hiddenBridge'")

    def test_flags_unicode_axiom_name(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(root, "axiom φBridge : True\n")

            result = run_audit(root)

        self.assertEqual(len(result.findings), 1)
        self.assertEqual(result.findings[0].command, "axiom")
        self.assertEqual(result.findings[0].name, "φBridge")

    def test_flags_constant_command(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(root, "constant externalBridge : True\n")

            result = run_audit(root)

        self.assertEqual(len(result.findings), 1)
        self.assertEqual(result.findings[0].command, "constant")
        self.assertEqual(result.findings[0].name, "externalBridge")

    def test_ignores_docstring_prose_and_line_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(
                root,
                """/-- This sentence mentions axiom fake : True. -/
-- constant alsoFake : True
theorem ok : True := by trivial
""",
            )

            result = run_audit(root)

        self.assertEqual(result.findings, ())

    def test_ignores_nested_block_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(
                root,
                """/- Outer comment
  /- nested axiom fake : True -/
  constant alsoFake : True
-/
theorem ok : True := by trivial
""",
            )

            result = run_audit(root)

        self.assertEqual(result.findings, ())

    def test_ignores_multiline_raw_string_content(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(
                root,
                """def exampleText := r#"
axiom fake : True
constant alsoFake : True
"#
theorem ok : True := by trivial
""",
            )

            result = run_audit(root)

        self.assertEqual(result.findings, ())

    def test_ignores_interpolated_string_content(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(
                root,
                """def exampleText := s!"
axiom fake : True
"
theorem ok : True := by trivial
""",
            )

            result = run_audit(root)

        self.assertEqual(result.findings, ())


if __name__ == "__main__":
    unittest.main()
