#!/usr/bin/env python3
"""Regression tests for scripts/audit_green_node_integrity.py."""

from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import audit_green_node_integrity as audit  # noqa: E402


class GreenNodeIntegrityAuditTests(unittest.TestCase):
    def test_endpoint_prose_does_not_close_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_file = root / "MIPStarRE" / "Foo.lean"
            lean_file.parent.mkdir(parents=True)
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace MIPStarRE.LDT

                    /--
                    end point
                    endpoint prose in a mathematical docstring is not a Lean `end`
                    command, and therefore must not change the namespace stack.
                    -/
                    theorem afterEndpointProse (h : P) : Q := by
                      sorry

                    end MIPStarRE.LDT
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            headers = audit.declaration_headers(root)

        self.assertIn("MIPStarRE.LDT.afterEndpointProse", headers)
        self.assertIsNone(audit.EVENT_RE.search("endpoint"))
        self.assertTrue(audit.EVENT_RE.search("end point"))

    def test_line_comments_do_not_close_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_file = root / "MIPStarRE" / "Foo.lean"
            lean_file.parent.mkdir(parents=True)
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace MIPStarRE.LDT

                    -- end point
                    theorem afterLineComment (h : P) : Q := by
                      sorry

                    end MIPStarRE.LDT
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            headers = audit.declaration_headers(root)

        self.assertIn("MIPStarRE.LDT.afterLineComment", headers)


if __name__ == "__main__":
    unittest.main()
