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

    def test_tex_comment_does_not_mark_node_green(self) -> None:
        block = textwrap.dedent(
            r"""
            \begin{theorem}\label{thm:commented}
              \lean{Foo.bar}
              % This source theorem is not marked \leanok.
            \end{theorem}
            """
        )

        masked = audit.mask_tex_comments(block)

        self.assertNotIn(r"\leanok", masked)
        self.assertIn(r"\lean{Foo.bar}", masked)

    def test_unfaithful_docstring_is_indexed(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_file = root / "MIPStarRE" / "Foo.lean"
            lean_file.parent.mkdir(parents=True)
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace MIPStarRE.LDT

                    /--
                    A source-shaped declaration.

                    **Unfaithful:** This proof still depends on a tracked
                    obligation.
                    -/
                    theorem sourceStatement (h : P) : Q := by
                      sorry

                    end MIPStarRE.LDT
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            docstrings = audit.declaration_docstrings(root)

        self.assertTrue(
            audit.has_unfaithful_marker("MIPStarRE.LDT.sourceStatement", docstrings)
        )

    def test_plain_block_comment_does_not_reuse_previous_docstring(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_file = root / "MIPStarRE" / "Foo.lean"
            lean_file.parent.mkdir(parents=True)
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace MIPStarRE.LDT

                    /--
                    **Unfaithful:** This marker belongs only to the first
                    declaration.
                    -/
                    theorem firstSourceStatement (h : P) : Q := by
                      sorry

                    /- A plain implementation note immediately before the next
                    declaration is not a docstring. -/
                    theorem secondStatement (h : P) : Q := by
                      sorry

                    end MIPStarRE.LDT
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            docstrings = audit.declaration_docstrings(root)

        self.assertTrue(
            audit.has_unfaithful_marker("MIPStarRE.LDT.firstSourceStatement", docstrings)
        )
        self.assertFalse(
            audit.has_unfaithful_marker("MIPStarRE.LDT.secondStatement", docstrings)
        )

    def test_nested_block_comment_inside_docstring_is_indexed(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_file = root / "MIPStarRE" / "Foo.lean"
            lean_file.parent.mkdir(parents=True)
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace MIPStarRE.LDT

                    /--
                    A source-shaped declaration whose docstring contains a
                    nested implementation aside: /- nested note -/.

                    **Unfaithful:** The marker still belongs to this declaration.
                    -/
                    theorem nestedDocstringStatement (h : P) : Q := by
                      sorry

                    end MIPStarRE.LDT
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            docstrings = audit.declaration_docstrings(root)

        self.assertTrue(
            audit.has_unfaithful_marker(
                "MIPStarRE.LDT.nestedDocstringStatement", docstrings
            )
        )


if __name__ == "__main__":
    unittest.main()
