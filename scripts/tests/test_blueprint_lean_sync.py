#!/usr/bin/env python3
"""Regression tests for scripts/blueprint_lean_sync.py."""

from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import blueprint_lean_sync  # noqa: E402
from blueprint_lean_sync import (  # noqa: E402
    collect_blueprint_entries,
    find_orphan_leanok_tags,
)


class BlueprintLeanSyncTests(unittest.TestCase):
    def test_orphan_leanok_detection_tracks_statement_and_proof_context(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            chapter_dir = root / "blueprint" / "src" / "chapter"
            chapter_dir.mkdir(parents=True)
            (chapter_dir / "ch01_test.tex").write_text(
                textwrap.dedent(
                    r"""
                    \begin{lemma}
                    \leanok
                    \lean{Foo.bar}
                    Statement.
                    \end{lemma}

                    \begin{lemma}
                    \lean{Foo.baz}
                    Statement.
                    \end{lemma}
                    \begin{proof}\leanok
                    Proof.
                    \end{proof}

                    \begin{lemma}
                    Statement only.
                    \end{lemma}
                    \begin{proof}\leanok
                    Missing preceding lean tag.
                    \end{proof}
                    """
                ).strip()
                + "\n"
            )

            blueprint_src = root / "blueprint" / "src"
            orphans = find_orphan_leanok_tags(blueprint_src)
            self.assertEqual(
                [(orphan.line, orphan.context) for orphan in orphans],
                [(2, "statement"), (18, "proof")],
            )

            entries = collect_blueprint_entries(blueprint_src)
            by_decl = {entry.lean_decl: entry for entry in entries}
            self.assertIn("Foo.bar", by_decl)
            self.assertIn("Foo.baz", by_decl)
            self.assertFalse(by_decl["Foo.bar"].proof_has_leanok)
            self.assertTrue(by_decl["Foo.baz"].proof_has_leanok)

    def test_orphan_leanok_ignores_intervening_non_lean_environment(self) -> None:
        """A \\begin{remark}\\end{remark} between a statement and its proof
        must not trigger a spurious orphan \\leanok warning on the proof."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            chapter_dir = root / "blueprint" / "src" / "chapter"
            chapter_dir.mkdir(parents=True)
            (chapter_dir / "ch01_intervening.tex").write_text(
                textwrap.dedent(
                    r"""
                    \begin{theorem}
                    \lean{Foo.bar}
                    Statement.
                    \end{theorem}

                    \begin{remark}
                    Intervening remark without \lean{} tag.
                    \end{remark}

                    \begin{proof}\leanok
                    Proof.
                    \end{proof}
                    """
                ).strip()
                + "\n"
            )

            blueprint_src = root / "blueprint" / "src"
            orphans = find_orphan_leanok_tags(blueprint_src)
            self.assertEqual(orphans, [])


class CollectBlueprintEntriesTests(unittest.TestCase):
    def _collect_entries(self, tex_source: str) -> list[blueprint_lean_sync.BlueprintEntry]:
        with tempfile.TemporaryDirectory() as tmp_dir:
            blueprint_src = Path(tmp_dir) / "blueprint" / "src"
            chapter_dir = blueprint_src / "chapter"
            chapter_dir.mkdir(parents=True)
            (chapter_dir / "ch04_projective.tex").write_text(tex_source.strip() + "\n")
            return blueprint_lean_sync.collect_blueprint_entries(blueprint_src)

    def test_nested_proof_credits_outer_proof_leanok(self) -> None:
        entries = self._collect_entries(
            r"""
\begin{lemma}[Orthogonalization lemma for measurements]\label{lem:orthonormalization-main-lemma}
  \lean{OuterDecl}
\end{lemma}

\begin{proof}[Proof of \ref{lem:orthonormalization-main-lemma}]
  \leanok

  \begin{lemma}\label{lem:trunc-inequality}
    \lean{InnerDecl}
    \leanok
  \end{lemma}
  \begin{proof}
    \leanok
  \end{proof}
\end{proof}
"""
        )

        self.assertEqual(len(entries), 2)
        by_label = {entry.label: entry for entry in entries}

        outer = by_label["lem:orthonormalization-main-lemma"]
        inner = by_label["lem:trunc-inequality"]

        self.assertFalse(outer.has_leanok)
        self.assertTrue(outer.proof_has_leanok)
        self.assertTrue(inner.has_leanok)
        self.assertTrue(inner.proof_has_leanok)

    def test_inner_leanok_does_not_formalize_outer_proof(self) -> None:
        entries = self._collect_entries(
            r"""
\begin{lemma}[Orthogonalization lemma for measurements]\label{lem:orthonormalization-main-lemma}
  \lean{OuterDecl}
\end{lemma}

\begin{proof}[Proof of \ref{lem:orthonormalization-main-lemma}]
  \begin{lemma}\label{lem:trunc-inequality}
    \lean{InnerDecl}
    \leanok
  \end{lemma}
  \begin{proof}
    \leanok
  \end{proof}
\end{proof}
"""
        )

        by_label = {entry.label: entry for entry in entries}

        outer = by_label["lem:orthonormalization-main-lemma"]
        inner = by_label["lem:trunc-inequality"]

        self.assertFalse(outer.has_leanok)
        self.assertFalse(outer.proof_has_leanok)
        self.assertTrue(inner.has_leanok)
        self.assertTrue(inner.proof_has_leanok)


if __name__ == "__main__":
    unittest.main()
