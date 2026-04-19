from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from blueprint_lean_sync import collect_blueprint_entries, find_orphan_leanok_tags


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


if __name__ == "__main__":
    unittest.main()
