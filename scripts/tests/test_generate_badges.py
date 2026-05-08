#!/usr/bin/env python3
"""Regression tests for scripts/generate_badges.py."""

from __future__ import annotations

import dataclasses
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from generate_badges import (  # noqa: E402
    AXIOM_RE,
    SORRY_RE,
    _blueprint_badge_counts,
    count_pattern,
)

# Canonical proof-bearing environment types (must match
# blueprint_lean_sync._PROOF_BEARING_ENV_TYPES).
_TST_PROOF_BEARING_ENV_TYPES = frozenset(
    {"theorem", "lemma", "proposition", "corollary"}
)


# ---------------------------------------------------------------------------
# Minimal BlueprintEntry-alike for testing _blueprint_badge_counts
# ---------------------------------------------------------------------------


@dataclasses.dataclass
class _FakeBlueprintEntry:
    lean_decl: str
    has_leanok: bool = False
    proof_has_leanok: bool = False
    env_type: str = "lemma"


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


class GenerateBadgesTests(unittest.TestCase):
    def _count(self, source: str, pattern) -> int:
        with tempfile.TemporaryDirectory() as tmp_dir:
            path = Path(tmp_dir) / "Test.lean"
            path.write_text(textwrap.dedent(source).strip() + "\n", encoding="utf-8")
            return count_pattern([path], pattern)

    def test_sorry_count_ignores_comments_and_strings(self) -> None:
        count = self._count(
            r'''
            def visibleOne : True := by
              sorry

            -- sorry in a line comment
            /-
            sorry in a block comment
            /- sorry in a nested block comment -/
            -/
            def quoted : String := "sorry in a string"

            def visibleTwo : True := by
              exact sorry
            ''',
            SORRY_RE,
        )

        self.assertEqual(count, 2)

    def test_axiom_count_accepts_lean_modifiers_and_attributes(self) -> None:
        count = self._count(
            r'''
            axiom plainAxiom : Prop
            private axiom privateAxiom : Prop
            @[simp] protected axiom attributedAxiom : Prop
            @[simp]
            noncomputable unsafe axiom multilineAttributedAxiom : Prop

            -- axiom commentedAxiom : Prop
            def quoted : String := "private axiom stringAxiom : Prop"
            ''',
            AXIOM_RE,
        )

        self.assertEqual(count, 4)


class BlueprintBadgeCountsTests(unittest.TestCase):
    """Unit tests for :func:`_blueprint_badge_counts`."""

    def test_all_no_leanok(self) -> None:
        entries = [
            _FakeBlueprintEntry("A"),
            _FakeBlueprintEntry("B"),
        ]
        no_leanok, not_ready = _blueprint_badge_counts(entries, _TST_PROOF_BEARING_ENV_TYPES)
        self.assertEqual(no_leanok, 2)
        self.assertEqual(not_ready, 2)

    def test_all_fully_formalized(self) -> None:
        entries = [
            _FakeBlueprintEntry("A", has_leanok=True, proof_has_leanok=True),
            _FakeBlueprintEntry("B", has_leanok=True, proof_has_leanok=True),
        ]
        no_leanok, not_ready = _blueprint_badge_counts(entries, _TST_PROOF_BEARING_ENV_TYPES)
        self.assertEqual(no_leanok, 0)
        self.assertEqual(not_ready, 0)

    def test_statement_only_is_not_ready_but_not_no_leanok(self) -> None:
        """statement-level \\leanok alone: not 'no leanok', but still 'not ready'."""
        entries = [
            _FakeBlueprintEntry("A", has_leanok=True, proof_has_leanok=False),
        ]
        no_leanok, not_ready = _blueprint_badge_counts(entries, _TST_PROOF_BEARING_ENV_TYPES)
        self.assertEqual(no_leanok, 0)  # has statement-level
        self.assertEqual(not_ready, 1)  # proof missing

    def test_definition_only_with_statement_is_ready(self) -> None:
        entries = [
            _FakeBlueprintEntry("A", has_leanok=True, env_type="definition"),
        ]
        no_leanok, not_ready = _blueprint_badge_counts(entries, _TST_PROOF_BEARING_ENV_TYPES)
        self.assertEqual(no_leanok, 0)
        self.assertEqual(not_ready, 0)

    def test_definition_only_without_statement_is_not_ready(self) -> None:
        entries = [
            _FakeBlueprintEntry("A", has_leanok=False, env_type="definition"),
        ]
        no_leanok, not_ready = _blueprint_badge_counts(entries, _TST_PROOF_BEARING_ENV_TYPES)
        self.assertEqual(no_leanok, 1)
        self.assertEqual(not_ready, 1)

    def test_remark_only_is_excluded_from_not_ready(self) -> None:
        entries = [
            _FakeBlueprintEntry("A", has_leanok=False, env_type="remark"),
        ]
        no_leanok, not_ready = _blueprint_badge_counts(entries, _TST_PROOF_BEARING_ENV_TYPES)
        self.assertEqual(no_leanok, 1)
        self.assertEqual(not_ready, 0)  # remark-only: excluded denominator

    def test_mixed_remark_and_lemma_treated_as_proof_bearing(self) -> None:
        """When a decl appears in both remark and lemma, treat as proof-bearing."""
        entries = [
            _FakeBlueprintEntry("A", has_leanok=True, env_type="remark"),
            _FakeBlueprintEntry("A", has_leanok=True, proof_has_leanok=False, env_type="lemma"),
        ]
        no_leanok, not_ready = _blueprint_badge_counts(entries, _TST_PROOF_BEARING_ENV_TYPES)
        self.assertEqual(no_leanok, 0)  # has statement
        self.assertEqual(not_ready, 1)  # proof-bearing, missing proof

    def test_split_entries_across_files_for_same_decl(self) -> None:
        """Multiple entries for the same decl are aggregated correctly."""
        entries = [
            _FakeBlueprintEntry("A", has_leanok=True, proof_has_leanok=False, env_type="lemma"),
            _FakeBlueprintEntry("A", has_leanok=False, proof_has_leanok=True, env_type="remark"),
        ]
        no_leanok, not_ready = _blueprint_badge_counts(entries, _TST_PROOF_BEARING_ENV_TYPES)
        # Has both markers, even though spread across entries.
        self.assertEqual(no_leanok, 0)
        self.assertEqual(not_ready, 0)

    def test_mixed_type_with_no_markers(self) -> None:
        entries = [
            _FakeBlueprintEntry("A", has_leanok=False, env_type="lemma"),
            _FakeBlueprintEntry("B", has_leanok=False, env_type="definition"),
            _FakeBlueprintEntry("C", has_leanok=False, env_type="remark"),
        ]
        no_leanok, not_ready = _blueprint_badge_counts(entries, _TST_PROOF_BEARING_ENV_TYPES)
        self.assertEqual(no_leanok, 3)
        # A: lemma missing both → not ready (1)
        # B: def missing stmt → not ready (1)
        # C: remark-only → excluded (0)
        self.assertEqual(not_ready, 2)

    def test_proof_only_decl_has_leanok_but_is_not_ready(self) -> None:
        """proof_only (style violation): has proof \\leanok but no stmt \\leanok.

        The ``no_leanok`` count is about the **presence** of any \\leanok
        marker; a proof_only declaration does have one (albeit the wrong
        placement), so it is NOT counted as ``no_leanok``.  However, it
        is ``not_ready`` because proof-bearing declarations require both
        markers.
        """
        entries = [
            _FakeBlueprintEntry("A", has_leanok=False, proof_has_leanok=True),
        ]
        no_leanok, not_ready = _blueprint_badge_counts(entries, _TST_PROOF_BEARING_ENV_TYPES)
        # Has proof-level leanok, so NOT "no leanok".
        self.assertEqual(no_leanok, 0)
        # Proof-bearing, missing statement → not ready
        self.assertEqual(not_ready, 1)


class BlueprintBadgeCLITests(unittest.TestCase):
    """CLI-level tests for ``--blueprint-src`` argument validation."""

    def test_invalid_blueprint_src_prints_error_and_exits_nonzero(self) -> None:
        """Passing a nonexistent --blueprint-src must fail with a clear error."""
        import subprocess

        result = subprocess.run(
            [
                sys.executable,
                str(SCRIPT_DIR / "generate_badges.py"),
                "--blueprint-src",
                "/nonexistent/path",
                "--output-dir",
                "/tmp",
            ],
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("--blueprint-src", result.stderr)
        self.assertIn("does not exist", result.stderr)

    def test_blueprint_src_without_chapter_subdir_fails(self) -> None:
        """A path without a chapter/ subdirectory must also fail."""
        import subprocess

        with tempfile.TemporaryDirectory() as tmp_dir:
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT_DIR / "generate_badges.py"),
                    "--blueprint-src",
                    tmp_dir,
                    "--output-dir",
                    "/tmp",
                ],
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("chapter/", result.stderr)

    def test_valid_blueprint_src_succeeds(self) -> None:
        """A path with a chapter/ subdirectory must succeed."""
        import subprocess

        with tempfile.TemporaryDirectory() as tmp_dir:
            (Path(tmp_dir) / "chapter").mkdir()
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT_DIR / "generate_badges.py"),
                    "--blueprint-src",
                    tmp_dir,
                    "--output-dir",
                    "/tmp",
                ],
                capture_output=True,
                text=True,
            )
            self.assertEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
