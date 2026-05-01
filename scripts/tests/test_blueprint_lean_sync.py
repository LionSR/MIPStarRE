#!/usr/bin/env python3
"""Regression tests for scripts/blueprint_lean_sync.py."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import blueprint_lean_sync  # noqa: E402
from blueprint_lean_sync import (  # noqa: E402
    BlueprintEntry,
    LeanDecl,
    SyncReport,
    _chapter_stats,
    _leanok_placement,
    _line_has_leanok_marker,
    _strip_tex_comment,
    _write_json_report,
    collect_blueprint_entries,
    collect_file_lean_decls,
    find_changed_decls_missing_from_blueprint,
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

    def test_strip_tex_comment_respects_escaped_percent_signs(self) -> None:
        self.assertEqual(
            _strip_tex_comment(r"active \% still active"),
            r"active \% still active",
        )
        self.assertEqual(_strip_tex_comment(r"active \\% comment \leanok"), r"active \\")
        self.assertEqual(_strip_tex_comment(r"active % comment \leanok"), "active ")

    def test_line_has_leanok_marker_rejects_prose_mentions(self) -> None:
        self.assertTrue(_line_has_leanok_marker(r"\leanok"))
        self.assertTrue(_line_has_leanok_marker(r"\begin{proof}\leanok"))
        self.assertTrue(_line_has_leanok_marker(r"\lean{Foo.bar}\leanok"))
        self.assertFalse(_line_has_leanok_marker(r"This result is not marked \leanok."))

    def test_comments_and_prose_do_not_create_leanok_markers(self) -> None:
        entries = self._collect_entries(
            r"""
\begin{lemma}\label{lem:comment-only}
  \lean{Foo.commentOnly}
  % Restore \leanok once the proof is complete.
\end{lemma}
\begin{proof}
  % Restore \leanok here too.
\end{proof}

\begin{lemma}\label{lem:prose-only}
  \lean{Foo.proseOnly}
  This result is not marked \leanok.
\end{lemma}

\begin{lemma}\label{lem:real-statement}
  \lean{Foo.realStatement}\leanok % active marker; comment follows.
\end{lemma}

\begin{lemma}\label{lem:real-proof}
  \lean{Foo.realProof}
  \leanok
\end{lemma}
\begin{proof}\leanok % active proof marker; comment follows.
  Proof.
\end{proof}
"""
        )

        by_decl = {entry.lean_decl: entry for entry in entries}
        self.assertFalse(by_decl["Foo.commentOnly"].has_leanok)
        self.assertFalse(by_decl["Foo.commentOnly"].proof_has_leanok)
        self.assertFalse(by_decl["Foo.proseOnly"].has_leanok)
        self.assertTrue(by_decl["Foo.realStatement"].has_leanok)
        self.assertFalse(by_decl["Foo.realStatement"].proof_has_leanok)
        self.assertTrue(by_decl["Foo.realProof"].has_leanok)
        self.assertTrue(by_decl["Foo.realProof"].proof_has_leanok)

    def test_orphan_detection_ignores_comment_and_prose_leanok_mentions(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            chapter_dir = root / "blueprint" / "src" / "chapter"
            chapter_dir.mkdir(parents=True)
            (chapter_dir / "ch01_comments.tex").write_text(
                textwrap.dedent(
                    r"""
                    % \leanok outside should be a comment, not an orphan.
                    This prose line mentions \leanok outside any statement.

                    \begin{lemma}
                    % \leanok before \lean{Foo.bar} should not be an orphan.
                    \lean{Foo.bar}
                    This result is not marked \leanok.
                    \end{lemma}
                    """
                ).strip()
                + "\n"
            )

            blueprint_src = root / "blueprint" / "src"
            self.assertEqual(find_orphan_leanok_tags(blueprint_src), [])

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


class CollectLeanDeclsTests(unittest.TestCase):
    def test_collect_file_lean_decls_ignores_comments_and_marks_private(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_root = root / "MIPStarRE"
            lean_root.mkdir()
            lean_file = lean_root / "Fake.lean"
            lean_file.write_text(
                textwrap.dedent(
                    """
                    namespace Foo

                    /-
                    lemma commentedOut : True := by
                      trivial
                    -/

                    -- def lineCommented : Nat := 0

                    def stringBlockCommentToken : String := "/-"
                    def afterStringBlockCommentToken : Nat := 1
                    def stringLineCommentToken : String := "--"
                    def interpolatedStringToken : String := s!"{"/-"}"
                    def afterInterpolatedStringToken : Nat := 2
                    def escapedNestedInterpolatedStringToken : String := s!"{\"/-\"}"
                    def afterEscapedNestedInterpolatedStringToken : Nat := 3
                    def messageInterpolatedStringToken : MessageData := m!"{"/-"}"
                    def afterMessageInterpolatedStringToken : Nat := 4
                    def nestedInterpolatedStringToken : String := s!"{s!"{1}"} /-"
                    def afterNestedInterpolatedStringToken : Nat := 5
                    def escapedInterpolationBraceToken : String := s!"{{/-}}"
                    def charLiterals : List Char := ['/', '-']
                    def primedName' : Nat := 0
                    def rawStringBlockCommentToken : String := r#""/-""#
                    def afterRawStringBlockCommentToken : Nat := 6
                    def rawStringMultiHashBlockCommentToken : String := r##""/-##"/-##"##
                    def afterRawStringMultiHashBlockCommentToken : Nat := 7
                    def plainRawStringBlockCommentToken : String := r" /- "
                    def afterPlainRawStringBlockCommentToken : Nat := 8
                    def plainRawStringBeforeHashToken : String := r" /- "#eval 9
                    def afterPlainRawStringBeforeHashToken : Nat := 9
                    def commentBoundaryBeforeHashQuote : String := r/- not raw -/#"ordinary" /- comment starts
                    def hiddenIfBoundaryIgnored : Nat := 999
                    -/
                    def afterCommentBoundaryBeforeHashQuote : Nat := 8

                    private lemma privateHelper : True := by
                      trivial

                    theorem publicTheorem : True := by
                      trivial

                    end Foo
                    """
                ).strip()
                + "\n"
            )

            decls = collect_file_lean_decls(lean_file, lean_root)
            by_name = {decl.fqn: decl for decl in decls}

            self.assertNotIn("Foo.commentedOut", by_name)
            self.assertNotIn("Foo.lineCommented", by_name)
            self.assertIn("Foo.stringBlockCommentToken", by_name)
            self.assertIn("Foo.afterStringBlockCommentToken", by_name)
            self.assertIn("Foo.stringLineCommentToken", by_name)
            self.assertIn("Foo.interpolatedStringToken", by_name)
            self.assertIn("Foo.afterInterpolatedStringToken", by_name)
            self.assertIn("Foo.escapedNestedInterpolatedStringToken", by_name)
            self.assertIn("Foo.afterEscapedNestedInterpolatedStringToken", by_name)
            self.assertIn("Foo.messageInterpolatedStringToken", by_name)
            self.assertIn("Foo.afterMessageInterpolatedStringToken", by_name)
            self.assertIn("Foo.nestedInterpolatedStringToken", by_name)
            self.assertIn("Foo.afterNestedInterpolatedStringToken", by_name)
            self.assertIn("Foo.escapedInterpolationBraceToken", by_name)
            self.assertIn("Foo.charLiterals", by_name)
            self.assertIn("Foo.primedName'", by_name)
            self.assertIn("Foo.rawStringBlockCommentToken", by_name)
            self.assertIn("Foo.afterRawStringBlockCommentToken", by_name)
            self.assertIn("Foo.rawStringMultiHashBlockCommentToken", by_name)
            self.assertIn("Foo.afterRawStringMultiHashBlockCommentToken", by_name)
            self.assertIn("Foo.plainRawStringBlockCommentToken", by_name)
            self.assertIn("Foo.afterPlainRawStringBlockCommentToken", by_name)
            self.assertIn("Foo.plainRawStringBeforeHashToken", by_name)
            self.assertIn("Foo.afterPlainRawStringBeforeHashToken", by_name)
            self.assertIn("Foo.commentBoundaryBeforeHashQuote", by_name)
            self.assertNotIn("Foo.hiddenIfBoundaryIgnored", by_name)
            self.assertIn("Foo.afterCommentBoundaryBeforeHashQuote", by_name)
            self.assertTrue(by_name["Foo.privateHelper"].is_private)
            self.assertFalse(by_name["Foo.publicTheorem"].is_private)

    def test_find_changed_decls_missing_from_blueprint_tracks_public_dotted_api(self) -> None:
        """Public dotted names are not internal merely because they contain a dot."""
        if shutil.which("git") is None:
            self.skipTest("git executable is required for diff-based reverse-blueprint checks")

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            lean_root = root / "MIPStarRE"
            lean_root.mkdir()
            blueprint_chapter = root / "blueprint" / "src" / "chapter"
            blueprint_chapter.mkdir(parents=True)
            (blueprint_chapter / "ch01_empty.tex").write_text("No Lean refs here.\n")

            lean_file = lean_root / "Fake.lean"
            lean_file.write_text("-- base file before public API additions\n")

            def git(*args: str) -> str:
                return subprocess.check_output(["git", *args], cwd=root, text=True).strip()

            git("init", "-q")
            git("config", "user.email", "tests@example.invalid")
            git("config", "user.name", "Blueprint Sync Tests")
            git("add", ".")
            git("commit", "-q", "-m", "base")
            base = git("rev-parse", "HEAD")

            lean_file.write_text(
                textwrap.dedent(
                    """
                    -- base file before public API additions

                    def Role.other : Nat := 1
                    theorem Parameters.next : True := by
                      trivial
                    def _root_.RootPublic : Nat := 3
                    """
                ).strip()
                + "\n"
            )
            git("add", ".")
            git("commit", "-q", "-m", "add dotted public API")

            missing = find_changed_decls_missing_from_blueprint(
                root,
                changed_files=["MIPStarRE/Fake.lean"],
                diff_base=base,
                diff_head="HEAD",
            )

            missing_names = [decl.fqn for decl in missing]
            self.assertEqual(
                missing_names,
                ["Role.other", "Parameters.next", "_root_.RootPublic"],
            )


class LeanokPlacementReportingTests(unittest.TestCase):
    """The JSON report and chapter stats must keep statement-level and
    proof-level \\leanok coverage separable."""

    def _fake_decl(self, name: str) -> LeanDecl:
        return LeanDecl(
            file="MIPStarRE/Fake.lean",
            line=1,
            fqn=name,
            kind="theorem",
            short_name=name.split(".")[-1],
            end_line=1,
        )

    def _entries_report(self) -> SyncReport:
        entries = [
            # Statement-level only (statement is matched, proof is not).
            BlueprintEntry(
                file="src/chapter/ch04.tex",
                line=10,
                env_type="lemma",
                label="lem:stmt-only",
                lean_decl="Foo.stmtOnly",
                has_leanok=True,
                proof_has_leanok=False,
            ),
            # Proof-level claim (fully formalized).
            BlueprintEntry(
                file="src/chapter/ch08.tex",
                line=20,
                env_type="theorem",
                label="thm:full",
                lean_decl="Foo.full",
                has_leanok=True,
                proof_has_leanok=True,
            ),
            # Neither marker.
            BlueprintEntry(
                file="src/chapter/ch04.tex",
                line=30,
                env_type="lemma",
                label="lem:bare",
                lean_decl="Foo.bare",
                has_leanok=False,
                proof_has_leanok=False,
            ),
        ]
        lean_decls = {
            entry.lean_decl: self._fake_decl(entry.lean_decl) for entry in entries
        }
        return SyncReport(blueprint_entries=entries, lean_decls=lean_decls)

    def test_chapter_stats_distinguishes_statement_and_proof_levels(self) -> None:
        stats = _chapter_stats(self._entries_report())

        ch04 = stats["src/chapter/ch04.tex"]
        self.assertEqual(ch04["total"], 2)
        self.assertEqual(ch04["statement_formalized"], 1)
        self.assertEqual(ch04["proof_formalized"], 0)
        self.assertEqual(ch04["proof_total"], 2)
        # Legacy alias must stay in lockstep with statement_formalized.
        self.assertEqual(ch04["formalized"], ch04["statement_formalized"])

        ch08 = stats["src/chapter/ch08.tex"]
        self.assertEqual(ch08["total"], 1)
        self.assertEqual(ch08["statement_formalized"], 1)
        self.assertEqual(ch08["proof_formalized"], 1)
        self.assertEqual(ch08["proof_total"], 1)

    def test_json_report_exposes_leanok_totals_and_per_entry_placement(self) -> None:
        report = self._entries_report()
        with tempfile.TemporaryDirectory() as td:
            out = Path(td) / "report.json"
            _write_json_report(report, out, Path(td))
            data = json.loads(out.read_text())

        self.assertEqual(
            data["leanok_totals"],
            {
                "statement_level": 2,
                "proof_level": 1,
                "statement_level_with_matching_lean_decl": 2,
                "proof_level_with_matching_lean_decl": 1,
            },
        )
        ch04 = data["chapter_stats"]["src/chapter/ch04.tex"]
        self.assertEqual(ch04["statement_formalized"], 1)
        self.assertEqual(ch04["proof_formalized"], 0)

    def test_leanok_placement_categorises_each_entry(self) -> None:
        report = self._entries_report()
        by_decl = {e.lean_decl: _leanok_placement(e) for e in report.blueprint_entries}
        self.assertEqual(
            by_decl,
            {
                "Foo.stmtOnly": "statement",
                "Foo.full": "both",
                "Foo.bare": "none",
            },
        )

    def test_leanok_placement_distinguishes_proof_only_from_both(self) -> None:
        # ``proof_only`` is the style-guide-violating case: \leanok is in the
        # proof block but not on the statement. It must not be conflated with
        # ``both`` (fully formalized) just because proof_has_leanok is true.
        proof_only_entry = BlueprintEntry(
            file="src/chapter/ch04.tex",
            line=10,
            env_type="lemma",
            label="lem:proof-only",
            lean_decl="Foo.proofOnly",
            has_leanok=False,
            proof_has_leanok=True,
        )
        self.assertEqual(_leanok_placement(proof_only_entry), "proof_only")

    def test_proof_only_entry_does_not_count_as_proof_formalized(self) -> None:
        proof_only_entry = BlueprintEntry(
            file="src/chapter/ch04.tex",
            line=10,
            env_type="lemma",
            label="lem:proof-only",
            lean_decl="Foo.proofOnly",
            has_leanok=False,
            proof_has_leanok=True,
        )
        report = SyncReport(
            blueprint_entries=[proof_only_entry],
            lean_decls={"Foo.proofOnly": self._fake_decl("Foo.proofOnly")},
        )
        stats = _chapter_stats(report)
        ch04 = stats["src/chapter/ch04.tex"]
        self.assertEqual(ch04["statement_formalized"], 0)
        self.assertEqual(ch04["proof_formalized"], 0)

    def test_definition_entries_do_not_deflate_proof_coverage(self) -> None:
        entries = [
            BlueprintEntry(
                file="src/chapter/ch04.tex",
                line=10,
                env_type="definition",
                label="def:only",
                lean_decl="Foo.definitionOnly",
                has_leanok=True,
                proof_has_leanok=False,
            ),
            BlueprintEntry(
                file="src/chapter/ch04.tex",
                line=20,
                env_type="lemma",
                label="lem:full",
                lean_decl="Foo.fullLemma",
                has_leanok=True,
                proof_has_leanok=True,
            ),
        ]
        report = SyncReport(
            blueprint_entries=entries,
            lean_decls={
                entry.lean_decl: self._fake_decl(entry.lean_decl) for entry in entries
            },
        )
        stats = _chapter_stats(report)
        ch04 = stats["src/chapter/ch04.tex"]
        self.assertEqual(ch04["total"], 2)
        self.assertEqual(ch04["statement_formalized"], 2)
        self.assertEqual(ch04["proof_total"], 1)
        self.assertEqual(ch04["proof_formalized"], 1)

    def test_split_entries_for_same_decl_count_as_proof_formalized(self) -> None:
        entries = [
            BlueprintEntry(
                file="src/chapter/ch04.tex",
                line=10,
                env_type="lemma",
                label="lem:split-statement",
                lean_decl="Foo.split",
                has_leanok=True,
                proof_has_leanok=False,
            ),
            BlueprintEntry(
                file="src/chapter/ch04.tex",
                line=20,
                env_type="remark",
                label=None,
                lean_decl="Foo.split",
                has_leanok=False,
                proof_has_leanok=True,
            ),
        ]
        report = SyncReport(
            blueprint_entries=entries,
            lean_decls={"Foo.split": self._fake_decl("Foo.split")},
        )
        stats = _chapter_stats(report)
        ch04 = stats["src/chapter/ch04.tex"]
        self.assertEqual(ch04["total"], 2)
        self.assertEqual(ch04["proof_total"], 1)
        self.assertEqual(ch04["statement_formalized"], 1)
        self.assertEqual(ch04["proof_formalized"], 1)

    def test_missing_in_lean_entry_records_leanok_placement(self) -> None:
        # Construct a report where the \leanok-tagged entry has no matching
        # Lean declaration, so it lands in missing_in_lean / leanok_but_missing.
        entries = [
            BlueprintEntry(
                file="src/chapter/ch04.tex",
                line=10,
                env_type="lemma",
                label="lem:stmt-only",
                lean_decl="Foo.stmtOnly",
                has_leanok=True,
                proof_has_leanok=False,
            )
        ]
        report = SyncReport(blueprint_entries=entries)
        report.missing_in_lean = list(entries)
        report.leanok_but_missing = list(entries)

        with tempfile.TemporaryDirectory() as td:
            out = Path(td) / "report.json"
            _write_json_report(report, out, Path(td))
            data = json.loads(out.read_text())

        self.assertEqual(data["missing_in_lean"][0]["leanok_placement"], "statement")
        self.assertTrue(data["missing_in_lean"][0]["statement_leanok"])
        self.assertFalse(data["missing_in_lean"][0]["proof_leanok"])
        self.assertEqual(data["leanok_but_missing"][0]["leanok_placement"], "statement")

    def test_missing_in_lean_preserves_has_leanok_statement_semantics(self) -> None:
        # ``has_leanok`` must keep its pre-placement-aware meaning
        # (statement-level only) so downstream consumers don't silently
        # flip. ``has_any_leanok`` is the new broader signal.
        proof_only_entry = BlueprintEntry(
            file="src/chapter/ch04.tex",
            line=10,
            env_type="lemma",
            label="lem:proof-only",
            lean_decl="Foo.proofOnly",
            has_leanok=False,
            proof_has_leanok=True,
        )
        report = SyncReport(blueprint_entries=[proof_only_entry])
        report.missing_in_lean = [proof_only_entry]

        with tempfile.TemporaryDirectory() as td:
            out = Path(td) / "report.json"
            _write_json_report(report, out, Path(td))
            data = json.loads(out.read_text())

        entry = data["missing_in_lean"][0]
        self.assertFalse(entry["has_leanok"])
        self.assertTrue(entry["has_any_leanok"])
        self.assertEqual(entry["leanok_placement"], "proof_only")


if __name__ == "__main__":
    unittest.main()
