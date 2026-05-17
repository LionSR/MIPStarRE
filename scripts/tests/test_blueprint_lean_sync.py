#!/usr/bin/env python3
"""Regression tests for scripts/blueprint_lean_sync.py."""

from __future__ import annotations

import contextlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest import mock
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import blueprint_lean_sync  # noqa: E402
from blueprint_lean_sync import (  # noqa: E402
    BlueprintEntry,
    HeaderLeanokWithoutProofLeanok,
    LeanDecl,
    SyncReport,
    _BLUEPRINT_COVERAGE_COMMENT_MARKER,
    _append_missing_blueprint_step_summary,
    _chapter_stats,
    _create_pr_comment,
    _delete_pr_comment,
    _find_bot_pr_comment,
    _github_api_request,
    _github_api_request_paginated,
    _leanok_placement,
    _line_has_leanok_marker,
    _missing_blueprint_summary_command,
    _parse_pr_number_from_env,
    _pr_comment_body,
    _strip_tex_comment,
    _try_post_pr_comment,
    _update_pr_comment,
    _write_json_report,
    collect_blueprint_entries,
    collect_file_lean_decls,
    find_changed_decls_missing_from_blueprint,
    find_header_leanok_without_proof_leanok,
    find_orphan_leanok_tags,
    print_missing_blueprint_warnings,
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
                    def escapedNestedInterpolatedStringToken : String := s!"{\\\"/-\\\"}"
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


class MissingBlueprintStepSummaryTests(unittest.TestCase):
    def _decl(self, name: str) -> LeanDecl:
        return LeanDecl(
            file="MIPStarRE/Fake.lean",
            line=17,
            fqn=name,
            kind="theorem",
            short_name=name.split(".")[-1],
            end_line=20,
        )

    def test_step_summary_lists_missing_declarations_and_command(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            summary_path = Path(td) / "step-summary.md"
            old_summary = os.environ.get("GITHUB_STEP_SUMMARY")
            os.environ["GITHUB_STEP_SUMMARY"] = str(summary_path)
            try:
                _append_missing_blueprint_step_summary(
                    [self._decl("Foo.paperFacing")],
                    command=(
                        "python3 scripts/blueprint_lean_sync.py --root . "
                        "--warn-missing-blueprint --diff-base origin/main "
                        "--changed-files MIPStarRE/Fake.lean"
                    ),
                )
            finally:
                if old_summary is None:
                    os.environ.pop("GITHUB_STEP_SUMMARY", None)
                else:
                    os.environ["GITHUB_STEP_SUMMARY"] = old_summary

            summary = summary_path.read_text()
            self.assertIn("## Blueprint reverse-coverage warnings", summary)
            self.assertIn("`Foo.paperFacing`", summary)
            self.assertIn("`MIPStarRE/Fake.lean:17`", summary)
            self.assertIn(r"`\lean{Foo.paperFacing}`", summary)
            self.assertIn("--warn-missing-blueprint", summary)

    def test_step_summary_is_not_created_without_missing_declarations(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            summary_path = Path(td) / "step-summary.md"
            old_summary = os.environ.get("GITHUB_STEP_SUMMARY")
            os.environ["GITHUB_STEP_SUMMARY"] = str(summary_path)
            try:
                _append_missing_blueprint_step_summary([])
            finally:
                if old_summary is None:
                    os.environ.pop("GITHUB_STEP_SUMMARY", None)
                else:
                    os.environ["GITHUB_STEP_SUMMARY"] = old_summary

            self.assertFalse(summary_path.exists())

    def test_summary_command_includes_nondefault_diff_head(self) -> None:
        command = _missing_blueprint_summary_command(
            diff_base="origin/main",
            diff_head="feature/head",
            changed_files=["MIPStarRE/Fake.lean"],
        )

        self.assertIn("--diff-head feature/head", command)

    def test_summary_command_omits_default_diff_head(self) -> None:
        command = _missing_blueprint_summary_command(
            diff_base="origin/main",
            diff_head="HEAD",
            changed_files=["MIPStarRE/Fake.lean"],
        )

        self.assertNotIn("--diff-head", command)

    def test_fail_on_missing_prints_error(self) -> None:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            print_missing_blueprint_warnings(
                [self._decl("Foo.paperFacing")],
                fail_on_missing=True,
            )

        self.assertIn("WARNING: Changed declarations not yet in blueprint", stdout.getvalue())
        self.assertIn(
            r"ERROR: changed Lean declarations are missing corresponding \lean{} tags",
            stderr.getvalue(),
        )

    def test_fail_on_missing_requires_warn_mode(self) -> None:
        result = subprocess.run(
            [
                sys.executable,
                str(SCRIPT_DIR / "blueprint_lean_sync.py"),
                "--fail-on-missing-blueprint",
            ],
            check=False,
            capture_output=True,
            text=True,
        )

        self.assertEqual(result.returncode, 2)
        self.assertIn(
            "--fail-on-missing-blueprint requires --warn-missing-blueprint",
            result.stderr,
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


class PRCommentTests(unittest.TestCase):
    """Tests for --post-pr-comment: comment body rendering, marker, idempotent
    selection, and graceful error handling."""

    def _decl(self, name: str) -> LeanDecl:
        return LeanDecl(
            file="MIPStarRE/Fake.lean",
            line=17,
            fqn=name,
            kind="theorem",
            short_name=name.split(".")[-1],
            end_line=20,
        )

    # ── comment body rendering ────────────────────────────────────────────

    def test_comment_body_includes_marker(self) -> None:
        body = _pr_comment_body([self._decl("Foo.bar")])
        self.assertIn(_BLUEPRINT_COVERAGE_COMMENT_MARKER, body)

    def test_comment_body_with_warnings_contains_decl_and_location(self) -> None:
        body = _pr_comment_body([self._decl("Foo.bar")])
        self.assertIn("`Foo.bar`", body)
        self.assertIn("`MIPStarRE/Fake.lean:17`", body)
        self.assertIn(r"`\lean{Foo.bar}`", body)
        self.assertIn("## Blueprint reverse-coverage warnings", body)

    def test_comment_body_no_warnings_is_resolved_note(self) -> None:
        body = _pr_comment_body([])
        self.assertIn(_BLUEPRINT_COVERAGE_COMMENT_MARKER, body)
        self.assertIn("✓ No changed declarations", body)
        self.assertNotIn("## Blueprint reverse-coverage warnings", body)

    def test_comment_body_includes_command_when_given(self) -> None:
        body = _pr_comment_body(
            [self._decl("Foo.bar")],
            command="python3 scripts/blueprint_lean_sync.py --root . --warn-missing-blueprint",
        )
        self.assertIn("--warn-missing-blueprint", body)
        self.assertIn("```bash", body)

    # ── marker constant ───────────────────────────────────────────────────

    def test_marker_is_html_comment(self) -> None:
        self.assertTrue(_BLUEPRINT_COVERAGE_COMMENT_MARKER.startswith("<!--"))
        self.assertTrue(_BLUEPRINT_COVERAGE_COMMENT_MARKER.endswith("-->"))

    # ── PR number parsing from environment ────────────────────────────────

    def test_parse_pr_number_from_refs_pull_merge(self) -> None:
        with mock.patch.dict(os.environ, {"GITHUB_REF": "refs/pull/42/merge"}):
            self.assertEqual(_parse_pr_number_from_env(), 42)

    def test_parse_pr_number_from_refs_pull_head(self) -> None:
        with mock.patch.dict(os.environ, {"GITHUB_REF": "refs/pull/99/head"}):
            self.assertEqual(_parse_pr_number_from_env(), 99)

    def test_parse_pr_number_from_refs_pull_no_suffix(self) -> None:
        with mock.patch.dict(os.environ, {"GITHUB_REF": "refs/pull/7"}):
            self.assertEqual(_parse_pr_number_from_env(), 7)

    def test_parse_pr_number_returns_none_for_non_pr_ref(self) -> None:
        with mock.patch.dict(os.environ, {"GITHUB_REF": "refs/heads/main"}):
            self.assertIsNone(_parse_pr_number_from_env())

    def test_parse_pr_number_returns_none_when_not_set(self) -> None:
        with mock.patch.dict(os.environ, {}, clear=True):
            # GITHUB_REF may be set in the test runner environment; clear it
            with mock.patch.dict(os.environ, {"GITHUB_REF": ""}, clear=False):
                self.assertIsNone(_parse_pr_number_from_env())

    # ── find_bot_pr_comment idempotent selection ──────────────────────────

    def _make_comment(self, cid: int, body: str, *, user: str = "github-actions[bot]") -> dict:
        return {"id": cid, "body": body, "user": {"login": user}}

    def _mock_api_response(self, status: int = 200, body: object = None) -> mock.MagicMock:
        """Build a mock ``urlopen`` context manager that returns the given status/body."""
        if body is None:
            content = b"[]"
        elif isinstance(body, (dict, list)):
            content = json.dumps(body).encode("utf-8")
        else:
            content = str(body).encode("utf-8")
        cm = mock.MagicMock()
        cm.__enter__.return_value.status = status
        cm.__enter__.return_value.read.return_value = content
        return cm

    def test_find_bot_comment_returns_id_when_marker_present(self) -> None:
        comments = [
            self._make_comment(1, "regular comment"),
            self._make_comment(2, f"Bot report {_BLUEPRINT_COVERAGE_COMMENT_MARKER}"),
            self._make_comment(3, "another comment"),
        ]
        with mock.patch(
            "blueprint_lean_sync._github_api_request_paginated", return_value=comments
        ):
            cid = _find_bot_pr_comment("o", "r", 1, "tok")
        self.assertEqual(cid, 2)

    def test_find_bot_comment_returns_none_when_marker_absent(self) -> None:
        comments = [
            self._make_comment(1, "regular comment"),
            self._make_comment(2, "another regular"),
        ]
        with mock.patch(
            "blueprint_lean_sync._github_api_request_paginated", return_value=comments
        ):
            cid = _find_bot_pr_comment("o", "r", 1, "tok")
        self.assertIsNone(cid)

    def test_find_bot_comment_returns_none_when_no_comments(self) -> None:
        with mock.patch(
            "blueprint_lean_sync._github_api_request_paginated", return_value=[]
        ):
            cid = _find_bot_pr_comment("o", "r", 1, "tok")
        self.assertIsNone(cid)

    def test_find_bot_comment_rejects_non_bot_author(self) -> None:
        """A comment with the marker but authored by a regular user is ignored."""
        comments = [
            self._make_comment(
                1, f"User comment {_BLUEPRINT_COVERAGE_COMMENT_MARKER}",
                user="some-user",
            ),
        ]
        with mock.patch(
            "blueprint_lean_sync._github_api_request_paginated", return_value=comments
        ):
            cid = _find_bot_pr_comment("o", "r", 1, "tok")
        self.assertIsNone(cid)

    def test_find_bot_comment_paginates_across_pages(self) -> None:
        """When first page is full (100 items) but no marker, it queries page 2."""
        page1 = [self._make_comment(i, f"comment {i}") for i in range(100)]
        page2 = [
            self._make_comment(200, f"Bot {_BLUEPRINT_COVERAGE_COMMENT_MARKER}"),
        ]
        with mock.patch(
            "blueprint_lean_sync._github_api_request_paginated",
            return_value=page1 + page2,
        ):
            cid = _find_bot_pr_comment("o", "r", 1, "tok")
        self.assertEqual(cid, 200)

    # ── _try_post_pr_comment orchestration ────────────────────────────────

    def test_try_post_pr_comment_creates_new_comment_when_none_exists(self) -> None:
        with mock.patch(
            "blueprint_lean_sync._find_bot_pr_comment", return_value=None
        ) as mock_find, mock.patch(
            "blueprint_lean_sync._create_pr_comment", return_value=42
        ) as mock_create, mock.patch(
            "blueprint_lean_sync._update_pr_comment"
        ) as mock_update, mock.patch(
            "blueprint_lean_sync._delete_pr_comment"
        ) as mock_delete:
            _try_post_pr_comment(
                [self._decl("Foo.bar")],
                pr_number=1,
                owner="o",
                repo="r",
                token="tok",
            )
        mock_find.assert_called_once()
        mock_create.assert_called_once()
        mock_update.assert_not_called()
        mock_delete.assert_not_called()

    def test_try_post_pr_comment_updates_existing_comment_when_present(self) -> None:
        with mock.patch(
            "blueprint_lean_sync._find_bot_pr_comment", return_value=99
        ) as mock_find, mock.patch(
            "blueprint_lean_sync._create_pr_comment"
        ) as mock_create, mock.patch(
            "blueprint_lean_sync._update_pr_comment"
        ) as mock_update, mock.patch(
            "blueprint_lean_sync._delete_pr_comment"
        ) as mock_delete:
            _try_post_pr_comment(
                [self._decl("Foo.bar")],
                pr_number=1,
                owner="o",
                repo="r",
                token="tok",
            )
        mock_find.assert_called_once()
        mock_update.assert_called_once_with("o", "r", 99, mock.ANY, "tok")
        mock_create.assert_not_called()
        mock_delete.assert_not_called()

    def test_try_post_pr_comment_deletes_existing_comment_when_no_warnings(self) -> None:
        with mock.patch(
            "blueprint_lean_sync._find_bot_pr_comment", return_value=99
        ) as mock_find, mock.patch(
            "blueprint_lean_sync._create_pr_comment"
        ) as mock_create, mock.patch(
            "blueprint_lean_sync._update_pr_comment"
        ) as mock_update, mock.patch(
            "blueprint_lean_sync._delete_pr_comment"
        ) as mock_delete:
            _try_post_pr_comment(
                [],
                pr_number=1,
                owner="o",
                repo="r",
                token="tok",
            )
        mock_find.assert_called_once()
        mock_delete.assert_called_once_with("o", "r", 99, "tok")
        mock_create.assert_not_called()
        mock_update.assert_not_called()

    def test_try_post_pr_comment_does_nothing_when_no_warnings_and_no_comment(self) -> None:
        with mock.patch(
            "blueprint_lean_sync._find_bot_pr_comment", return_value=None
        ) as mock_find, mock.patch(
            "blueprint_lean_sync._create_pr_comment"
        ) as mock_create, mock.patch(
            "blueprint_lean_sync._update_pr_comment"
        ) as mock_update, mock.patch(
            "blueprint_lean_sync._delete_pr_comment"
        ) as mock_delete:
            _try_post_pr_comment(
                [],
                pr_number=1,
                owner="o",
                repo="r",
                token="tok",
            )
        mock_find.assert_called_once()
        mock_create.assert_not_called()
        mock_update.assert_not_called()
        mock_delete.assert_not_called()

    # ── graceful error handling ───────────────────────────────────────────

    def test_try_post_skips_when_token_missing(self) -> None:
        with mock.patch(
            "blueprint_lean_sync._find_bot_pr_comment"
        ) as mock_find, mock.patch(
            "blueprint_lean_sync._create_pr_comment"
        ) as mock_create:
            _try_post_pr_comment(
                [self._decl("Foo.bar")],
                pr_number=1,
                owner="o",
                repo="r",
                token=None,
            )
        mock_find.assert_not_called()
        mock_create.assert_not_called()

    def test_try_post_skips_when_owner_missing(self) -> None:
        with mock.patch(
            "blueprint_lean_sync._find_bot_pr_comment"
        ) as mock_find, mock.patch(
            "blueprint_lean_sync._create_pr_comment"
        ) as mock_create:
            _try_post_pr_comment(
                [self._decl("Foo.bar")],
                pr_number=1,
                owner=None,
                repo="r",
                token="tok",
            )
        mock_find.assert_not_called()
        mock_create.assert_not_called()

    def test_try_post_skips_when_pr_number_missing(self) -> None:
        with mock.patch(
            "blueprint_lean_sync._find_bot_pr_comment"
        ) as mock_find, mock.patch(
            "blueprint_lean_sync._create_pr_comment"
        ) as mock_create:
            _try_post_pr_comment(
                [self._decl("Foo.bar")],
                pr_number=None,
                owner="o",
                repo="r",
                token="tok",
            )
        mock_find.assert_not_called()
        mock_create.assert_not_called()

    def test_try_post_continues_when_api_fails(self) -> None:
        """If the API call raises, the function must not propagate the exception."""
        with mock.patch(
            "blueprint_lean_sync._find_bot_pr_comment",
            side_effect=RuntimeError("network error"),
        ):
            # Must not raise
            _try_post_pr_comment(
                [self._decl("Foo.bar")],
                pr_number=1,
                owner="o",
                repo="r",
                token="tok",
            )

    # ── GitHub API request helper ─────────────────────────────────────────

    def test_github_api_request_get_parses_json_list(self) -> None:
        with mock.patch("urllib.request.urlopen") as mock_urlopen:
            mock_urlopen.return_value = self._mock_api_response(
                200, [{"id": 1}, {"id": 2}]
            )
            result = _github_api_request("GET", "https://api.github.com/test", "tok")
        self.assertEqual(result, [{"id": 1}, {"id": 2}])

    def test_github_api_request_delete_returns_none_on_204(self) -> None:
        cm = mock.MagicMock()
        cm.__enter__.return_value.status = 204
        cm.__enter__.return_value.read.return_value = b""
        with mock.patch("urllib.request.urlopen", return_value=cm):
            result = _github_api_request(
                "DELETE", "https://api.github.com/test", "tok"
            )
        self.assertIsNone(result)

    def test_github_api_request_raises_on_http_error(self) -> None:
        import urllib.error

        with mock.patch("urllib.request.urlopen") as mock_urlopen:
            fp = mock.MagicMock()
            fp.read.return_value = b'{"message": "Not Found"}'
            mock_urlopen.side_effect = urllib.error.HTTPError(
                "https://api.github.com/test", 404, "Not Found", {}, fp
            )
            with self.assertRaises(RuntimeError) as ctx:
                _github_api_request("GET", "https://api.github.com/test", "tok")
            self.assertIn("404", str(ctx.exception))

    # ── paginated request helper ──────────────────────────────────────────

    def test_paginated_returns_concatenated_pages(self) -> None:
        """Multiple pages are concatenated."""
        with mock.patch(
            "blueprint_lean_sync._github_api_request"
        ) as mock_req:
            mock_req.side_effect = [
                [{"id": i} for i in range(100)],   # page 1 (full)
                [{"id": i} for i in range(100, 150)],  # page 2 (partial)
            ]
            result = _github_api_request_paginated(
                "https://api.github.com/repos/o/r/issues/1/comments", "tok"
            )
        self.assertEqual(len(result), 150)

    def test_paginated_stops_on_empty_page(self) -> None:
        with mock.patch(
            "blueprint_lean_sync._github_api_request"
        ) as mock_req:
            mock_req.side_effect = [[{"id": 1}], []]
            result = _github_api_request_paginated(
                "https://api.github.com/repos/o/r/issues/1/comments", "tok"
            )
        self.assertEqual(len(result), 1)

    def test_paginated_stops_on_dict_response(self) -> None:
        """A dict response (GitHub error object) stops pagination cleanly."""
        with mock.patch(
            "blueprint_lean_sync._github_api_request"
        ) as mock_req:
            # First request succeeds; second returns an error dict.
            mock_req.side_effect = [
                [{"id": 1}],
                {"message": "Bad credentials", "documentation_url": "..."},
            ]
            result = _github_api_request_paginated(
                "https://api.github.com/repos/o/r/issues/1/comments", "tok"
            )
        # Should return only the items from the first (successful) page.
        self.assertEqual(result, [{"id": 1}])

    def test_paginated_stops_on_none_response(self) -> None:
        with mock.patch(
            "blueprint_lean_sync._github_api_request"
        ) as mock_req:
            mock_req.side_effect = [[{"id": 1}], None]
            result = _github_api_request_paginated(
                "https://api.github.com/repos/o/r/issues/1/comments", "tok"
            )
        self.assertEqual(result, [{"id": 1}])




class HeaderLeanokWithoutProofLeanokTests(unittest.TestCase):
    """Tests for the new mismatch category: header \\leanok paired with a
    proof block that lacks its own \\leanok."""

    def _run_scan(self, tex_source: str) -> list:
        with tempfile.TemporaryDirectory() as tmp_dir:
            blueprint_src = Path(tmp_dir) / "blueprint" / "src"
            chapter_dir = blueprint_src / "chapter"
            chapter_dir.mkdir(parents=True)
            (chapter_dir / "ch01_test.tex").write_text(tex_source.strip() + "\n")
            return find_header_leanok_without_proof_leanok(blueprint_src)

    def test_header_leanok_without_proof_leanok_is_reported(self) -> None:
        """(a) header \\leanok + proof block without proof \\leanok is reported."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}\label{lem:test}
  \lean{Foo.bar}
  \leanok
\end{lemma}
\begin{proof}
  Proof text without \leanok.
\end{proof}
"""
        )
        self.assertEqual(len(mismatches), 1)
        self.assertEqual(mismatches[0].env_type, "lemma")
        self.assertEqual(mismatches[0].label, "lem:test")

    def test_header_and_proof_both_leanok_is_ok(self) -> None:
        """(b) header \\leanok + proof \\leanok is ok."""
        mismatches = self._run_scan(
            r"""
\begin{theorem}\label{thm:ok}
  \lean{Foo.ok}
  \leanok
\end{theorem}
\begin{proof}\leanok
  Proof text with \leanok.
\end{proof}
"""
        )
        self.assertEqual(mismatches, [])

    def test_statement_only_no_proof_block_is_ok(self) -> None:
        """(c) statement-only entry with no proof remains ok."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}\label{lem:stmt-only}
  \lean{Foo.stmtOnly}
  \leanok
\end{lemma}
"""
        )
        self.assertEqual(mismatches, [])

    def test_consecutive_theorem_like_environments_do_not_share_proofs(self) -> None:
        """A proof of the second statement is not attributed to the first."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}\label{lem:first}
  \lean{Foo.first}
  \leanok
\end{lemma}
\begin{lemma}\label{lem:second}
  \lean{Foo.second}
  \leanok
\end{lemma}
\begin{proof}
  Proof of the second statement, without \leanok.
\end{proof}
"""
        )
        self.assertEqual(len(mismatches), 1)
        self.assertEqual(mismatches[0].label, "lem:second")

    def test_multiline_lean_blocks_are_handled(self) -> None:
        """(d) multiline \\lean{} remains ok when both have \\leanok."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}\label{lem:multi}
  \lean{Foo.bar, Foo.baz, Foo.qux, Foo.quux, Foo.corge,
        Foo.grault, Foo.garply, Foo.waldo, Foo.fred, Foo.plugh,
        Foo.xyzzy, Foo.thud}
  \leanok
\end{lemma}
\begin{proof}\leanok
  Proof.
\end{proof}
"""
        )
        self.assertEqual(mismatches, [])

    def test_multiline_lean_missing_proof_leanok_is_reported(self) -> None:
        """Multiline \\lean{} with header \\leanok but missing proof \\leanok."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}\label{lem:multi-missing}
  \lean{Foo.bar, Foo.baz, Foo.qux, Foo.quux, Foo.corge,
        Foo.grault, Foo.garply, Foo.waldo, Foo.fred, Foo.plugh,
        Foo.xyzzy, Foo.thud}
  \leanok
\end{lemma}
\begin{proof}
  Proof text without \leanok.
\end{proof}
"""
        )
        self.assertEqual(len(mismatches), 1)
        self.assertEqual(mismatches[0].label, "lem:multi-missing")

    def test_comment_leanok_is_ignored(self) -> None:
        r"""\\leanok inside a TeX ``%`` comment does not count as a marker."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}\label{lem:comment}
  \lean{Foo.comment}
  % \leanok was here but is commented out.
\end{lemma}
\begin{proof}\leanok
  Proof.
\end{proof}
"""
        )
        self.assertEqual(mismatches, [])

    def test_leanok_in_prose_is_ignored(self) -> None:
        """A prose mention like ``not marked \\leanok`` inside the statement
        body must not be counted as a real marker."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}\label{lem:prose}
  \lean{Foo.prose}
  This lemma is not marked \leanok.
\end{lemma}
\begin{proof}
  Proof.
\end{proof}
"""
        )
        self.assertEqual(mismatches, [])

    def test_header_no_leanok_proof_has_leanok_is_not_reported(self) -> None:
        """The check is one-directional: only header-with-\\leanok +
        proof-without-\\leanok is reported.  The reverse is not flagged."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}\label{lem:reverse}
  \lean{Foo.reverse}
\end{lemma}
\begin{proof}\leanok
  Proof.
\end{proof}
"""
        )
        self.assertEqual(mismatches, [])

    def test_intervening_remark_between_statement_and_proof(self) -> None:
        """A remark between the statement and its proof does not confuse
        the scanning — the proof is still the immediately-following block."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}\label{lem:intervening}
  \lean{Foo.intervening}
  \leanok
\end{lemma}
\begin{remark}
  Intervening remark.
\end{remark}
\begin{proof}
  Proof without \leanok.
\end{proof}
"""
        )
        self.assertEqual(len(mismatches), 1)
        self.assertEqual(mismatches[0].label, "lem:intervening")

    def test_corollary_and_proposition_are_also_checked(self) -> None:
        """Corollary and proposition environments are checked alongside
        lemma and theorem."""
        mismatches = self._run_scan(
            r"""
\begin{corollary}\label{cor:test}
  \lean{Foo.cor}
  \leanok
\end{corollary}
\begin{proof}
  Proof without \leanok.
\end{proof}

\begin{proposition}\label{prop:test}
  \lean{Foo.prop}
  \leanok
\end{proposition}
\begin{proof}\leanok
  Proof with \leanok.
\end{proof}
"""
        )
        self.assertEqual(len(mismatches), 1)
        self.assertEqual(mismatches[0].env_type, "corollary")

    def test_escaped_percent_leanok_is_not_a_comment(self) -> None:
        r"""A literal ``\%leanok`` in the source is not stripped by
        comment processing and, since it doesn't match ``\\leanok\\b``,
        should not be treated as a marker."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}\label{lem:escaped}
  \lean{Foo.escaped}
  \%leanok is not a real marker.
\end{lemma}
\begin{proof}\leanok
  Proof.
\end{proof}
"""
        )
        self.assertEqual(mismatches, [])

    def test_no_label_environment_is_still_flagged(self) -> None:
        """An environment without a \\label should still be flagged."""
        mismatches = self._run_scan(
            r"""
\begin{lemma}
  \lean{Foo.nolabel}
  \leanok
\end{lemma}
\begin{proof}
  Proof without \leanok.
\end{proof}
"""
        )
        self.assertEqual(len(mismatches), 1)
        self.assertEqual(mismatches[0].label, None)


if __name__ == "__main__":
    unittest.main()
