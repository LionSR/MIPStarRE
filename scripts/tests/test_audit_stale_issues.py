#!/usr/bin/env python3
"""Regression tests for scripts/audit_stale_issues.py."""

from __future__ import annotations

import json
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import audit_stale_issues  # noqa: E402
from audit_stale_issues import (  # noqa: E402
    DeclCitation,
    FileCitation,
    audit_issue,
    build_decl_index,
    extract_decl_citations,
    extract_file_citations,
    line_is_sorry,
    main,
    render_json_report,
    render_text_report,
    run_audit,
)


def _make_fake_repo(root: Path) -> None:
    """Create a minimal MIPStarRE/ tree used by audit tests."""
    mod = root / "MIPStarRE" / "LDT" / "Fake"
    mod.mkdir(parents=True)
    (mod / "Live.lean").write_text(
        textwrap.dedent(
            """\
            import Mathlib

            namespace Fake

            /-- A live declaration. -/
            theorem live_theorem : 1 = 1 := by rfl

            /-- Another live declaration. -/
            def liveDef : Nat := 0

            /-- A sorry we still ship. -/
            theorem still_open : True := by
              sorry

            end Fake
            """
        )
    )


class ExtractFileCitationsTests(unittest.TestCase):
    def test_extracts_path_with_colon_line(self) -> None:
        body = "See `MIPStarRE/LDT/Foo/Bar.lean:141` for details."
        self.assertEqual(
            extract_file_citations(body),
            [FileCitation(path="MIPStarRE/LDT/Foo/Bar.lean", line=141)],
        )

    def test_attaches_nearby_line_word_to_sole_path_on_line(self) -> None:
        body = "at MIPStarRE/LDT/Foo/Bar.lean on line 42."
        self.assertEqual(
            extract_file_citations(body),
            [FileCitation(path="MIPStarRE/LDT/Foo/Bar.lean", line=42)],
        )

    def test_does_not_cross_attribute_when_multiple_paths_on_line(self) -> None:
        body = (
            "MIPStarRE/A.lean and MIPStarRE/B.lean both matter; also line 99."
        )
        self.assertEqual(
            extract_file_citations(body),
            [
                FileCitation(path="MIPStarRE/A.lean", line=None),
                FileCitation(path="MIPStarRE/B.lean", line=None),
            ],
        )

    def test_deduplicates_repeated_citations(self) -> None:
        body = (
            "See MIPStarRE/X.lean:10.\n"
            "Again MIPStarRE/X.lean:10.\n"
            "And MIPStarRE/X.lean without a line."
        )
        self.assertEqual(
            extract_file_citations(body),
            [
                FileCitation(path="MIPStarRE/X.lean", line=10),
                FileCitation(path="MIPStarRE/X.lean", line=None),
            ],
        )

    def test_extracts_path_from_github_blob_url(self) -> None:
        body = (
            "See https://github.com/LionSR/MIPStarRE/blob/main/"
            "MIPStarRE/LDT/Foo/Bar.lean#L141 for details."
        )
        self.assertEqual(
            extract_file_citations(body),
            [FileCitation(path="MIPStarRE/LDT/Foo/Bar.lean", line=141)],
        )

    def test_extracts_path_from_blob_url_with_slash_in_ref(self) -> None:
        body = (
            "See https://github.com/LionSR/MIPStarRE/blob/feature/foo/"
            "MIPStarRE/LDT/Foo/Bar.lean#L13 for details."
        )
        self.assertEqual(
            extract_file_citations(body),
            [FileCitation(path="MIPStarRE/LDT/Foo/Bar.lean", line=13)],
        )


class ExtractDeclCitationsTests(unittest.TestCase):
    def test_extracts_backtick_identifiers(self) -> None:
        body = "We need to finish `fromHToG` and `hBConsistency_core`."
        self.assertEqual(
            extract_decl_citations(body),
            [
                DeclCitation(name="fromHToG"),
                DeclCitation(name="hBConsistency_core"),
            ],
        )

    def test_drops_stoplist_tokens(self) -> None:
        body = "This `sorry` should not trigger; neither should `main`."
        self.assertEqual(extract_decl_citations(body), [])

    def test_drops_all_upper_tokens(self) -> None:
        body = "Ignore `TODO` style tokens."
        self.assertEqual(extract_decl_citations(body), [])

    def test_deduplicates_repeated_mentions(self) -> None:
        body = "`fooBar` and again `fooBar` on another line."
        self.assertEqual(
            extract_decl_citations(body),
            [DeclCitation(name="fooBar")],
        )


class BuildDeclIndexTests(unittest.TestCase):
    def test_collects_short_and_qualified_names(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_fake_repo(root)
            index = build_decl_index(root / "MIPStarRE")
            self.assertIn("live_theorem", index)
            self.assertIn("liveDef", index)
            self.assertIn("still_open", index)


class LineIsSorryTests(unittest.TestCase):
    def test_returns_true_for_sorry_line_and_false_otherwise(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            f = root / "x.lean"
            f.write_text("theorem a : 1 = 1 := rfl\ntheorem b : True := by sorry\n")
            self.assertFalse(line_is_sorry(f, 1))
            self.assertTrue(line_is_sorry(f, 2))

    def test_out_of_range_returns_none(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            f = root / "x.lean"
            f.write_text("only one line\n")
            self.assertIsNone(line_is_sorry(f, 9))

    def test_ignores_sorry_in_line_comment(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            f = root / "x.lean"
            f.write_text("theorem a : 1 = 1 := rfl -- was sorry\n")
            self.assertFalse(line_is_sorry(f, 1))

    def test_sees_sorry_before_trailing_comment(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            f = root / "x.lean"
            f.write_text("theorem b : True := by sorry -- TODO close\n")
            self.assertTrue(line_is_sorry(f, 1))


class AuditIssueTests(unittest.TestCase):
    def test_flags_missing_file_missing_decl_and_resolved_sorry(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_fake_repo(root)
            decl_index = build_decl_index(root / "MIPStarRE")

            # Live.lean line 6 is `theorem live_theorem : 1 = 1 := by rfl`,
            # which no longer contains `sorry` — cite it to trigger the
            # non-sorry-line flag.  Live.lean line 13 is the real `  sorry`
            # line and must NOT trigger the flag (covered by the next test).
            issue = {
                "number": 42,
                "title": "example",
                "url": "https://example.invalid/42",
                "body": (
                    "Stale file: `MIPStarRE/LDT/Fake/Gone.lean:10`\n"
                    "Resolved line: `MIPStarRE/LDT/Fake/Live.lean:6`\n"
                    "Missing decl `ghost_lemma`. Live decl `live_theorem`.\n"
                ),
            }
            report = audit_issue(issue, root, decl_index)
            self.assertTrue(report.is_flagged)
            self.assertEqual(
                report.missing_files, ["MIPStarRE/LDT/Fake/Gone.lean:10"]
            )
            self.assertEqual(
                report.non_sorry_lines,
                [("MIPStarRE/LDT/Fake/Live.lean", 6)],
            )
            self.assertEqual(report.missing_decls, ["ghost_lemma"])

    def test_flags_out_of_range_line_as_stale(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_fake_repo(root)
            decl_index = build_decl_index(root / "MIPStarRE")
            issue = {
                "number": 99,
                "title": "past-EOF citation",
                "url": "",
                "body": "Out of range: `MIPStarRE/LDT/Fake/Live.lean:9999`.",
            }
            report = audit_issue(issue, root, decl_index)
            self.assertTrue(report.is_flagged)
            self.assertEqual(
                report.non_sorry_lines,
                [("MIPStarRE/LDT/Fake/Live.lean", 9999)],
            )

    def test_flags_file_citation_that_escapes_repo_root(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            outer = Path(td)
            root = outer / "repo"
            root.mkdir()
            _make_fake_repo(root)
            # The escaped file really exists and contains a sorry.  The audit
            # must still reject it instead of inspecting files outside root.
            (outer / "secret.lean").write_text("theorem ok : True := by\n  sorry\n")
            decl_index = build_decl_index(root / "MIPStarRE")
            issue = {
                "number": 100,
                "title": "path escape",
                "url": "",
                "body": "Escapes checkout: `MIPStarRE/../../secret.lean:2`.",
            }
            report = audit_issue(issue, root, decl_index)
            self.assertTrue(report.is_flagged)
            self.assertEqual(
                report.missing_files,
                ["MIPStarRE/../../secret.lean:2"],
            )
            self.assertEqual(report.non_sorry_lines, [])

    def test_not_flagged_when_all_citations_resolve(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_fake_repo(root)
            decl_index = build_decl_index(root / "MIPStarRE")
            issue = {
                "number": 7,
                "title": "ok",
                "url": "",
                "body": (
                    "Line `MIPStarRE/LDT/Fake/Live.lean:13` is still a sorry "
                    "for `still_open`."
                ),
            }
            report = audit_issue(issue, root, decl_index)
            self.assertFalse(report.is_flagged)


class RenderReportTests(unittest.TestCase):
    def test_text_and_json_renderers_include_flagged_issue(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_fake_repo(root)
            issue = {
                "number": 1,
                "title": "broken",
                "url": "u",
                "body": "`MIPStarRE/LDT/Fake/Gone.lean:3`",
            }
            reports = run_audit([issue], root)
            text = render_text_report(reports, only_flagged=True)
            self.assertIn("#1 — broken", text)
            self.assertIn("MIPStarRE/LDT/Fake/Gone.lean:3", text)

            payload = json.loads(render_json_report(reports))
            self.assertEqual(len(payload), 1)
            self.assertTrue(payload[0]["flagged"])
            self.assertEqual(
                payload[0]["missing_files"],
                ["MIPStarRE/LDT/Fake/Gone.lean:3"],
            )


class SelfTestCLITests(unittest.TestCase):
    def test_self_test_passes_on_fake_repo(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_fake_repo(root)
            exit_code = main(
                ["--repo-root", str(root), "--self-test"]
            )
            self.assertEqual(exit_code, 0)


if __name__ == "__main__":
    unittest.main()
