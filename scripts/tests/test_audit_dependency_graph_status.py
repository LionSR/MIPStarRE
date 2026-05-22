"""Regression tests for scripts/audit_dependency_graph_status.py."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from audit_dependency_graph_status import run_audit  # noqa: E402


def write_graph(root: Path, dot: str) -> Path:
    """Create a minimal generated dependency-graph HTML fixture."""
    path = root / "blueprint" / "web" / "dep_graph_document.html"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"""<html><body>
<script>
graphContainer.graphviz().renderDot(`strict digraph "" {{ {dot} }}`).on("end", interactive);
</script>
</body></html>
""",
        encoding="utf-8",
    )
    return path


GOOD_DOT = r'''
"thm:naimark" [color=green, fillcolor="#1CAC78", label=naimark, shape=ellipse, style=filled];
"rem:lean-naimark-auxiliary-declarations" [color=green, fillcolor="#B0ECA3", label="lean-naimark-auxiliary-declarations", shape=box, style=filled];
"thm:main-formal" [color=blue, label="main-formal", shape=ellipse];
"thm:main-induction" [color=blue, label="main-induction", shape=ellipse];
"thm:main-formal-current-interface" [color=green, fillcolor="#1CAC78", label="main-formal-current-interface", shape=ellipse, style=filled];
"thm:main-induction-current-interface" [color=green, fillcolor="#1CAC78", label="main-induction-current-interface", shape=ellipse, style=filled];
"prop:main-formal-source-obligation" [color=blue, label="main-formal-source-obligation", shape=ellipse];
"prop:main-formal-source-small-error-obligation" [color=blue, label="main-formal-source-small-error-obligation", shape=ellipse];
"prop:main-formal-source-two-space-role-register" [color=blue, label="main-formal-source-two-space-role-register", shape=ellipse];
"prop:main-formal-source-k-range-boundary" [color=blue, label="main-formal-source-k-range-boundary", shape=ellipse];
"prop:main-induction-source-range-obligation" [color=blue, fillcolor="#A3D6FF", label="main-induction-source-range-obligation", shape=ellipse, style=filled];
"prop:main-induction-successor-small-error-construction" [color=green, fillcolor="#1CAC78", label="main-induction-successor-small-error-construction", shape=ellipse, style=filled];
"prop:main-induction-successor-predecessor-induction" [color=green, fillcolor="#1CAC78", label="main-induction-successor-predecessor-induction", shape=ellipse, style=filled];
"prop:main-induction-successor-answer-valued-pasting" [color=green, fillcolor="#1CAC78", label="main-induction-successor-answer-valued-pasting", shape=ellipse, style=filled];
"prop:main-induction-successor-answer-slice-realization" [color=blue, label="main-induction-successor-answer-slice-realization", shape=ellipse];
"thm:naimark" -> "rem:lean-naimark-auxiliary-declarations" [style=dashed];
'''


class DependencyGraphStatusAuditTests(unittest.TestCase):
    def test_accepts_expected_local_frontier_statuses(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            graph = write_graph(Path(tmp), GOOD_DOT)

            result = run_audit(graph)

        self.assertEqual(result.findings, ())

    def test_flags_retired_successor_node(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            graph = write_graph(
                Path(tmp),
                GOOD_DOT
                + '"def:successor-obligation-reductions" '
                '[color=green, fillcolor="#B0ECA3", shape=box, style=filled];',
            )

            result = run_audit(graph)

        self.assertEqual(len(result.findings), 1)
        self.assertEqual(result.findings[0].label, "def:successor-obligation-reductions")
        self.assertEqual(result.findings[0].kind, "retired-node-present")

    def test_flags_proof_filled_frontier_node(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            graph = write_graph(
                Path(tmp),
                GOOD_DOT.replace(
                    '"prop:main-induction-source-range-obligation" '
                    '[color=blue, fillcolor="#A3D6FF", '
                    'label="main-induction-source-range-obligation", '
                    'shape=ellipse, style=filled];',
                    '"prop:main-induction-source-range-obligation" '
                    '[color=green, fillcolor="#1CAC78", '
                    'label="main-induction-source-range-obligation", '
                    'shape=ellipse, style=filled];',
                ),
            )

            result = run_audit(graph)

        self.assertEqual(len(result.findings), 1)
        self.assertEqual(
            result.findings[0].label,
            "prop:main-induction-source-range-obligation",
        )
        self.assertEqual(result.findings[0].kind, "frontier-proof-filled")

    def test_flags_missing_frontier_node(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            graph = write_graph(
                Path(tmp),
                GOOD_DOT.replace(
                    '"prop:main-formal-source-small-error-obligation" '
                    '[color=blue, '
                    'label="main-formal-source-small-error-obligation", '
                    'shape=ellipse];\n',
                    "",
                ),
            )

            result = run_audit(graph)

        self.assertEqual(len(result.findings), 1)
        self.assertEqual(
            result.findings[0].label,
            "prop:main-formal-source-small-error-obligation",
        )
        self.assertEqual(result.findings[0].kind, "frontier-node-missing")

    def test_flags_unfilled_current_interface(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            graph = write_graph(
                Path(tmp),
                GOOD_DOT.replace(
                    '"thm:main-induction-current-interface" '
                    '[color=green, fillcolor="#1CAC78", ',
                    '"thm:main-induction-current-interface" '
                    '[color=blue, fillcolor="#A3D6FF", ',
                ),
            )

            result = run_audit(graph)

        self.assertEqual(len(result.findings), 1)
        self.assertEqual(result.findings[0].label, "thm:main-induction-current-interface")
        self.assertEqual(result.findings[0].kind, "proved-node-not-proof-filled")

    def test_flags_unproved_looking_naimark_node(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            graph = write_graph(
                Path(tmp),
                GOOD_DOT.replace(
                    '"thm:naimark" [color=green, fillcolor="#1CAC78", ',
                    '"thm:naimark" [color=blue, fillcolor="#A3D6FF", ',
                ),
            )

            result = run_audit(graph)

        self.assertEqual(len(result.findings), 2)
        self.assertEqual({finding.kind for finding in result.findings},
            {"proved-node-not-proof-filled", "formalized-node-not-green"})


if __name__ == "__main__":
    unittest.main()
