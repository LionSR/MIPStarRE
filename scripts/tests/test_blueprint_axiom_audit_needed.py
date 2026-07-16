#!/usr/bin/env python3
"""Tests for blueprint axiom-audit path classification."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from blueprint_axiom_audit_needed import (
    diff_touches_formalization_markers,
    needs_axiom_audit_for_paths,
)


class BlueprintAxiomAuditNeededTests(unittest.TestCase):
    def test_uses_only_blueprint_diff_skips_heavy_audit(self) -> None:
        diff = r"""
diff --git a/blueprint/src/chapter/ch09_pasting.tex b/blueprint/src/chapter/ch09_pasting.tex
@@ -10,0 +11 @@
+  \uses{lem:looks-easy-but-took-me-a-while}
"""
        self.assertFalse(diff_touches_formalization_markers(diff))
        self.assertFalse(
            needs_axiom_audit_for_paths(["blueprint/src/chapter/ch09_pasting.tex"], diff)
        )

    def test_lean_marker_blueprint_diff_requires_heavy_audit(self) -> None:
        diff = r"""
diff --git a/blueprint/src/chapter/ch09_pasting.tex b/blueprint/src/chapter/ch09_pasting.tex
@@ -10,0 +11,2 @@
+  \lean{MIPStarRE.LDT.Pasting.someTheorem}
+  \leanok
"""
        self.assertTrue(diff_touches_formalization_markers(diff))
        self.assertTrue(
            needs_axiom_audit_for_paths(["blueprint/src/chapter/ch09_pasting.tex"], diff)
        )

    def test_removed_leanok_requires_heavy_audit(self) -> None:
        diff = r"""
diff --git a/blueprint/src/chapter/ch09_pasting.tex b/blueprint/src/chapter/ch09_pasting.tex
@@ -10 +9,0 @@
-  \leanok
"""
        self.assertTrue(diff_touches_formalization_markers(diff))

    def test_lean_source_requires_heavy_audit(self) -> None:
        self.assertTrue(
            needs_axiom_audit_for_paths(["MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean"])
        )

    def test_workflow_or_audit_script_change_requires_heavy_audit(self) -> None:
        self.assertTrue(needs_axiom_audit_for_paths([".github/workflows/pr-ci.yml"]))
        self.assertTrue(needs_axiom_audit_for_paths(["scripts/blueprint_leanok_axioms.py"]))

    def test_plain_blueprint_prose_skips_heavy_audit(self) -> None:
        diff = r"""
diff --git a/blueprint/src/chapter/ch09_pasting.tex b/blueprint/src/chapter/ch09_pasting.tex
@@ -10 +10 @@
-  Old prose.
+  New prose.
"""
        self.assertFalse(
            needs_axiom_audit_for_paths(["blueprint/src/chapter/ch09_pasting.tex"], diff)
        )


if __name__ == "__main__":
    unittest.main()
