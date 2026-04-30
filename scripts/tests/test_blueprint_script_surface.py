#!/usr/bin/env python3
"""Coverage-policy tests for blueprint-support Python helpers."""

from __future__ import annotations

import re
import unittest
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]

BLUEPRINT_SUPPORT_SCRIPTS = {
    "scripts/blueprint_lean_sync.py": {
        "tests": {"scripts/tests/test_blueprint_lean_sync.py"},
        "workflows": {
            ".github/workflows/blueprint-sync.yml",
            ".github/workflows/lint-blueprint.yml",
        },
    },
    "scripts/blueprint_leanok_axioms.py": {
        "tests": {"scripts/tests/test_blueprint_leanok_axioms.py"},
        "workflows": {".github/workflows/blueprint-sync.yml"},
    },
    "scripts/check_blueprint_sync.py": {
        "tests": {"scripts/tests/test_check_blueprint_sync.py"},
        "workflows": {".github/workflows/blueprint-sync.yml"},
    },
    "scripts/check_blueprint_latex.py": {
        "tests": {"scripts/tests/test_check_blueprint_latex.py"},
        "workflows": {".github/workflows/lint-blueprint.yml"},
    },
    "scripts/tex_utils.py": {
        # Shared utility: the behavior is covered through both consumers rather
        # than by a separate duplicate test module.
        "tests": {
            "scripts/tests/test_blueprint_lean_sync.py",
            "scripts/tests/test_check_blueprint_latex.py",
        },
        "workflows": {
            ".github/workflows/blueprint-sync.yml",
            ".github/workflows/lint-blueprint.yml",
        },
    },
}

WORKFLOW_REQUIRED_PATHS = {
    ".github/workflows/blueprint-sync.yml": {
        "scripts/blueprint_lean_sync.py",
        "scripts/blueprint_leanok_axioms.py",
        "scripts/check_blueprint_sync.py",
        "scripts/tex_utils.py",
        "scripts/tests/**",
        ".github/workflows/blueprint-sync.yml",
    },
    ".github/workflows/lint-blueprint.yml": {
        "scripts/blueprint_lean_sync.py",
        "scripts/check_blueprint_latex.py",
        "scripts/tex_utils.py",
        "scripts/tests/**",
        ".github/workflows/lint-blueprint.yml",
    },
}

_PATH_LINE_RE = re.compile(r"^\s*-\s+['\"]?([^'\"\n]+)['\"]?\s*$")


def workflow_paths(path: str) -> set[str]:
    """Extract literal path-filter entries from a GitHub Actions workflow."""

    text = (PROJECT_ROOT / path).read_text(encoding="utf-8")
    return {
        match.group(1)
        for line in text.splitlines()
        if (match := _PATH_LINE_RE.match(line))
    }


class BlueprintScriptSurfaceTests(unittest.TestCase):
    def test_blueprint_named_scripts_are_classified(self) -> None:
        candidates = {
            str(path.relative_to(PROJECT_ROOT))
            for path in (PROJECT_ROOT / "scripts").glob("*.py")
            if "blueprint" in path.name or path.name == "tex_utils.py"
        }

        self.assertEqual(candidates, set(BLUEPRINT_SUPPORT_SCRIPTS))

    def test_surface_scripts_and_tests_exist(self) -> None:
        for script, metadata in BLUEPRINT_SUPPORT_SCRIPTS.items():
            with self.subTest(script=script):
                self.assertTrue((PROJECT_ROOT / script).is_file())
                for test_path in metadata["tests"]:
                    self.assertTrue((PROJECT_ROOT / test_path).is_file(), test_path)

    def test_workflow_path_filters_cover_surface(self) -> None:
        for workflow, required_paths in WORKFLOW_REQUIRED_PATHS.items():
            with self.subTest(workflow=workflow):
                self.assertTrue(
                    required_paths <= workflow_paths(workflow),
                    required_paths - workflow_paths(workflow),
                )

    def test_surface_doc_mentions_every_script_and_workflow(self) -> None:
        doc = (PROJECT_ROOT / "docs" / "blueprint-script-coverage.md").read_text(
            encoding="utf-8"
        )
        for script, metadata in BLUEPRINT_SUPPORT_SCRIPTS.items():
            with self.subTest(script=script):
                self.assertIn(script, doc)
                for workflow in metadata["workflows"]:
                    self.assertIn(workflow, doc)


if __name__ == "__main__":
    unittest.main()
