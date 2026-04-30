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

_PATHS_KEY_RE = re.compile(r"^(?P<indent>\s*)paths:\s*$")
_PATH_ENTRY_RE = re.compile(
    r"^(?P<indent>\s*)-\s+['\"]?(?P<path>[^'\"\n]+)['\"]?\s*$"
)


def path_filter_blocks(text: str) -> list[set[str]]:
    """Extract only entries inside GitHub Actions ``paths:`` filters."""

    blocks: list[set[str]] = []
    in_paths = False
    paths_indent = 0
    current_block: set[str] = set()

    for raw_line in text.splitlines():
        while True:
            if in_paths:
                stripped = raw_line.strip()
                if not stripped or stripped.startswith("#"):
                    break
                indent = len(raw_line) - len(raw_line.lstrip(" "))
                if indent <= paths_indent:
                    blocks.append(current_block)
                    in_paths = False
                    current_block = set()
                    # Reconsider this same line: it might start another paths block.
                    continue
                if match := _PATH_ENTRY_RE.match(raw_line):
                    current_block.add(match.group("path").strip())
                break

            if match := _PATHS_KEY_RE.match(raw_line):
                in_paths = True
                paths_indent = len(match.group("indent"))
                current_block = set()
            break

    if in_paths:
        blocks.append(current_block)
    return blocks


def workflow_path_filter_blocks(path: str) -> list[set[str]]:
    """Extract path-filter blocks from a GitHub Actions workflow file."""

    return path_filter_blocks((PROJECT_ROOT / path).read_text(encoding="utf-8"))


class BlueprintScriptSurfaceTests(unittest.TestCase):
    def test_blueprint_named_scripts_are_classified(self) -> None:
        candidates = {
            path.relative_to(PROJECT_ROOT).as_posix()
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

    def test_path_filter_parser_ignores_non_trigger_lists(self) -> None:
        text = """
        on:
          pull_request:
            paths:
              - 'scripts/tex_utils.py'
        jobs:
          test:
            steps:
              - uses: actions/checkout@v6
              - run: python3 scripts/blueprint_lean_sync.py --root . --ci
        """

        self.assertEqual(path_filter_blocks(text), [{"scripts/tex_utils.py"}])

    def test_workflow_path_filters_cover_surface(self) -> None:
        for workflow, required_paths in WORKFLOW_REQUIRED_PATHS.items():
            with self.subTest(workflow=workflow):
                path_blocks = workflow_path_filter_blocks(workflow)
                self.assertGreater(len(path_blocks), 0)
                for path_block in path_blocks:
                    missing_paths = required_paths - path_block
                    self.assertFalse(missing_paths, missing_paths)

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
