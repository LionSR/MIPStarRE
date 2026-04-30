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

_PATHS_KEY_RE = re.compile(
    r"^(?P<indent>\s*)(?:paths|'paths'|\"paths\"):\s*"
    r"(?:(?P<anchor>&[A-Za-z0-9_-]+)\s*)?"
    r"(?:(?P<alias>\*[A-Za-z0-9_-]+)|(?P<flow>\[[^\n]*\]))?"
    r"\s*(?:#.*)?$"
)
_PATH_ENTRY_RE = re.compile(
    r"^(?P<indent>\s*)-\s+"
    r"(?P<scalar>(?:'[^'\n]*'|\"[^\"\n]*\"|[^#\n]*?))"
    r"(?:\s+#.*)?\s*$"
)
_ON_KEY_RE = re.compile(r"^(?P<indent>\s*)(?:on|'on'|\"on\"):\s*(?:#.*)?$")
_YAML_KEY_RE = re.compile(r"^(?P<indent>\s*)[^:#]+:\s*.*$")


def _unquote_path_scalar(scalar: str) -> str:
    scalar = scalar.strip()
    if len(scalar) >= 2 and scalar[0] == scalar[-1] and scalar[0] in {"'", '"'}:
        return scalar[1:-1]
    return scalar


def _flow_path_scalars(flow: str) -> set[str]:
    """Parse a simple YAML flow-style path list such as ``['a', \"b\"]``."""

    entries: list[str] = []
    current: list[str] = []
    quote: str | None = None
    for char in flow.strip()[1:-1]:
        if quote is not None:
            current.append(char)
            if char == quote:
                quote = None
        elif char in {"'", '"'}:
            quote = char
            current.append(char)
        elif char == ",":
            entries.append("".join(current))
            current = []
        else:
            current.append(char)
    entries.append("".join(current))

    return {
        path
        for entry in entries
        if (path := _unquote_path_scalar(entry))
    }


def path_filter_blocks(text: str) -> list[set[str]]:
    """Extract entries from GitHub Actions trigger ``paths:`` filters."""

    blocks: list[set[str]] = []
    anchors: dict[str, set[str]] = {}
    in_on = False
    on_indent = 0
    event_indent: int | None = None
    event_child_indent: int | None = None
    in_paths = False
    paths_indent = 0
    current_block: set[str] = set()
    current_anchor: str | None = None

    def finish_current_block() -> None:
        nonlocal current_anchor, current_block, in_paths
        block = set(current_block)
        blocks.append(block)
        if current_anchor is not None:
            anchors[current_anchor] = block
        current_anchor = None
        current_block = set()
        in_paths = False

    def start_paths_block(match: re.Match[str]) -> None:
        nonlocal current_anchor, current_block, in_paths, paths_indent
        anchor = match.group("anchor")
        anchor_name = anchor.removeprefix("&") if anchor else None
        if alias := match.group("alias"):
            blocks.append(set(anchors.get(alias.removeprefix("*"), set())))
        elif flow := match.group("flow"):
            block = _flow_path_scalars(flow)
            blocks.append(block)
            if anchor_name is not None:
                anchors[anchor_name] = block
        else:
            in_paths = True
            paths_indent = len(match.group("indent"))
            current_block = set()
            current_anchor = anchor_name

    for raw_line in text.splitlines():
        while True:
            stripped = raw_line.strip()
            if not stripped or stripped.startswith("#"):
                break
            indent = len(raw_line) - len(raw_line.lstrip(" "))

            if in_paths:
                if indent <= paths_indent:
                    finish_current_block()
                    # Reconsider this same line: it might start another paths block.
                    continue
                if match := _PATH_ENTRY_RE.match(raw_line):
                    path = _unquote_path_scalar(match.group("scalar"))
                    if path:
                        current_block.add(path)
                break

            if in_on:
                if indent <= on_indent:
                    in_on = False
                    event_indent = None
                    event_child_indent = None
                    # Reconsider this same line: it might start another top-level block.
                    continue

                if match := _PATHS_KEY_RE.match(raw_line):
                    path_key_indent = len(match.group("indent"))
                    if event_indent is not None and (
                        event_child_indent is None or path_key_indent == event_child_indent
                    ):
                        event_child_indent = path_key_indent
                        start_paths_block(match)
                    break

                if match := _YAML_KEY_RE.match(raw_line):
                    key_indent = len(match.group("indent"))
                    if event_indent is None or key_indent <= event_indent:
                        event_indent = key_indent
                        event_child_indent = None
                    elif event_child_indent is None:
                        event_child_indent = key_indent
                break

            if match := _ON_KEY_RE.match(raw_line):
                in_on = True
                on_indent = len(match.group("indent"))
                event_indent = None
                event_child_indent = None
            break

    if in_paths:
        finish_current_block()
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

    def test_path_filter_parser_ignores_non_trigger_paths_keys(self) -> None:
        text = """
        on:
          pull_request:
            paths:
              - 'scripts/tex_utils.py'
        jobs:
          test:
            steps:
              - uses: actions/cache@v5
                with:
                  paths:
                    - '.lake/build'
        """

        self.assertEqual(path_filter_blocks(text), [{"scripts/tex_utils.py"}])

    def test_path_filter_parser_resolves_yaml_anchor_aliases(self) -> None:
        text = """
        on:
          push:
            paths: &blueprint_paths
              - 'scripts/blueprint_lean_sync.py'
              - 'scripts/tex_utils.py'
          pull_request:
            paths: *blueprint_paths
        """

        expected = {"scripts/blueprint_lean_sync.py", "scripts/tex_utils.py"}
        self.assertEqual(path_filter_blocks(text), [expected, expected])

    def test_path_filter_parser_accepts_yaml_comments(self) -> None:
        text = """
        on:
          push:
            paths: &blueprint_paths  # shared trigger list
              - 'scripts/blueprint_lean_sync.py'  # sync helper
              - "scripts/tex_utils.py"  # shared helper
              - scripts/tests/**  # helper tests
          pull_request:
            paths: *blueprint_paths  # reuse push paths
        """

        expected = {
            "scripts/blueprint_lean_sync.py",
            "scripts/tex_utils.py",
            "scripts/tests/**",
        }
        self.assertEqual(path_filter_blocks(text), [expected, expected])

    def test_path_filter_parser_accepts_flow_style_lists_and_quoted_on(self) -> None:
        text = """
        "on":
          push:
            paths: &blueprint_paths ['scripts/blueprint_lean_sync.py', scripts/tests/**]
          pull_request:
            paths: *blueprint_paths
        """

        expected = {"scripts/blueprint_lean_sync.py", "scripts/tests/**"}
        self.assertEqual(path_filter_blocks(text), [expected, expected])

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
