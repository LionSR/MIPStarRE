#!/usr/bin/env python3
r"""Decide whether a blueprint-facing diff needs the heavy Lean axiom audit.

There are two logically separate blueprint checks:

* the fast surface check that ``\lean{...}`` references match Lean declarations;
* the expensive proof-status check that builds Lean and audits proof-level
  ``\leanok`` declarations for ``sorryAx``.

This helper classifies when the second check is mathematically relevant.  The
pull-request surface-sync workflow uses the result for reporting; the full
``scripts/blueprint_leanok_axioms.py --ci`` audit is run locally or in a Lean
environment with enough disk for toolchain setup.  A proof-dependency edit such
as adding ``\uses{...}`` does not change the set of declarations whose axiom
closure is claimed by the blueprint, so it does not need a full Lean build.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable, Sequence


FORMALIZATION_MARKER_RE = re.compile(
    r"\\(?:lean|leanok|notready|proves)\b|\\lean\{"
)


def _run(cmd: Sequence[str]) -> str:
    return subprocess.check_output(cmd, text=True)


def _normalize_path(path: str) -> str:
    stripped = path.strip()
    return stripped[2:] if stripped.startswith("./") else stripped


def _is_lean_source(path: str) -> bool:
    return path.endswith(".lean") and (
        path.startswith("MIPStarRE/") or path.startswith("scripts/")
    )


def _is_lean_project_metadata(path: str) -> bool:
    return path in {
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
    }


def _is_axiom_audit_implementation(path: str) -> bool:
    return path in {
        "scripts/blueprint_lean_sync.py",
        "scripts/blueprint_leanok_axioms.py",
        "scripts/tex_utils.py",
        ".github/workflows/blueprint-sync.yml",
    }


def _is_blueprint_tex(path: str) -> bool:
    return path.startswith("blueprint/") and path.endswith(".tex")


def changed_files(base_ref: str, head_ref: str) -> list[str]:
    """Return files changed between ``base_ref`` and ``head_ref``."""
    out = _run(["git", "diff", "--name-only", f"{base_ref}...{head_ref}"])
    return [_normalize_path(line) for line in out.splitlines() if line.strip()]


def diff_for_paths(base_ref: str, head_ref: str, paths: Iterable[str]) -> str:
    """Return a zero-context diff for ``paths``."""
    path_list = list(paths)
    if not path_list:
        return ""
    return _run(["git", "diff", "--unified=0", f"{base_ref}...{head_ref}", "--", *path_list])


def diff_touches_formalization_markers(diff_text: str) -> bool:
    """Return whether a diff adds or removes Lean-facing blueprint markers."""
    for raw_line in diff_text.splitlines():
        if not raw_line.startswith(("+", "-")):
            continue
        if raw_line.startswith(("+++", "---")):
            continue
        if FORMALIZATION_MARKER_RE.search(raw_line[1:]):
            return True
    return False


def needs_axiom_audit_for_paths(changed: Iterable[str], blueprint_diff: str = "") -> bool:
    """Classify whether the heavy Lean axiom audit is required."""
    changed_paths = [_normalize_path(path) for path in changed]
    for path in changed_paths:
        if _is_lean_source(path):
            return True
        if _is_lean_project_metadata(path):
            return True
        if _is_axiom_audit_implementation(path):
            return True
    return diff_touches_formalization_markers(blueprint_diff)


def default_base_ref() -> str:
    if env_base := os.environ.get("BASE_REF"):
        return env_base
    if github_base := os.environ.get("GITHUB_BASE_REF"):
        return f"origin/{github_base}"
    return "origin/main"


def write_github_output(name: str, value: str) -> None:
    if output_path := os.environ.get("GITHUB_OUTPUT"):
        with Path(output_path).open("a", encoding="utf-8") as handle:
            handle.write(f"{name}={value}\n")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-ref", default=default_base_ref())
    parser.add_argument("--head-ref", default="HEAD")
    parser.add_argument("--github-output", action="store_true")
    args = parser.parse_args(argv)

    files = changed_files(args.base_ref, args.head_ref)
    blueprint_files = [path for path in files if _is_blueprint_tex(path)]
    blueprint_diff = diff_for_paths(args.base_ref, args.head_ref, blueprint_files)
    needed = needs_axiom_audit_for_paths(files, blueprint_diff)
    value = "true" if needed else "false"
    print(value)
    if args.github_output:
        write_github_output("needs_axiom_audit", value)
    return 0


if __name__ == "__main__":
    sys.exit(main())
