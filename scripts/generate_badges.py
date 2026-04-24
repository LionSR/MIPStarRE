#!/usr/bin/env python3
"""Generate Shields.io endpoint JSON for Lean repository badges."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tomllib
from pathlib import Path


SORRY_RE = re.compile(r"\bsorry\b")
AXIOM_RE = re.compile(r"(?m)^\s*axiom\s+[A-Za-z_]")


def tracked_lean_files(repo_root: Path) -> list[Path]:
    output = subprocess.check_output(
        ["git", "ls-files", "*.lean"], cwd=repo_root, text=True
    )
    return [repo_root / line for line in output.splitlines() if line]


def strip_comments_and_strings(source: str) -> str:
    result: list[str] = []
    i = 0
    block_depth = 0
    in_string = False

    while i < len(source):
        char = source[i]
        nxt = source[i + 1] if i + 1 < len(source) else ""

        if in_string:
            if char == "\\" and nxt:
                i += 2
                continue
            if char == '"':
                in_string = False
            result.append("\n" if char == "\n" else " ")
            i += 1
            continue

        if block_depth > 0:
            if char == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if char == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            result.append("\n" if char == "\n" else " ")
            i += 1
            continue

        if char == "-" and nxt == "-":
            while i < len(source) and source[i] != "\n":
                result.append(" ")
                i += 1
            continue

        if char == "/" and nxt == "-":
            block_depth = 1
            i += 2
            continue

        if char == '"':
            in_string = True
            result.append(" ")
            i += 1
            continue

        result.append(char)
        i += 1

    return "".join(result)


def badge(label: str, message: str, color: str) -> dict[str, str | int]:
    return {
        "schemaVersion": 1,
        "label": label,
        "message": message,
        "color": color,
    }


def count_pattern(files: list[Path], pattern: re.Pattern[str]) -> int:
    count = 0
    for path in files:
        source = path.read_text(encoding="utf-8")
        count += len(pattern.findall(strip_comments_and_strings(source)))
    return count


def count_color(count: int, *, warn: int, danger: int) -> str:
    if count == 0:
        return "brightgreen"
    if count < warn:
        return "yellow"
    if count < danger:
        return "orange"
    return "red"


def lean_version(repo_root: Path) -> str:
    toolchain = (repo_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    return toolchain.rsplit(":", maxsplit=1)[-1]


def mathlib_version(repo_root: Path) -> str:
    lakefile = tomllib.loads((repo_root / "lakefile.toml").read_text(encoding="utf-8"))
    for requirement in lakefile.get("require", []):
        if requirement.get("name") == "mathlib":
            return str(requirement.get("rev", "unknown"))
    return "unknown"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, default=Path("badges"))
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    lean_files = tracked_lean_files(repo_root)

    sorry_count = count_pattern(lean_files, SORRY_RE)
    axiom_count = count_pattern(lean_files, AXIOM_RE)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    badges = {
        "sorries.json": badge(
            "sorries", str(sorry_count), count_color(sorry_count, warn=10, danger=50)
        ),
        "axioms.json": badge(
            "axioms", str(axiom_count), "brightgreen" if axiom_count == 0 else "red"
        ),
        "lean.json": badge("Lean", lean_version(repo_root), "blue"),
        "mathlib.json": badge("Mathlib", mathlib_version(repo_root), "blue"),
    }

    for filename, payload in badges.items():
        path = args.output_dir / filename
        path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {path}: {payload['message']}")


if __name__ == "__main__":
    main()
