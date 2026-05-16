#!/usr/bin/env python3
"""Small scanner primitives for Lean declaration headers."""

from __future__ import annotations

from pathlib import Path


OPEN_TO_CLOSE = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
CLOSE_TO_OPEN = {value: key for key, value in OPEN_TO_CLOSE.items()}


def line_number(text: str, offset: int) -> int:
    """Return the one-based line number of ``offset`` in ``text``."""

    return text.count("\n", 0, offset) + 1


def ldt_lean_files(root: Path) -> list[Path]:
    """Return Lean files in the active LDT tree."""

    base = root / "MIPStarRE" / "LDT"
    if not base.exists():
        return []
    return sorted(path for path in base.rglob("*.lean") if path.is_file())


def advance_depth(ch: str, stack: list[str]) -> None:
    """Update a delimiter stack with one Lean header character."""

    if ch in OPEN_TO_CLOSE:
        stack.append(ch)
    elif ch in CLOSE_TO_OPEN and stack and stack[-1] == CLOSE_TO_OPEN[ch]:
        stack.pop()


def identifier_char(ch: str) -> bool:
    """Return whether ``ch`` can continue a Lean identifier-like token."""

    return ch.isalnum() or ch in "_?'"


def starts_keyword(text: str, pos: int, keyword: str) -> bool:
    """Return whether ``keyword`` starts at ``pos`` as a standalone token."""

    if not text.startswith(keyword, pos):
        return False
    before_ok = pos == 0 or not identifier_char(text[pos - 1])
    after = pos + len(keyword)
    after_ok = after >= len(text) or not identifier_char(text[after])
    return before_ok and after_ok
