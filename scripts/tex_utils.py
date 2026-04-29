"""Shared helpers for parsing active TeX source lines."""

from __future__ import annotations


def strip_tex_comment(line: str) -> str:
    r"""Return the active TeX prefix before the first unescaped ``%``.

    TeX comments start at an unescaped percent sign. A percent sign preceded
    by an odd-length run of backslashes is the literal ``\%`` token and must
    not truncate the line; an even-length run leaves the ``%`` unescaped.
    """

    for idx, char in enumerate(line):
        if char != "%":
            continue
        backslashes = 0
        j = idx - 1
        while j >= 0 and line[j] == "\\":
            backslashes += 1
            j -= 1
        if backslashes % 2 == 0:
            return line[:idx]
    return line
