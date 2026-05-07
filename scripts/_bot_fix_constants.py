"""Shared constants for bot auto-fix loops.

The canonical source of truth is
``.github/actions/bot-fix-guard/action.yml`` — its regex
``\\[(claude|codex)-(auto|review)-fix\\]`` and its default ``max-iterations: 5``
gate every PR's auto-fix loop. The constants here exist so offline audits
(``scripts/audit_drift.py``, ``scripts/audit_ci_waste.py``) match what the
guard actually enforces, including Codex-driven loops.

If you change the prefix list or the cap here, change ``bot-fix-guard``
too — and vice versa.
"""

from __future__ import annotations

import re

# Mirrors ``inputs.max-iterations`` default in
# ``.github/actions/bot-fix-guard/action.yml``.
MAX_BOT_FIX_ITERATIONS = 5

# Mirrors the regex on line 34 of ``bot-fix-guard/action.yml``.
BOT_FIX_PREFIXES: tuple[str, ...] = (
    "[claude-auto-fix]",
    "[claude-review-fix]",
    "[codex-auto-fix]",
    "[codex-review-fix]",
)

BOT_FIX_PREFIX_RE = re.compile(r"^\[(claude|codex)-(auto|review)-fix\]")
