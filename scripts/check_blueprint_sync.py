#!/usr/bin/env python3
"""Backward-compatible wrapper for the blueprint \\leanok axiom checker.

Legacy callers (e.g. older CI invocations) ran ``check_blueprint_sync.py``
without a ``--ci`` flag and relied on the exit code to surface failures.  The
new checker only returns non-zero with ``--ci``, so we inject that flag here
whenever it was not passed explicitly, preserving the original failing-exit
semantics for legacy callers.
"""

from __future__ import annotations

import sys

from blueprint_leanok_axioms import main


if __name__ == "__main__":
    if "--ci" not in sys.argv[1:]:
        sys.argv.append("--ci")
    raise SystemExit(main())
