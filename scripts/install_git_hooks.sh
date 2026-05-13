#!/bin/sh
set -eu

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

if [ ! -d .githooks ]; then
  echo "No .githooks directory found at repository root." >&2
  exit 1
fi

chmod +x .githooks/pre-commit .githooks/pre-push
git config core.hooksPath .githooks

echo "Installed MIPStarRE Git hooks by setting core.hooksPath to .githooks."
echo "Set MIPSTARRE_SKIP_HOOKS=1 for a one-off bypass."
echo "Set MIPSTARRE_HOOK_FULL=1 before git push to run the full local gate."
