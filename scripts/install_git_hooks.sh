#!/bin/sh
set -eu

usage() {
  cat <<'EOF'
Usage: scripts/install_git_hooks.sh [--install|--check|--help]

Install or verify the repository-local Git hooks for the current worktree.

  --install  Set core.hooksPath to .githooks. This is the default.
  --check    Verify that core.hooksPath points to .githooks and hooks are executable.
  --help     Show this help text.
EOF
}

MODE="install"
case "${1:-}" in
  ""|--install)
    MODE="install"
    ;;
  --check|--verify)
    MODE="check"
    ;;
  --help|-h)
    usage
    exit 0
    ;;
  *)
    usage >&2
    exit 2
    ;;
esac

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

if [ ! -d .githooks ]; then
  echo "No .githooks directory found at repository root." >&2
  exit 1
fi

check_hook_files() {
  HOOK_STATUS=0
  for HOOK in .githooks/pre-commit .githooks/pre-push
  do
    if [ ! -f "$HOOK" ]; then
      echo "Missing hook file: $HOOK" >&2
      HOOK_STATUS=1
    elif [ ! -x "$HOOK" ]; then
      echo "Hook file is not executable: $HOOK" >&2
      HOOK_STATUS=1
    fi
  done
  return "$HOOK_STATUS"
}

check_hooks_installed() {
  INSTALL_STATUS=0
  CURRENT_HOOKS_PATH="$(git config --get core.hooksPath || true)"
  case "$CURRENT_HOOKS_PATH" in
    .githooks|"$ROOT/.githooks")
      ;;
    "")
      echo "core.hooksPath is not set for this worktree." >&2
      INSTALL_STATUS=1
      ;;
    *)
      echo "core.hooksPath is '$CURRENT_HOOKS_PATH', not .githooks." >&2
      INSTALL_STATUS=1
      ;;
  esac

  if ! check_hook_files; then
    INSTALL_STATUS=1
  fi

  if [ "$INSTALL_STATUS" -eq 0 ]; then
    echo "MIPStarRE Git hooks are installed for this worktree."
    echo "core.hooksPath=$CURRENT_HOOKS_PATH"
  else
    echo "Run scripts/install_git_hooks.sh to install the repository hooks." >&2
  fi
  return "$INSTALL_STATUS"
}

if [ "$MODE" = "check" ]; then
  check_hooks_installed
  exit $?
fi

chmod +x .githooks/pre-commit .githooks/pre-push
git config core.hooksPath .githooks

echo "Installed MIPStarRE Git hooks by setting core.hooksPath to .githooks."
echo "Verify with scripts/install_git_hooks.sh --check."
echo "Set MIPSTARRE_SKIP_HOOKS=1 for a one-off bypass."
echo "Set MIPSTARRE_HOOK_FULL=1 before git push to run the full local gate."
