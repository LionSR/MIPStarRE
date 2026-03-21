#!/usr/bin/env bash
set -euxo pipefail

# Install basic tools if missing
if ! command -v curl >/dev/null 2>&1; then
  apt-get update
  apt-get install -y curl git zstd unzip build-essential ca-certificates
fi

# Install elan if missing
if ! command -v elan >/dev/null 2>&1; then
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
fi

# Make Lean tools available to later shells
grep -qxF 'export PATH="$HOME/.elan/bin:$PATH"' "$HOME/.bashrc" 2>/dev/null || \
  echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.bashrc"
export PATH="$HOME/.elan/bin:$PATH"

# Show versions for debugging
elan --version || true
lean --version || true
lake --version || true

# Sync dependencies
if [ -f "lean-toolchain" ]; then
  lake update || true
fi

# Fetch mathlib cache when available
lake exe cache get || true

# Warm the build cache
lake build || true
