#!/usr/bin/env bash
set -euxo pipefail

export PATH="$HOME/.elan/bin:$PATH"

lake update || true
lake exe cache get || true
