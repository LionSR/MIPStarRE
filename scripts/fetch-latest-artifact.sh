#!/usr/bin/env bash
# Download the newest non-expired GitHub Actions artifact with a given name.
# Usage: fetch-latest-artifact.sh NAME DEST_DIR
#
# Exits successfully with a warning, without creating DEST_DIR, when no artifact
# is available. Requires GH_TOKEN with actions:read on GITHUB_REPOSITORY.
set -euo pipefail

if [ "$#" -ne 2 ]; then
  echo "Usage: $0 NAME DEST_DIR" >&2
  exit 2
fi

NAME="$1"
DEST="$2"
REPO="${GITHUB_REPOSITORY:?GITHUB_REPOSITORY must be set}"

artifact_id="$(gh api "repos/${REPO}/actions/artifacts?name=${NAME}&per_page=100" \
  | jq -r --arg name "$NAME" \
      '[.artifacts[] | select(.name == $name and (.expired | not))]
       | sort_by(.created_at) | last | .id // empty')"

if [ -z "$artifact_id" ]; then
  echo "::warning::No non-expired artifact named '${NAME}' found"
  exit 0
fi

echo "==> Downloading ${NAME} artifact ${artifact_id}..."
tmp_zip="$(mktemp)"
trap 'rm -f "$tmp_zip"' EXIT
gh api "repos/${REPO}/actions/artifacts/${artifact_id}/zip" > "$tmp_zip"
mkdir -p "$DEST"
unzip -q "$tmp_zip" -d "$DEST"
echo "==> Extracted ${NAME} to ${DEST}"
