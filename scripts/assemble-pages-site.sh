#!/usr/bin/env bash
# Assemble the GitHub Pages site tree from downloaded component artifacts.
# Usage: assemble-pages-site.sh COMPONENTS_DIR OUT_DIR
#
# COMPONENTS_DIR may contain:
#   site-blueprint/  Jekyll-built homepage, blueprint web, and PDF (required)
#   site-docs/       doc-gen4 API documentation (required)
#   site-badges/     Shields.io endpoint JSON (required)
set -euo pipefail

if [ "$#" -ne 2 ]; then
  echo "Usage: $0 COMPONENTS_DIR OUT_DIR" >&2
  exit 2
fi

COMPONENTS="$1"
OUT="$2"

if [ ! -d "$COMPONENTS/site-blueprint" ]; then
  echo "::error::site-blueprint component missing — cannot assemble site"
  exit 1
fi
if [ ! -d "$COMPONENTS/site-blueprint/homepage" ]; then
  echo "::error::site-blueprint/homepage missing — cannot assemble site"
  exit 1
fi
if [ ! -d "$COMPONENTS/site-blueprint/blueprint" ]; then
  echo "::error::site-blueprint/blueprint missing — cannot assemble site"
  exit 1
fi
if [ ! -f "$COMPONENTS/site-blueprint/blueprint.pdf" ]; then
  echo "::error::site-blueprint/blueprint.pdf missing — cannot assemble site"
  exit 1
fi
if [ ! -d "$COMPONENTS/site-docs/docs" ]; then
  echo "::error::site-docs component missing — refusing to remove deployed API docs"
  exit 1
fi
if [ ! -d "$COMPONENTS/site-badges" ] \
    || ! find "$COMPONENTS/site-badges" -maxdepth 1 -name '*.json' -print -quit | grep -q .; then
  echo "::error::site-badges component missing — refusing to remove deployed badge endpoints"
  exit 1
fi

rm -rf "$OUT"
mkdir -p "$OUT"

echo "==> Homepage..."
cp -r "$COMPONENTS/site-blueprint/homepage/." "$OUT/"
# Live badge values come from the separately refreshed badge component.
rm -rf "$OUT/badges"

echo "==> Blueprint..."
mkdir -p "$OUT/blueprint"
cp -r "$COMPONENTS/site-blueprint/blueprint/." "$OUT/blueprint/"
cp "$COMPONENTS/site-blueprint/blueprint.pdf" "$OUT/blueprint.pdf"

echo "==> API docs..."
cp -r "$COMPONENTS/site-docs/docs" "$OUT/docs"

if [ -d "$COMPONENTS/site-docs/paper-gaps" ]; then
  echo "==> Paper-gap PDFs..."
  cp -r "$COMPONENTS/site-docs/paper-gaps" "$OUT/paper-gaps"
fi

echo "==> Badges..."
mkdir -p "$OUT/badges"
cp "$COMPONENTS/site-badges"/*.json "$OUT/badges/"

echo "==> Site assembled at $OUT"
du -sh "$OUT"
