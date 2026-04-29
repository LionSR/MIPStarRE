#!/usr/bin/env bash
# Shared deploy logic for pushing to the Pages branch.
# Usage: ./scripts/deploy-to-gh-pages.sh [--with-docs] [--badges-dir DIR] [--badges-only] [--ci]
#
# --with-docs   Also deploy API docs from docbuild/.lake/build/doc (fails if missing)
# --badges-dir  Also deploy Shields.io endpoint JSON files from DIR to badges/
# --badges-only Deploy only badges, skipping blueprint, homepage, and docs
# --ci          Use github-actions[bot] as committer instead of local git config
set -euo pipefail

WITH_DOCS=false
BADGES_ONLY=false
CI_MODE=false
BADGES_DIR=""
while [ "$#" -gt 0 ]; do
  case $1 in
    --with-docs) WITH_DOCS=true ;;
    --badges-only) BADGES_ONLY=true ;;
    --badges-dir)
      if [ "$#" -lt 2 ]; then
        echo "::error::--badges-dir requires a directory argument"
        exit 1
      fi
      BADGES_DIR="$2"
      shift
      ;;
    --ci) CI_MODE=true ;;
    *)
      echo "::error::unknown argument: $1"
      exit 1
      ;;
  esac
  shift
done

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

if [ "$CI_MODE" = true ]; then
  REPO_URL="https://x-access-token:${GITHUB_TOKEN:-$GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git"
else
  REPO_URL="$(git -C "$REPO_ROOT" remote get-url origin)"
fi

if [ -n "${PAGES_BRANCH:-}" ]; then
  TARGET_BRANCH="$PAGES_BRANCH"
elif git -C "$REPO_ROOT" ls-remote --exit-code --heads origin github-pages >/dev/null 2>&1; then
  TARGET_BRANCH="github-pages"
else
  TARGET_BRANCH="gh-pages"
fi

echo "==> Cloning $TARGET_BRANCH branch..."
git clone --branch "$TARGET_BRANCH" --single-branch --depth 1 "$REPO_URL" "$WORK_DIR/site"

if [ "$BADGES_ONLY" != true ]; then
  # Update blueprint
  echo "==> Updating blueprint..."
  rm -rf "$WORK_DIR/site/blueprint"
  mkdir -p "$WORK_DIR/site/blueprint"
  cp -r "$REPO_ROOT/blueprint/web/." "$WORK_DIR/site/blueprint/"
  # Copy fresh PDF if available; leave existing PDF untouched otherwise
  if [ -f "$REPO_ROOT/blueprint/print/print.pdf" ]; then
    cp "$REPO_ROOT/blueprint/print/print.pdf" "$WORK_DIR/site/blueprint.pdf"
  else
    echo "==> Skipping blueprint.pdf; blueprint/print/print.pdf not found."
  fi

  # Update homepage (remove all homepage files first, then copy fresh)
  echo "==> Updating homepage..."
  rm -rf "$WORK_DIR/site/_layouts" "$WORK_DIR/site/assets" \
         "$WORK_DIR/site/_config.yml" "$WORK_DIR/site/index.md" \
         "$WORK_DIR/site/404.html" "$WORK_DIR/site/Gemfile"
  cp -r "$REPO_ROOT/home_page/." "$WORK_DIR/site/"
fi

# Update badge endpoint files
if [ -n "$BADGES_DIR" ]; then
  if [ ! -d "$BADGES_DIR" ]; then
    echo "::error::Badge directory not found: $BADGES_DIR"
    exit 1
  fi
  echo "==> Updating badges..."
  rm -rf "$WORK_DIR/site/badges"
  mkdir -p "$WORK_DIR/site/badges"
  cp -r "$BADGES_DIR/." "$WORK_DIR/site/badges/"
fi

# Update API docs (only with --with-docs)
if [ "$WITH_DOCS" = true ]; then
  echo "==> Updating API docs..."
  if [ ! -d "$REPO_ROOT/docbuild/.lake/build/doc" ]; then
    echo "::error::API docs not found at docbuild/.lake/build/doc"
    echo "Run 'cd docbuild && lake build MIPStarRE:docs' first."
    exit 1
  fi
  rm -rf "$WORK_DIR/site/docs"
  cp -r "$REPO_ROOT/docbuild/.lake/build/doc" "$WORK_DIR/site/docs"
elif [ "$BADGES_ONLY" != true ] && [ ! -f "$WORK_DIR/site/docs/index.html" ]; then
  if [ ! -d "$WORK_DIR/site/docs" ] \
      || [ -z "$(find "$WORK_DIR/site/docs" -mindepth 1 -print -quit)" ]; then
    echo "==> Creating API docs placeholder..."
    mkdir -p "$WORK_DIR/site/docs"
    cat > "$WORK_DIR/site/docs/index.html" <<'HTML'
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>MIPStarRE API documentation</title>
  <style>
    body {
      color: #24292f;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      line-height: 1.5;
      margin: 0;
      padding: 3rem 1.5rem;
    }
    main {
      margin: 0 auto;
      max-width: 42rem;
    }
    a {
      color: #0969da;
    }
  </style>
</head>
<body>
  <main>
    <h1>MIPStarRE API documentation</h1>
    <p>
      The generated Lean API documentation has not been deployed yet.
      It is published by the full documentation workflow after docgen succeeds.
    </p>
    <p><a href="../">Return to the project homepage</a></p>
  </main>
</body>
</html>
HTML
  else
    echo "==> Preserving existing API docs directory without index.html."
  fi
fi

# Commit and push
echo "==> Committing and pushing..."
cd "$WORK_DIR/site"
if [ "$CI_MODE" = true ]; then
  git config user.name "github-actions[bot]"
  git config user.email "github-actions[bot]@users.noreply.github.com"
else
  git config user.name "$(git -C "$REPO_ROOT" config user.name || echo 'deploy-script')"
  git config user.email "$(git -C "$REPO_ROOT" config user.email || echo 'deploy@local')"
fi
git add -A
if [ -f blueprint.pdf ]; then
  # `*.pdf` is gitignored repo-wide; force-stage the freshly built blueprint.
  git add -f blueprint.pdf
fi
if git diff --cached --quiet; then
  echo "No changes to deploy."
else
  MSG="Update blueprint"
  [ "$WITH_DOCS" = true ] && MSG="Full docs update"
  [ "$BADGES_ONLY" = true ] && MSG="Update Lean badges"
  git commit -m "$MSG ($(date -u '+%Y-%m-%d %H:%M UTC'))"
  git push origin "$TARGET_BRANCH"
  echo "==> Deployed!"
fi
