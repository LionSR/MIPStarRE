#!/usr/bin/env bash
# Shared deploy logic for pushing to the Pages branch.
# Usage: ./scripts/deploy-to-gh-pages.sh [--with-docs] [--ci]
#
# --with-docs   Also deploy API docs from docbuild/.lake/build/doc (fails if missing)
# --ci          Use github-actions[bot] as committer instead of local git config
set -euo pipefail

WITH_DOCS=false
CI_MODE=false
for arg in "$@"; do
  case $arg in
    --with-docs) WITH_DOCS=true ;;
    --ci) CI_MODE=true ;;
  esac
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

# Update blueprint
echo "==> Updating blueprint..."
rm -rf "$WORK_DIR/site/blueprint"
mkdir -p "$WORK_DIR/site/blueprint"
cp -r "$REPO_ROOT/blueprint/web/." "$WORK_DIR/site/blueprint/"
# Copy fresh PDF if available; leave existing PDF untouched otherwise
if [ -f "$REPO_ROOT/blueprint/print/print.pdf" ]; then
  cp "$REPO_ROOT/blueprint/print/print.pdf" "$WORK_DIR/site/blueprint.pdf"
fi

# Update homepage (remove all homepage files first, then copy fresh)
echo "==> Updating homepage..."
rm -rf "$WORK_DIR/site/_layouts" "$WORK_DIR/site/assets" \
       "$WORK_DIR/site/_config.yml" "$WORK_DIR/site/index.md" \
       "$WORK_DIR/site/404.html" "$WORK_DIR/site/Gemfile"
cp -r "$REPO_ROOT/home_page/." "$WORK_DIR/site/"

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
if git diff --cached --quiet; then
  echo "No changes to deploy."
else
  MSG="Update blueprint"
  [ "$WITH_DOCS" = true ] && MSG="Full docs update"
  git commit -m "$MSG ($(date -u '+%Y-%m-%d %H:%M UTC'))"
  git push origin "$TARGET_BRANCH"
  echo "==> Deployed!"
fi
