#!/bin/bash
# Sync local formal/ to PUBLISH/ and push to GitHub
# Usage: cd PUBLISH && bash sync.sh

set -e

PROJ_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PUBLISH_DIR="$(cd "$(dirname "$0")" && pwd)"

echo "Syncing from $PROJ_ROOT/formal/ to $PUBLISH_DIR/formal/"

rsync -av --delete \
  --exclude='.lake' \
  --exclude='lake-packages' \
  --exclude='.DS_Store' \
  --exclude='.gitignore' \
  --exclude='.github' \
  --exclude='AUDIT.md' \
  --exclude='AUDIT2.md' \
  --exclude='FORMALIZATION-PLAN.md' \
  --exclude='TODO.md' \
  --exclude='README.md' \
  --exclude='InteractiveKAC.lean' \
  "$PROJ_ROOT/formal/" "$PUBLISH_DIR/formal/"

cd "$PUBLISH_DIR"

# Show what changed
git status

echo ""
echo "To commit and push:"
echo "  cd $PUBLISH_DIR"
echo "  git add -A"
echo '  git commit -m "update: $(date +%Y-%m-%d)"'
echo "  git push origin main"
