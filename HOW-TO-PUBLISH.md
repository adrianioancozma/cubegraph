# How to Publish — Sync & Push Workflow

## Quick (one command)

```bash
cd /home/adrian/dev/adrian/p-vs-np/PUBLISH
bash sync.sh && git add -A && git commit -m "update: $(date +%Y-%m-%d)" && git push origin main
```

## Step by step

### 1. Sync formal/ from working tree to PUBLISH/

```bash
cd /home/adrian/dev/adrian/p-vs-np/PUBLISH
bash sync.sh
```

This runs `rsync` from `../formal/` to `PUBLISH/formal/`, excluding:
- `.lake/`, `lake-packages/` (build artifacts)
- `README.md` (PUBLISH has its own — NOT overwritten)
- `TODO.md`, `AUDIT.md`, `AXIOM12-ELIMINATED.md` (internal docs)

### 2. Review changes

```bash
git status
git diff --stat
```

### 3. Commit and push

```bash
git add -A
git commit -m "update: $(date +%Y-%m-%d) — description"
git push origin main
```

## Important rules

- **README.md** in PUBLISH root is SEPARATE from formal/README.md
  - sync.sh does NOT overwrite it (excluded in rsync)
  - Edit PUBLISH/README.md directly for public-facing content
  - formal/README.md is internal (and has been deleted)

- **Never push .lake/** — .gitignore handles this

- **Build before publishing**:
  ```bash
  cd /home/adrian/dev/adrian/p-vs-np/formal
  lake build   # must pass with 0 errors
  ```

- **Check axiom count**:
  ```bash
  grep -rc "^axiom " formal/CubeGraph/ --include="*.lean" | awk -F: '{s+=$2} END {print s}'
  ```
  Update README.md if the count changed.

## Repository

- GitHub: https://github.com/adrianioancozma/cubegraph
- Branch: main
- License: Apache 2.0
