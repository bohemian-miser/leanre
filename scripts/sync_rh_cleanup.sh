#!/usr/bin/env bash
# Sync local `data/rh_cleanup` mirror against upstream `leanprover-community/riemann-hypothesis`,
# push fast-forwarded `main` to `origin` (`bohemian-miser/riemann-hypothesis`), and regenerate
# `outputs/slop_rh_cleanup.json` + `outputs/rh_cleanup_diff.json` with live open-PR cold gaps.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CLEANUP_DIR="${REPO_ROOT}/data/rh_cleanup"
ORIG_SLOP="${REPO_ROOT}/outputs/slop_rh_orig_src.json"
CLEANUP_SLOP="${REPO_ROOT}/outputs/slop_rh_cleanup.json"
DIFF_OUT="${REPO_ROOT}/outputs/rh_cleanup_diff.json"
GH_REPO="leanprover-community/riemann-hypothesis"

if [[ ! -d "${CLEANUP_DIR}/.git" && ! -f "${CLEANUP_DIR}/.git" ]]; then
  echo "error: missing cleanup checkout at data/rh_cleanup" >&2
  exit 1
fi

OLD_SHA="$(git -C "${CLEANUP_DIR}" rev-parse HEAD)"

if git -C "${CLEANUP_DIR}" remote get-url upstream >/dev/null 2>&1; then
  git -C "${CLEANUP_DIR}" fetch upstream main
  git -C "${CLEANUP_DIR}" merge --ff-only upstream/main
else
  git -C "${CLEANUP_DIR}" fetch origin main
  git -C "${CLEANUP_DIR}" merge --ff-only origin/main
fi

NEW_SHA="$(git -C "${CLEANUP_DIR}" rev-parse HEAD)"

if git -C "${CLEANUP_DIR}" remote get-url origin >/dev/null 2>&1; then
  ORIGIN_URL="$(git -C "${CLEANUP_DIR}" remote get-url origin)"
  if [[ "${ORIGIN_URL}" == *"bohemian-miser/riemann-hypothesis"* ]]; then
    git -C "${CLEANUP_DIR}" push origin main
  fi
fi

if [[ ! -f "${ORIG_SLOP}" ]]; then
  python3 "${REPO_ROOT}/leanre/leanre.py" slop scan "${REPO_ROOT}/data/rh_mirror/src" \
    --slug riemann-hypothesis \
    --out "${ORIG_SLOP}"
fi

python3 "${REPO_ROOT}/leanre/leanre.py" slop scan "${CLEANUP_DIR}/src" \
  --slug riemann-hypothesis-cleanup \
  --out "${CLEANUP_SLOP}"

python3 "${REPO_ROOT}/leanre/leanre.py" slop diff "${ORIG_SLOP}" "${CLEANUP_SLOP}" \
  --gh-repo "${GH_REPO}" \
  --label-before "Original archive (40e56bab)" \
  --label-after "Community cleanup (HEAD)" \
  --out "${DIFF_OUT}"

if [[ "${OLD_SHA}" != "${NEW_SHA}" ]]; then
  echo "UPDATED: rh_cleanup advanced ${OLD_SHA:0:12} -> ${NEW_SHA:0:12}; rebuild and republish recommended."
else
  echo "UP_TO_DATE: rh_cleanup unchanged at ${NEW_SHA:0:12}; slop diff and live cold gaps refreshed."
fi
