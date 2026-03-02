#!/usr/bin/env bash
set -euo pipefail

# Vercel ignoreCommand contract:
# - exit 0 => skip build/deployment
# - exit 1 => continue build/deployment

# Not a PR deployment: continue building.
if [ -z "${VERCEL_GIT_PULL_REQUEST_ID:-}" ]; then
  echo "Not a PR deployment; continuing build"
  exit 1
fi

# If no GitHub token is configured, fail open and continue build.
if [ -z "${GITHUB_TOKEN:-}" ]; then
  echo "GITHUB_TOKEN missing; continuing build"
  exit 1
fi

owner="${VERCEL_GIT_REPO_OWNER:-}"
repo="${VERCEL_GIT_REPO_SLUG:-}"
pr="${VERCEL_GIT_PULL_REQUEST_ID:-}"

if [ -z "$owner" ] || [ -z "$repo" ]; then
  echo "Repository metadata missing; continuing build"
  exit 1
fi

api_url="https://api.github.com/repos/${owner}/${repo}/pulls/${pr}"

response="$(curl -fsSL \
  -H "Authorization: Bearer ${GITHUB_TOKEN}" \
  -H "Accept: application/vnd.github+json" \
  "$api_url")"

is_draft="$(printf '%s' "$response" | python3 -c 'import json,sys; print(str(json.load(sys.stdin).get("draft", False)).lower())')"

if [ "$is_draft" = "true" ]; then
  echo "Draft PR detected; skipping Vercel build"
  exit 0
fi

echo "PR is ready for review; continuing build"
exit 1
