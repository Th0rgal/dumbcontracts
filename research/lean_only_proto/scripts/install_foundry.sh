#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOCK_FILE="$ROOT/toolchain.lock.json"

VERSION=""
URL=""
EXPECTED_SHA=""

if [ -f "$LOCK_FILE" ]; then
  VERSION=$(python3 - <<PY
import json
with open("$LOCK_FILE", "r", encoding="utf-8") as f:
    data = json.load(f)
print(data["foundry"]["version"])
PY
  )
  URL=$(python3 - <<PY
import json
with open("$LOCK_FILE", "r", encoding="utf-8") as f:
    data = json.load(f)
print(data["foundry"]["url"])
PY
  )
  EXPECTED_SHA=$(python3 - <<PY
import json
with open("$LOCK_FILE", "r", encoding="utf-8") as f:
    data = json.load(f)
print(data["foundry"]["sha256"])
PY
  )
fi

if [ -z "$VERSION" ] || [ -z "$URL" ]; then
  echo "toolchain.lock.json missing foundry entry" >&2
  exit 1
fi

if ! command -v curl >/dev/null 2>&1; then
  echo "curl is required to download foundry" >&2
  exit 1
fi

archive=$(mktemp)
curl -fsSL "$URL" -o "$archive"

if [ -n "$EXPECTED_SHA" ]; then
  actual_sha=$(sha256sum "$archive" | awk '{print $1}')
  if [ "$actual_sha" != "$EXPECTED_SHA" ]; then
    echo "foundry sha256 mismatch: expected $EXPECTED_SHA, got $actual_sha" >&2
    rm -f "$archive"
    exit 1
  fi
fi

# Install forge/cast/anvil to /usr/local/bin
if [ -w /usr/local/bin ]; then
  mkdir -p /usr/local/bin
  tar -xzf "$archive" -C /usr/local/bin
else
  if ! command -v sudo >/dev/null 2>&1; then
    echo "no permission to write /usr/local/bin and sudo not available" >&2
    rm -f "$archive"
    exit 1
  fi
  sudo mkdir -p /usr/local/bin
  sudo tar -xzf "$archive" -C /usr/local/bin
fi
rm -f "$archive"

echo "installed Foundry $VERSION"
forge --version | head -n 1
cast --version | head -n 1
anvil --version | head -n 1
