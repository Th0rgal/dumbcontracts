#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOCK_FILE="$ROOT/toolchain.lock.json"

VERSION="${1:-}"
EXPECTED_SHA=""
URL=""

if [ -z "$VERSION" ] && [ -f "$LOCK_FILE" ]; then
  VERSION=$(python3 - <<PY
import json
with open("$LOCK_FILE", "r", encoding="utf-8") as f:
    data = json.load(f)
print(data["solc"]["version"])
PY
)
  URL=$(python3 - <<PY
import json
with open("$LOCK_FILE", "r", encoding="utf-8") as f:
    data = json.load(f)
print(data["solc"]["url"])
PY
)
  EXPECTED_SHA=$(python3 - <<PY
import json
with open("$LOCK_FILE", "r", encoding="utf-8") as f:
    data = json.load(f)
print(data["solc"]["sha256"])
PY
)
fi

if [ -z "$VERSION" ]; then
  VERSION="0.8.33"
fi

if [ -z "$URL" ]; then
  URL="https://github.com/ethereum/solidity/releases/download/v${VERSION}/solc-static-linux"
fi

if ! command -v curl >/dev/null 2>&1; then
  echo "curl is required to download solc" >&2
  exit 1
fi

if ! curl -fsSLI "$URL" >/dev/null; then
  echo "solc version ${VERSION} not found at ${URL}" >&2
  exit 1
fi

tmp=$(mktemp)
curl -fsSL "$URL" -o "$tmp"
if [ -n "$EXPECTED_SHA" ]; then
  actual_sha=$(sha256sum "$tmp" | awk '{print $1}')
  if [ "$actual_sha" != "$EXPECTED_SHA" ]; then
    echo "solc sha256 mismatch: expected $EXPECTED_SHA, got $actual_sha" >&2
    rm -f "$tmp"
    exit 1
  fi
fi

install -m 0755 "$tmp" /usr/local/bin/solc
rm -f "$tmp"
chmod +x /usr/local/bin/solc

solc --version | head -n 1
