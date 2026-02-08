#!/usr/bin/env bash
set -euo pipefail

VERSION="${1:-0.8.33}"
URL="https://github.com/ethereum/solidity/releases/download/v${VERSION}/solc-static-linux"

if ! command -v curl >/dev/null 2>&1; then
  echo "curl is required to download solc" >&2
  exit 1
fi

if ! curl -fsSLI "$URL" >/dev/null; then
  echo "solc version ${VERSION} not found at ${URL}" >&2
  exit 1
fi

curl -fsSL "$URL" -o /usr/local/bin/solc
chmod +x /usr/local/bin/solc

solc --version | head -n 1
