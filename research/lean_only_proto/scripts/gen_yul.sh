#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if ! command -v lean >/dev/null 2>&1; then
  if [ -x /opt/lean-4.27.0/bin/lean ]; then
    export PATH="/opt/lean-4.27.0/bin:$PATH"
  else
    echo "lean not found. Install via elan or provide /opt/lean-4.27.0/bin/lean." >&2
    exit 1
  fi
fi

cd "$ROOT"

lake build
lake exe dumbcontracts
