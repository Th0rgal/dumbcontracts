#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 3 ]; then
  echo "usage: compare_bytecode.sh <direct.hex> <solc.hex> <output.md>" >&2
  exit 2
fi

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

python3 "$root/tools/compare_bytecode.py" "$@"
