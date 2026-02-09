#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <input.evm> <output.hex>" >&2
  exit 2
fi

python3 "$root/tools/evm_assemble.py" "$1" "$2"
