#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 3 ]; then
  echo "Usage: compare_evm_asm.sh <direct.evm> <solc.asm> <output.md>" >&2
  exit 2
fi

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

python3 "$root/tools/compare_evm_asm.py" "$1" "$2" "$3"
