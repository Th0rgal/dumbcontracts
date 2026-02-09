#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -lt 1 ]; then
  echo "usage: gen_provenance.sh <output.json> [artifact ...]" >&2
  exit 2
fi

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

python3 "$root/tools/gen_provenance.py" "$@"
