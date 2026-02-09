#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

input="$root/DumbContracts/Compiler.lean"
json_out="$root/out/selectors.json"
md_out="$root/out/selectors.md"

python3 "$root/tools/gen_selectors.py" --in "$input" --json "$json_out" --md "$md_out"
