#!/usr/bin/env bash
set -euo pipefail

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
  echo "Usage: $0 <input.asm> [output.summary]" >&2
  exit 2
fi

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

input_path="$1"
output_path="${2:-}"

if [ -z "$output_path" ]; then
  python3 "$root/tools/asm_summarize.py" "$input_path"
else
  python3 "$root/tools/asm_summarize.py" "$input_path" "$output_path"
fi
