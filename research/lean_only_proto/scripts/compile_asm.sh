#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <yul-file> [out-asm-file]" >&2
  exit 2
fi

if ! command -v solc >/dev/null 2>&1; then
  echo "solc not found. Run ./scripts/install_solc.sh or install Solidity compiler and re-run." >&2
  exit 1
fi

input="$1"
out_asm="${2:-${input%.yul}.asm}"

EVM_VERSION="${EVM_VERSION:-shanghai}"
solc --strict-assembly --evm-version "$EVM_VERSION" --asm "$input" > "$out_asm"
echo "wrote $out_asm"
