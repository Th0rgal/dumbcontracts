#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <yul-file> [out-bin-file]" >&2
  exit 2
fi

if ! command -v solc >/dev/null 2>&1; then
  echo "solc not found. Run ./scripts/install_solc.sh or install Solidity compiler and re-run." >&2
  exit 1
fi

input="$1"
out_bin="${2:-${input%.yul}.bin}"
EVM_VERSION="${EVM_VERSION:-shanghai}"

bin=$(
  solc --strict-assembly --evm-version "$EVM_VERSION" --bin "$input" | awk '
    /Binary representation:/ {found=1; next}
    found && NF {print $0; exit}
  '
)

if [[ -z "$bin" ]]; then
  echo "failed to extract bytecode from solc output" >&2
  exit 1
fi

echo "$bin" > "$out_bin"
echo "wrote $out_bin"
