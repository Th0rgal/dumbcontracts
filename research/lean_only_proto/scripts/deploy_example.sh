#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

RPC_URL=${RPC_URL:-http://127.0.0.1:8545}
PRIVATE_KEY=${PRIVATE_KEY:-0x59c6995e998f97a5a0044966f094538e1f7adf8c9b0f7c7b9b54d5a2e4e6b0b4}

creation_hex_file="$root/out/example.creation.bin"

if ! command -v cast >/dev/null 2>&1; then
  echo "cast not found. Install Foundry (cast/anvil) to run this script." >&2
  exit 1
fi

if [ ! -f "$creation_hex_file" ]; then
  echo "missing $creation_hex_file. Run ./scripts/end_to_end.sh first." >&2
  exit 1
fi

creation_hex=$(tr -d '\n' < "$creation_hex_file")
creation_hex="0x${creation_hex#0x}"

addr=$(cast send --rpc-url "$RPC_URL" --private-key "$PRIVATE_KEY" --create "$creation_hex" | awk '/contractAddress/ {print $2}')
if [ -z "$addr" ]; then
  echo "deployment failed; no contractAddress in cast output" >&2
  exit 1
fi

echo "deployed: $addr"

encode_call() {
  local selector="$1"
  shift
  python3 - <<PY
import sys
sel = bytes.fromhex("$selector")
args = [int(x, 0) for x in sys.argv[1:]]
calldata = sel + b"".join(a.to_bytes(32, "big") for a in args)
print("0x" + calldata.hex())
PY
}

# selectors from out/example.yul dispatch table
SEL_GET=7eba7ba6
SEL_SET=f2c298be
SEL_ADD=02222aec
SEL_GUARDED=49f583e3

# demo calls
slot=1
value=5

call_get=$(encode_call "$SEL_GET" "$slot")
call_set=$(encode_call "$SEL_SET" "$slot" "$value")
call_add=$(encode_call "$SEL_ADD" "$slot" 3)

cast send --rpc-url "$RPC_URL" --private-key "$PRIVATE_KEY" --to "$addr" --data "$call_set" >/dev/null
cast send --rpc-url "$RPC_URL" --private-key "$PRIVATE_KEY" --to "$addr" --data "$call_add" >/dev/null

result=$(cast call --rpc-url "$RPC_URL" --to "$addr" --data "$call_get")

echo "slot[$slot] = $result"

echo "try guardedAddSlot(delta=0) to see revert:"
call_guarded=$(encode_call "$SEL_GUARDED" "$slot" 0)
if cast send --rpc-url "$RPC_URL" --private-key "$PRIVATE_KEY" --to "$addr" --data "$call_guarded" >/dev/null 2>&1; then
  echo "guardedAddSlot did not revert (unexpected)"
else
  echo "guardedAddSlot reverted (expected)"
fi
