#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)

cd "$root"

./scripts/verify_toolchain.sh
./scripts/gen_yul.sh
./scripts/gen_selectors.sh
./scripts/check_yul.sh out/example.yul
./scripts/compile_asm.sh out/example.yul out/example.asm
./scripts/summarize_asm.sh out/example.asm out/example.asm.summary
./scripts/compile_yul.sh out/example.yul out/example.bin
./scripts/make_creation.sh out/example.bin out/example.creation.bin
./scripts/assemble_evm.sh out/example.evm out/example.evm.hex
./scripts/compare_evm_asm.sh out/example.evm out/example.asm out/example.evm.compare.md
./scripts/compare_bytecode.sh out/example.evm.hex out/example.bin out/example.evm.bytecode.md
./scripts/check_yul.sh out/health.yul
./scripts/compile_asm.sh out/health.yul out/health.asm
./scripts/summarize_asm.sh out/health.asm out/health.asm.summary
./scripts/compile_yul.sh out/health.yul out/health.bin
./scripts/make_creation.sh out/health.bin out/health.creation.bin
./scripts/gen_provenance.sh out/provenance.json \
  out/example.yul \
  out/example.asm \
  out/example.asm.summary \
  out/example.bin \
  out/example.creation.bin \
  out/example.evm \
  out/example.evm.hex \
  out/example.evm.compare.md \
  out/example.evm.bytecode.md \
  out/health.yul \
  out/health.asm \
  out/health.asm.summary \
  out/health.bin \
  out/health.creation.bin \
  out/selectors.json \
  out/selectors.md
