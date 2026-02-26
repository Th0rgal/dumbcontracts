# Yul Identity Checker (Groundwork)

Issue: [#967](https://github.com/Th0rgal/verity/issues/967)

This document defines the target workflow for checking AST-level identity between Verity-generated Yul and `solc`-generated Yul for pinned toolchain tuples.

## Status

Groundwork only. Interface and outputs below are proposed for implementation.

## Goals

1. Compare Yul at AST level (not text-only).
2. Localize mismatches to stable node paths and source/IR origins.
3. Produce machine-readable reports for CI and rule authoring.
4. Distinguish `non-identity` from `unsupported`.

## Proposed CLI Shape

```bash
lake exe verity-compiler check-identity \
  --parity-pack <pack-id> \
  --solc-yul <path> \
  --verity-yul <path> \
  --report <path.json>
```

## Proposed Report Schema

1. `packId`: parity pack used.
2. `targetTuple`: pinned solc/optimizer/evm metadata.
3. `status`: `identical | non_identical | unsupported`.
4. `mismatches[]`: `{ nodePath, kind, lhs, rhs, sourceRef, irRef }`.
5. `unsupported[]`: known unsupported construct IDs.
6. `summary`: counts by mismatch kind.

## CI Integration

1. Run identity checker on pinned fixture corpus.
2. Fail on `non_identical`.
3. Allow `unsupported` only if listed in tracked manifest.
4. Upload JSON reports as workflow artifacts.

## Related

- [`PARITY_PACKS.md`](PARITY_PACKS.md)
- [`REWRITE_RULES.md`](REWRITE_RULES.md)
- [`SOLIDITY_PARITY_PROTOCOL.md`](SOLIDITY_PARITY_PROTOCOL.md)
