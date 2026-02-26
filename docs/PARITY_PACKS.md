# Parity Packs

Issue: [#967](https://github.com/Th0rgal/verity/issues/967)

This document defines the proposed structure for versioned parity packs that target exact `solc` Yul identity for pinned toolchain tuples.

## Status

Partially implemented:
1. CLI selection via `--parity-pack <id>`.
2. Registry + hard validation in `Compiler/ParityPacks.lean`.
3. Ambiguous selection guard (`--parity-pack` cannot be combined with `--backend-profile`).
4. Codegen now runs a typed two-stage patch pipeline:
   - runtime-scoped `ExprRule`/`StmtRule`/`BlockRule` fixpoint pass,
   - followed by `ObjectRule` pass over the full object.
   This keeps deploy rewrites explicit (object rules only) while preserving runtime patch diagnostics.
5. Verbose parity-pack logs now include `metadataMode` alongside the rest of the pinned tuple.
6. Typed `RewriteCtx` scope/phase/iteration/pack metadata is now threaded through patch execution, and rule scope is enforced at application sites.
7. `--parity-pack` now propagates into patch execution context (`PatchPassConfig.packId`), and rules can gate activation with `packAllowlist`.

Not implemented yet:
1. pack-level proof composition checks;
2. identity checker and unsupported manifest workflow.

## Purpose

`solidity-parity` currently provides deterministic shape normalization. Parity packs extend this into a versioned, auditable system:

1. select rules by pinned compiler tuple;
2. apply deterministic canonicalization and rewrites;
3. require proof artifacts for each active rewrite;
4. surface unsupported identity gaps explicitly.

## Proposed Pack Key

`solc-<version>-o<optimizerRuns>-viair-<true|false>-evm-<version>`

Example: `solc-0.8.27-o200-viair-false-evm-shanghai`

## Implemented Pack(s)

1. `solc-0.8.28-o200-viair-false-evm-shanghai`
2. `solc-0.8.28-o999999-viair-true-evm-paris` (Morpho-focused tuple)

## Proposed Pack Contents

1. `compat`: pinned tuple metadata (solc commit/version, flags, EVM version).
2. `rules`: ordered typed rewrite rule IDs.
3. `canonicalization`: deterministic naming/ordering/layout policy.
4. `proofRefs`: theorem references for each rule and pack composition.
5. `unsupported`: explicit list of known non-identity constructs.

## Lifecycle

1. Create pack for pinned tuple.
2. Run identity checker on fixture corpus.
3. Add/adjust rules until diffs are either zero or explicitly unsupported.
4. Prove per-rule semantic preservation and pack composition.
5. Gate in CI and publish support matrix.

## CI Expectations

1. Pack selection must be explicit in build/test command.
2. Identity check artifacts must be uploaded on failure.
3. Pack metadata must be printed in CI logs.
4. Unknown/ambiguous tuple selection must fail hard.

## Related

- [`SOLIDITY_PARITY_PROFILE.md`](SOLIDITY_PARITY_PROFILE.md)
- [`REWRITE_RULES.md`](REWRITE_RULES.md)
- [`IDENTITY_CHECKER.md`](IDENTITY_CHECKER.md)
