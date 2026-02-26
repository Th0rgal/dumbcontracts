# Rewrite Rules (Groundwork)

Issue: [#967](https://github.com/Th0rgal/verity/issues/967)

This document defines the target authoring model for proof-carrying Yul subtree rewrites.

## Status

Partially implemented:
1. `ExprRule` (as `ExprPatchRule`) is active in the deterministic patch engine.
2. `StmtRule` (as `StmtPatchRule`) is now supported in the patch engine with the same fail-closed metadata gate.
3. `BlockRule` (as `BlockPatchRule`) is now supported in the patch engine with the same fail-closed metadata gate.
4. `ObjectRule` (as `ObjectPatchRule`) is now supported in the patch engine with the same fail-closed metadata gate.
5. Codegen now runs a two-stage typed rewrite pipeline:
   - runtime-scoped fixpoint pass for `ExprRule`/`StmtRule`/`BlockRule`;
   - object pass for `ObjectRule`.
   Foundation packs for `StmtRule`/`BlockRule`/`ObjectRule` are wired but currently empty.
6. Rule activation now supports pack-scoped allowlists (`packAllowlist`) checked against `RewriteCtx.packId`.
7. Patch execution now supports activation-time proof registry enforcement via `PatchPassConfig.requiredProofRefs`.
   In compiler codegen, this defaults to the selected rewrite bundle proof allowlist, so rules with unregistered `proofId` fail closed even if metadata is non-empty.
8. Rewrite bundles are now explicit and versioned (`foundation`, `solc-compat-v0`), with bundle selection propagated by `PatchPassConfig.rewriteBundleId`.
   Object rules are now applied sequentially in deterministic priority order within each object-pass iteration (instead of first-match only), enabling chained compat transforms in one iteration.
   `solc-compat-v0` now includes compatibility-only object rules:
   - `solc-compat-canonicalize-internal-fun-names`: canonicalizes `internal__*` helper names to `fun_*` and rewrites in-object call sites deterministically.
   - `solc-compat-inline-dispatch-wrapper-calls`: inlines runtime dispatch case bodies of the form `fun_*()` to the referenced top-level zero-arity helper body.
   - `solc-compat-inline-mapping-slot-calls`: inlines runtime `mappingSlot(baseSlot, key)` expression calls by materializing helper-equivalent scratch writes (`mstore(512, key)`, `mstore(544, baseSlot)`) plus `keccak256(512, 64)` into fresh collision-safe temporaries.
   - `solc-compat-inline-keccak-market-params-calls`: inlines direct runtime `keccakMarketParams(...)` helper calls into explicit `mstore`/`keccak256` sequences.
   - `solc-compat-dedupe-equivalent-helpers`: deduplicates structurally equivalent top-level helper defs and rewrites call sites to the retained canonical helper.
   - `solc-compat-prune-unreachable-helpers`: prunes unreachable top-level helper defs deterministically.
   `solc-compat-outline-dispatch-helpers` remains implemented and tested, but is not activated in `solc-compat-v0` by default because broad dispatch outlining introduces non-`solc` helper families on current targets.
9. Parity packs now require explicit pack-level proof composition metadata (`compositionProofRef`) and proof registry coverage (`requiredProofRefs`) against the selected rewrite bundle before `--parity-pack` selection is accepted.

## Rule Kinds

1. `ExprRule`: expression subtree rewrites.
2. `StmtRule`: statement-level rewrites.
3. `BlockRule`: block structure rewrites (ordering/grouping/scoping).
4. `ObjectRule`: deploy/runtime object-level rewrites.

## Required Rule Fields

1. `id`: stable rule identifier.
2. `scope`: where the rule may run (`runtime`, `deploy`, `dispatcher`, `abi`, `helper(name)`).
3. `matcher`: typed precondition over target subtree plus context.
4. `rewrite`: transformed subtree.
5. `proofRef`: theorem establishing semantic preservation under matcher preconditions.
6. `deterministic`: explicit guarantee that output is stable.

## Rewrite Context (Implemented Foundation)

Rules now receive a typed `RewriteCtx` with:

1. stage scope (`runtime`, `deploy`, `object`);
2. pass metadata (phase, iteration, pack ID).

Still planned:
1. symbol table and helper registry;
2. selector map / ABI layout facts;
3. canonicalization settings.

## Safety Rules

1. Rules without `proofRef` are not activatable.
2. Rules whose `proofRef` is not in the active proof registry are not activatable.
3. Out-of-scope rewrite attempts fail closed via scope-checked `RewriteCtx`.
4. Overlapping rules must be conflict-checked.
5. Pack composition must have a theorem proving semantics preservation.

## Testing Expectations

1. Unit tests per rule (positive/negative match cases).
2. Determinism tests (repeatability).
3. Blast-radius tests (no unrelated subtree mutation).
4. Differential execution backstop between pre/post rewrite artifacts.

## Related

- [`PARITY_PACKS.md`](PARITY_PACKS.md)
- [`IDENTITY_CHECKER.md`](IDENTITY_CHECKER.md)
- [`SOLIDITY_PARITY_PROTOCOL.md`](SOLIDITY_PARITY_PROTOCOL.md)
