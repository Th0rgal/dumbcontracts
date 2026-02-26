# Rewrite Rules (Groundwork)

Issue: [#967](https://github.com/Th0rgal/verity/issues/967)

This document defines the target authoring model for proof-carrying Yul subtree rewrites.

## Status

Partially implemented:
1. `ExprRule` (as `ExprPatchRule`) is active in the deterministic patch engine.
2. `StmtRule` (as `StmtPatchRule`) is now supported in the patch engine with the same fail-closed metadata gate.
3. `BlockRule` (as `BlockPatchRule`) is now supported in the patch engine with the same fail-closed metadata gate.
4. `ObjectRule` (as `ObjectPatchRule`) is now supported in the patch engine with the same fail-closed metadata gate.

Not implemented yet:
1. typed `RewriteCtx` plumbing.
2. mandatory proof checking beyond metadata linkage.

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

## Rewrite Context (Planned)

Rules should receive a typed `RewriteCtx` with:

1. symbol table and helper registry;
2. selector map / ABI layout facts;
3. stage metadata (deploy/runtime, pass index, pack ID);
4. canonicalization settings.

## Safety Rules

1. Rules without `proofRef` are not activatable.
2. Out-of-scope rewrite attempts must fail.
3. Overlapping rules must be conflict-checked.
4. Pack composition must have a theorem proving semantics preservation.

## Testing Expectations

1. Unit tests per rule (positive/negative match cases).
2. Determinism tests (repeatability).
3. Blast-radius tests (no unrelated subtree mutation).
4. Differential execution backstop between pre/post rewrite artifacts.

## Related

- [`PARITY_PACKS.md`](PARITY_PACKS.md)
- [`IDENTITY_CHECKER.md`](IDENTITY_CHECKER.md)
