# Research Log

Notes on design decisions, problems encountered, and proof techniques discovered during development.

## EDSL design

The core went through two phases:

**Phase 1 (iterations 1-7)**: Built 7 contracts on a `StateM ContractState` monad. Core grew from 58 to 82 lines. Three storage types were added as needed: `Nat -> Uint256` (iteration 1), `Nat -> Address` (iteration 3), `Nat -> Address -> Uint256` for mappings (iteration 6). Each was driven by a concrete example that needed it.

**Phase 2 (verification)**: Replaced `StateM` with a custom `ContractResult` inductive type (`success | revert`) so that `require` guards could be modeled explicitly. This was necessary to prove properties like "mint reverts when caller is not owner." Core grew to 234 lines, mostly from simp lemmas for proof automation and EVM context.

Key decisions:
- `Address := String`, `Uint256` is a dedicated 256-bit modular type to match EVM arithmetic.
- Storage is modeled as functions (`Nat -> Uint256`), not finite maps. Uninitialized slots return 0, matching Solidity.
- `require` returns `ContractResult.revert msg s` on failure, preserving the original state.
- Manual storage slot allocation (slot 0, slot 1, etc). No automatic allocation needed at this scale.
- `onlyOwner` is a regular function called at the top of guarded operations, not a special modifier syntax.

What didn't work:
- `StateM.get` doesn't exist in Lean 4. Use plain `get` in do-notation.
- `Repr` can't derive for function types. Added a manual instance.
- Generic `requireSome` needs `[Inhabited a]`. Made a `Uint256`-specific version instead.
- Marking `.fst`/`.snd` as `@[simp]` caused over-simplification. Added operation-specific simp lemmas instead.

## Arithmetic semantics

All core arithmetic is EVM‑compatible. `Uint256` wraps at `2^256`, so `+`, `-`, `*`, `/`, and `%` match EVM behavior by default.

The project handles overflow safety two ways:
- Counter/Ledger/SimpleToken use bare `+`/`-` (modular arithmetic, EVM‑accurate)
- SafeCounter uses `safeAdd`/`safeSub` from `Stdlib/Math.lean` which return `Option` and revert on overflow/underflow via `requireSomeUint`

`MAX_UINT256` is defined as `2^256 - 1`. The safe arithmetic functions check against this bound.

## Proof techniques

**Full unfolding** is the main approach. Most proofs look like:
```lean
simp only [operation, onlyOwner, isOwner, owner,
  msgSender, getStorageAddr, getStorage, setStorage,
  DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
  Contract.run, ContractResult.snd, ContractResult.fst]
simp [h_owner]
```

This works because the EDSL is shallow: every contract function is a composition of core primitives, and `simp` can unfold the whole chain.

**Private unfold helpers** pre-compute the exact result state when guards pass:
```lean
private theorem increment_unfold (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  (increment.run s) = ContractResult.success () { ... } := by
  simp only [increment, ...]; simp [h_owner]
```
Other theorems rewrite with this helper. But `private theorem` is not accessible from other files, so isolation proofs that live in separate files must repeat the full simp unfolding.

**Boolean equality**: Lean's `BEq` gives `(x == y) = true`, not `x = y`. Use `beq_iff_eq` to convert, or `simp [beq_iff_eq]`.

**Slot preservation**: When proving storage isolation (operation doesn't touch other slots):
```lean
intro slot h_neq h_eq
exact absurd h_eq h_neq
```

**Spec defs without `@[simp]`**: `simp only [my_spec_def]` does nothing if the def isn't marked `@[simp]`. Use `unfold my_spec_def` instead. But `unfold` fails if the goal has `let s' := ...` bindings. Inline the expression directly in the theorem statement.

**List sum reasoning**: `omega` can't handle `List.sum` or `variable * variable` multiplication. Use explicit `Nat.add_assoc`/`Nat.add_comm`/`Nat.add_left_comm` chains. For `List.countOcc`, pre-prove `countOcc_cons_eq`/`countOcc_cons_ne` helpers to avoid `if True then 1 else 0` reduction issues.

**`omega` and `MAX_UINT256`**: `omega` can't see through the `MAX_UINT256` definition. Use `Nat.not_lt.mpr` to convert `h : a + b <= MAX_UINT256` into `not (a + b > MAX_UINT256)`, then `simp`.

**No Mathlib**: `push_neg`, `set`, `ring`, `linarith` are unavailable. Use `by_cases`, explicit witnesses, manual `Nat.*` lemma chains.

## Verification structure

Each contract has:
- `Contracts/X/Impl.lean` -- implementation
- `Contracts/X/Spec.lean` -- what each operation should do (pre/postconditions)
- `Contracts/X/Invariants.lean` -- state properties that should hold across operations
- `Contracts/X/Proofs.lean` -- spec conformance and end-to-end correctness
- `Contracts/X/Proofs/*.lean` -- deeper properties (revert proofs, composition, invariants)

Some contracts have additional proof files:
- `Contracts/SimpleToken/Proofs/Supply.lean` -- supply conservation equations
- `Contracts/SimpleToken/Proofs/Isolation.lean` -- storage isolation across slot types
- `Contracts/Ledger/Proofs/Conservation.lean` -- balance conservation equations
- `Contracts/OwnedCounter/Proofs/Isolation.lean` -- cross-pattern storage isolation

Conservation proofs use `List.countOcc` to account for duplicate addresses in address lists. For `NoDup` lists, transfer preserves the exact sum. For general lists, exact equations with `countOcc` multipliers are proven instead.

## Known limitations

- **Self-transfer**: Transfer theorems require `sender != to`. A self-transfer overwrites the sender's deduction with the recipient's addition. Could be modeled as an identity operation.
- **Supply = sum of balances**: Requires a finite address model. Proven as exact sum equations with `countOcc` accounting, not as a global invariant over all addresses.
- **`ContractResult.fst`**: Returns `default` on revert, requiring `[Inhabited a]`. Proofs that use `.fst` always show the result is `success` first.
- **No events, no gas**: The EDSL models storage and control flow only.
- **No nested mappings**: Can't express `mapping(address => mapping(address => uint256))` for ERC-20 allowances without extending the core.

## What could come next

1. Self-transfer handling (special-case or identity operation)
2. Full `supply = sum(balances)` with a finite address set model
3. ERC-20 allowances (needs `Address -> Address -> Uint256` storage)
4. Gas consumption tracking in `ContractResult`
5. Cross-contract call modeling
