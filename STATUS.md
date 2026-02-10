# Dumb Contracts Research Status

## Current State: 152 Theorems, 7/7 Contracts Verified (2026-02-10)

### Summary
**Full Verification Achieved**: All 152 theorems proven with zero `sorry`, zero axioms, zero errors. Guard modeling via `ContractResult` type enables complete verification of `require`-guarded operations.

All 7 contract patterns verified at 100%:
- SimpleStorage (12 theorems) — 100% proven ✅
- Counter (19 theorems) — 100% proven ✅
- Owned (18 theorems) — 100% proven ✅
- SimpleToken (43 theorems: 33 basic + 10 correctness) — 100% proven ✅
- OwnedCounter (26 theorems) — 100% proven ✅
- Ledger (18 theorems) — 100% proven ✅
- SafeCounter (16 theorems) — 100% proven ✅

**Total: 152/152 theorems fully proven (100%) — zero sorry, zero axioms**

### Verification Tiers Achieved

**Tier 1: Safety Properties** ✅
- Balance non-negativity (implicit via Nat)
- Access control respected (mint reverts when not owner)
- No overdrafts (transfer reverts with insufficient balance)
- Overflow/underflow protection (SafeCounter revert proofs)

**Tier 2: Functional Correctness** ✅
- Transfer moves exact amount (sender decreases, recipient increases)
- Mint increases supply correctly
- All state transitions match specifications
- Constructor initializes correctly

**Tier 3: Invariants** ✅
- WellFormedState preserved by all operations (constructor, mint, transfer, reads)
- Owner stability (mint and transfer don't change owner)
- Storage isolation (operations only modify their designated slots)
- Bounds preservation (SafeCounter count stays within MAX_UINT256)

**Tier 4: Composition** ✅
- mint→balanceOf returns expected balance
- mint→getTotalSupply returns expected supply
- transfer→balanceOf returns expected sender/recipient balances
- constructor→getCount, constructor→getOwner end-to-end

### Key Achievements

✅ **SimpleStorage**: store/retrieve correctness, state isolation
✅ **Counter**: Arithmetic operations, composition (increment_twice_adds_two)
✅ **Owned**: Access control, ownership management, guard-protected transferOwnership
✅ **SimpleToken**: Constructor, mint (owner-guarded), transfer (balance-guarded), all reads, invariant preservation, revert proofs, end-to-end composition
✅ **OwnedCounter**: Composed ownership + counter patterns, storage isolation
✅ **Ledger**: Mapping-based deposit/withdraw/transfer, balance guards
✅ **SafeCounter**: Checked arithmetic with safeAdd/safeSub, overflow/underflow reverts, bounds preservation
✅ **Guard Modeling**: `ContractResult` type with explicit success/revert
✅ **Zero Sorry**: All proofs machine-checked, no axioms

### Proof Architecture

```
DumbContracts/
├── Core.lean (212 lines — ContractResult, require, simp lemmas)
├── Stdlib/Math.lean — Safe arithmetic (safeAdd, safeSub, MAX_UINT256)
├── Examples/ — 7 contract implementations
├── Specs/
│   ├── SimpleStorage/ (Spec.lean, Invariants.lean)
│   ├── Counter/ (Spec.lean, Invariants.lean)
│   ├── Owned/ (Spec.lean, Invariants.lean)
│   ├── SimpleToken/ (Spec.lean, Invariants.lean)
│   ├── OwnedCounter/ (Spec.lean, Invariants.lean)
│   ├── Ledger/ (Spec.lean, Invariants.lean)
│   └── SafeCounter/ (Spec.lean, Invariants.lean)
└── Proofs/
    ├── SimpleStorage/Basic.lean (12 theorems)
    ├── Counter/Basic.lean (19 theorems)
    ├── Owned/Basic.lean (18 theorems)
    ├── SimpleToken/Basic.lean (33 theorems)
    ├── SimpleToken/Correctness.lean (10 theorems)
    ├── OwnedCounter/Basic.lean (26 theorems)
    ├── Ledger/Basic.lean (18 theorems)
    └── SafeCounter/Basic.lean (16 theorems)
```

### Proof Techniques

- **Full unfolding**: `simp only [op, bind, Bind.bind, Pure.pure, Contract.run, ContractResult.snd, ...]`
- **Private unfold helpers**: Pre-compute exact result state when guards pass
- **Boolean equality conversion**: `beq_iff_eq` converts `(x == y) = true` to `x = y`
- **Slot preservation**: `intro slot h_neq h_eq; exact absurd h_eq h_neq`
- **Safe arithmetic helpers**: `safeAdd_some`/`safeSub_some` with `Nat.not_lt.mpr` for MAX_UINT256
- **Spec derivation**: Prove `meets_spec` first, then derive individual properties from it

### Known Limitations
- Transfer theorems require `sender ≠ to` (self-transfer overwrites sender deduction)
- `ContractResult.fst` requires `[Inhabited α]` constraint
- Complex invariants (supply = sum of balances) need finite address model
- `omega` can't see through `MAX_UINT256` def — use `Nat.not_lt.mpr`
- No Mathlib: `push_neg` unavailable, use `by_cases` or explicit witnesses

### CI/CD
- **Proof verification**: `.github/workflows/verify.yml` — runs `lake build` + sorry check
- **Docs build**: `.github/workflows/docs.yml` — checks docs-site builds
- **Deployment**: Vercel (automatic on push to main)

### Future Directions
1. Self-transfer support (model as identity operation)
2. Supply = sum of balances (requires finite address model)
3. Extended tokens (approval/transferFrom verification)
4. Gas modeling (add consumption tracking to ContractResult)
5. Cross-contract composition proofs
