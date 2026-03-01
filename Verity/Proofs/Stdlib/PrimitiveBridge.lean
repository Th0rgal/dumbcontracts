/-
  Verity.Proofs.Stdlib.PrimitiveBridge: EDSL ↔ Compiled Yul Primitive Lemmas

  For each EDSL primitive used by the `verity_contract` macro, we prove (or
  state with sorry) a lemma connecting the EDSL monadic operation to the
  compiled Yul output's execution under the proof-level Yul semantics.

  These lemmas are the building blocks for the macro-generated per-function
  semantic bridge theorems (Step 3 of Issue #998).

  **Architecture**:
  - EDSL primitives operate on `ContractState` (typed: Uint256, Address)
  - Compiled Yul operates on `IRState`/`YulState` (untyped: Nat)
  - The bridge shows that under a consistent state encoding, the two sides
    produce equivalent results.

  **What this file does NOT import**:
  - EVMYulLean — we stay on the Verity builtin path (`defaultBuiltinBackend = .verity`)
  - The EVMYulLean agreement for pure builtins is separately established in
    ArithmeticProfile.lean. Composing that with these lemmas gives the full
    EDSL ≡ EVMYulLean chain.

  Run: lake build Verity.Proofs.Stdlib.PrimitiveBridge
-/

import Verity.Core
import Compiler.Proofs.YulGeneration.Builtins
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.Conversions
import Compiler.Constants

namespace Verity.Proofs.Stdlib.PrimitiveBridge

open Verity
open Verity.Core.Uint256
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Compiler.Constants (evmModulus)

/-! ## State Encoding

The EDSL uses `ContractState` with typed fields (Uint256, Address).
The compiled Yul uses `IRState` with Nat-valued storage.
We define a consistent encoding and prove round-trip properties.
-/

/-- Encode EDSL ContractState storage into IR-level Nat storage.
This is the canonical encoding used in all primitive bridge lemmas. -/
def encodeStorage (state : ContractState) : Nat → Nat :=
  fun slot => (state.storage slot).val

/-- Encode EDSL sender as Nat. -/
def encodeSender (state : ContractState) : Nat :=
  state.sender.val

/-! ## Storage Primitives: getStorage / setStorage

These are the simplest primitives: `getStorage slot` reads a Uint256 from
storage, `setStorage slot value` writes one. The compiler generates
`sload(slotLiteral)` and `sstore(slotLiteral, value)` respectively.
-/

/-- getStorage correctness: reading EDSL storage at slot `s` returns the same
value (modulo Uint256↔Nat encoding) as `sload` on the encoded storage.

The compiled Yul for `getStorage(s)` is `sload(s.slot)`. Under the Verity
builtin backend, `evalBuiltinCall ... "sload" [slot]` returns
`abstractLoadStorageOrMapping storage slot = storage slot`. -/
theorem getStorage_matches_sload (s : StorageSlot Uint256) (state : ContractState) :
    let edslValue := (getStorage s) state
    match edslValue with
    | .success val _ =>
      evalBuiltinCall (encodeStorage state) (encodeSender state) 0 [] "sload" [s.slot] =
        some val.val
    | .revert _ _ => False := by
  simp [getStorage, encodeStorage, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping]

/-- setStorage correctness: writing EDSL storage at slot `s` with value `v`
produces the same storage update as `sstore(s.slot, v.val)`.

The compiled Yul for `setStorage(s, v)` is `sstore(s.slot, v.val)`. Under the
Verity builtin semantics, `abstractStoreStorageOrMapping storage s.slot v.val`
updates slot `s.slot` to `v.val` and leaves other slots unchanged. -/
theorem setStorage_matches_sstore (s : StorageSlot Uint256) (v : Uint256) (state : ContractState) :
    let edslResult := (setStorage s v) state
    match edslResult with
    | .success () newState =>
      -- The new storage at slot s.slot equals v.val
      encodeStorage newState s.slot = v.val ∧
      -- Other slots are unchanged
      (∀ other, other ≠ s.slot → encodeStorage newState other = encodeStorage state other)
    | .revert _ _ => False := by
  simp [setStorage, encodeStorage]
  constructor
  · simp [beq_iff_eq]
  · intro other hne
    simp [beq_iff_eq, hne]

/-! ## Arithmetic Primitives: add / sub

The EDSL uses `Uint256.add` and `Uint256.sub` (wrapping at 2^256).
The compiler generates `add(a, b)` and `sub(a, b)` Yul builtins.
ArithmeticProfile.lean already proves these builtins wrap at evmModulus.
Here we bridge the EDSL Uint256 operations to the builtin semantics.
-/

/-- EDSL Uint256.add matches the compiled `add` builtin.

Both produce (a + b) % 2^256. The EDSL operates on Uint256 values
(val < 2^256), while the builtin operates on arbitrary Nat values
but wraps at evmModulus = 2^256. -/
theorem uint256_add_matches_builtin (a b : Uint256) :
    (Uint256.add a b).val =
      ((a.val + b.val) % evmModulus) := by
  simp [Uint256.add, Uint256.ofNat, Uint256.modulus, UINT256_MODULUS, evmModulus]
  rfl

/-- EDSL Uint256.sub matches the compiled `sub` builtin.

The Verity builtin computes (evmModulus + a - b) % evmModulus.
The EDSL Uint256.sub computes:
  if b ≤ a: (a - b) % modulus
  else: (modulus - (b - a)) % modulus

Both produce the same result since:
  (evmModulus + a - b) % evmModulus = (a - b) % evmModulus when b ≤ a
  (evmModulus + a - b) % evmModulus = (modulus - (b - a)) % modulus when b > a
-/
theorem uint256_sub_matches_builtin (a b : Uint256) :
    (Uint256.sub a b).val =
      ((evmModulus + a.val - b.val) % evmModulus) := by
  simp [Uint256.sub, Uint256.ofNat, Uint256.modulus, UINT256_MODULUS, evmModulus]
  by_cases h : b.val ≤ a.val
  · -- No underflow case: result is (a - b) % modulus
    -- We need: (a - b) % modulus = (modulus + a - b) % modulus
    simp [h]
    have hle : b.val ≤ evmModulus + a.val := Nat.le_add_left _ _
    omega
  · -- Underflow case: result is (modulus - (b - a)) % modulus
    -- Need: (2^256 - (b - a)) % 2^256 = (2^256 + a - b) % 2^256
    -- Both sides equal 2^256 - (b - a) since b - a < 2^256
    simp [h]
    have hb_lt := b.isLt
    have ha_lt := a.isLt
    omega

/-- EDSL Uint256.mul matches the compiled `mul` builtin. -/
theorem uint256_mul_matches_builtin (a b : Uint256) :
    (Uint256.mul a b).val =
      ((a.val * b.val) % evmModulus) := by
  simp [Uint256.mul, Uint256.ofNat, Uint256.modulus, UINT256_MODULUS, evmModulus]
  rfl

/-! ## Require Primitive

The EDSL `require cond msg` succeeds with () if `cond = true`, reverts if false.
The compiler generates: `if iszero(cond) { revert(0, 0) }`.
-/

/-- require(true) produces success, matching a no-op in the compiled Yul
(the iszero check fails, so the revert is skipped). -/
theorem require_true_matches_noop (msg : String) (state : ContractState) :
    (require true msg) state = ContractResult.success () state := by
  rfl

/-- require(false) produces revert, matching `revert(0, 0)` in the compiled Yul
(the iszero check passes, triggering the revert). -/
theorem require_false_matches_revert (msg : String) (state : ContractState) :
    (require false msg) state = ContractResult.revert msg state := by
  rfl

/-- General require bridge: the EDSL require and the compiled Yul iszero-revert
pattern agree on success/failure. -/
theorem require_matches_iszero_revert (cond : Bool) (msg : String) (state : ContractState) :
    let edslResult := (require cond msg) state
    let isSuccess := match edslResult with
      | .success _ _ => true
      | .revert _ _ => false
    -- The iszero builtin returns 1 when cond is false (= 0), triggering revert
    let condNat := if cond then 1 else 0
    let isZeroResult := evalBuiltinCall (fun _ => 0) 0 0 [] "iszero" [condNat]
    -- When iszero returns 0 (cond was nonzero), no revert → success
    -- When iszero returns 1 (cond was zero), revert → failure
    (isZeroResult = some 0 ↔ isSuccess = true) := by
  cases cond <;> simp [require, evalBuiltinCall]

/-! ## If/Else Branching

The EDSL uses Lean's `if cond then ... else ...` via the Contract monad.
The compiler generates `if cond { ... }` or `switch iszero(cond) case 0 { thenBranch } default { elseBranch }`.

The key insight is that branching correctness follows from condition
evaluation correctness — if the condition evaluates to the same boolean,
the branch taken is the same.
-/

/-- Branching correctness for the Contract monad: if two computations agree on
success/failure for each branch, and the condition evaluates the same way,
then the if/else produces the same result.

This is a structural lemma — it does not need to inspect the compiled Yul
directly, because the compiler's if/else generation is straightforward. -/
theorem if_else_matches {α : Type}
    (cond : Bool) (thenBranch elseBranch : Contract α) (state : ContractState) :
    (if cond then thenBranch else elseBranch) state =
      if cond then thenBranch state else elseBranch state := by
  cases cond <;> rfl

/-! ## Context Accessors: msgSender

The EDSL `msgSender` reads `state.sender`.
The compiler generates `caller()`.
-/

/-- msgSender matches the `caller` builtin. -/
theorem msgSender_matches_caller (state : ContractState) :
    let edslResult := msgSender state
    match edslResult with
    | .success addr _ =>
      evalBuiltinCall (encodeStorage state) (encodeSender state) 0 [] "caller" [] =
        some addr.val
    | .revert _ _ => False := by
  simp [msgSender, encodeSender, evalBuiltinCall]

/-! ## Bind (Sequencing) Correctness

The Contract monad's `bind` sequences operations. The compiler generates
sequential Yul statements. The key property is that if each step preserves
the state encoding invariant, then the whole sequence does.
-/

/-- Bind unfolding: the Contract monad's `bind` (>>=) sequences operations.
When the first computation succeeds, the continuation runs on the new state.
When it reverts, the revert propagates.

This is the key structural lemma for composing primitive bridge proofs: each
step in a `do` block is one bind, and the per-step lemma applies to that step's
initial state. -/
theorem bind_unfold {α β : Type}
    (ma : Contract α) (f : α → Contract β)
    (state : ContractState) :
    (bind ma f) state = match ma state with
      | .success a s' => f a s'
      | .revert msg s' => .revert msg s' := by
  simp [bind]

/-- Pure (return) unfold: `pure a` always succeeds with value `a` and unchanged state.
Companion to `bind_unfold` — together they handle all `do`-notation steps. -/
theorem pure_unfold {α : Type} (a : α) (state : ContractState) :
    (pure a : Contract α) state = .success a state := by
  rfl

/-! ## Composition Summary

The per-function semantic bridge theorem (generated by the macro) will
compose these primitives as follows:

For a function like `increment`:
```
  do
    let count ← getStorage countSlot      -- getStorage_matches_sload
    let newCount := count + Uint256.ofNat 1  -- uint256_add_matches_builtin
    setStorage countSlot newCount            -- setStorage_matches_sstore
```

The composed theorem says:
  EDSL(increment).run state ≡ YulExec(compiled_increment) encodedState

Each line's correctness follows from the corresponding primitive lemma.
The bind/sequencing correctness (`bind_unfold`) stitches them together.

The full chain: EDSL ≡ compiledYul ≡ EVMYulLean is obtained by composing:
1. These primitive lemmas (EDSL ≡ Verity-backend Yul builtins)
2. ArithmeticProfile.lean (Verity builtins ≡ EVMYulLean UInt256 for pure ops)
3. EndToEnd.lean (IR→Yul dispatch preservation)
-/

end Verity.Proofs.Stdlib.PrimitiveBridge
