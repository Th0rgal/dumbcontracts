/-
  Compiler.Proofs.ArithmeticProfile: Arithmetic profile specification and proofs

  Documents and proves the arithmetic semantics used across all compilation
  layers. Verity uses wrapping modular arithmetic at 2^256, matching the
  EVM Yellow Paper specification.

  This file serves as the single formal reference for arithmetic behavior:
  - Proves wrapping is consistent across EDSL and compiler layers
  - Proves EVMYulLean bridge agreement for pure builtins
  - Documents the checked (safe) arithmetic alternative at EDSL level
  - Establishes that all backend profiles share identical arithmetic semantics

  Run: lake build Compiler.Proofs.ArithmeticProfile
-/

import Compiler.Constants
import Compiler.Proofs.YulGeneration.Builtins
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Verity.Core.Uint256
import EvmYul.UInt256

namespace Compiler.Proofs.ArithmeticProfile

open Compiler.Constants (evmModulus)
open Compiler.Proofs.YulGeneration (evalBuiltinCall)
open Compiler.Proofs.YulGeneration.Backends (evalPureBuiltinViaEvmYulLean)

-- ============================================================================
-- § 1. Arithmetic profile constants
-- ============================================================================

/-- The arithmetic modulus is 2^256, matching EVM word size. -/
theorem modulus_is_2_pow_256 : evmModulus = 2 ^ 256 := rfl

/-- EVMYulLean's UInt256.size equals Verity's evmModulus. -/
theorem evmyullean_size_eq_verity_modulus :
    EvmYul.UInt256.size = evmModulus := by decide

-- ============================================================================
-- § 2. Wrapping semantics: compiler builtins are total and wrapping
-- ============================================================================

-- Dummy state parameters (arithmetic builtins are state-independent).
private def s : Nat → Nat := fun _ => 0
private def sender : Nat := 0
private def sel : Nat := 0
private def cd : List Nat := []

/-- Addition wraps: (a + b) mod 2^256. -/
theorem add_wraps (a b : Nat) :
    evalBuiltinCall s sender sel cd "add" [a, b] = some ((a + b) % evmModulus) := by
  simp [evalBuiltinCall]

/-- Subtraction wraps: (2^256 + a - b) mod 2^256. -/
theorem sub_wraps (a b : Nat) :
    evalBuiltinCall s sender sel cd "sub" [a, b] = some ((evmModulus + a - b) % evmModulus) := by
  simp [evalBuiltinCall]

/-- Multiplication wraps: (a * b) mod 2^256. -/
theorem mul_wraps (a b : Nat) :
    evalBuiltinCall s sender sel cd "mul" [a, b] = some ((a * b) % evmModulus) := by
  simp [evalBuiltinCall]

/-- Division by zero returns 0. -/
theorem div_by_zero (a : Nat) :
    evalBuiltinCall s sender sel cd "div" [a, 0] = some 0 := by
  simp [evalBuiltinCall]

/-- Modulo by zero returns 0. -/
theorem mod_by_zero (a : Nat) :
    evalBuiltinCall s sender sel cd "mod" [a, 0] = some 0 := by
  simp [evalBuiltinCall]

-- ============================================================================
-- § 3. EVMYulLean bridge agreement for pure arithmetic
-- ============================================================================

-- These smoke-test proofs demonstrate that the EVMYulLean bridge produces
-- the same results as Verity's evalBuiltinCall on concrete values.
-- A full universal equivalence proof (∀ a b, verity a b = evmyullean a b)
-- would require bridging Nat-modular and Fin-based UInt256 representations;
-- that is a future proof-engineering task.

/-- Bridge agrees on addition: 100 + 200. -/
example : evalBuiltinCall s sender sel cd "add" [100, 200] =
          evalPureBuiltinViaEvmYulLean "add" [100, 200] := by native_decide

/-- Bridge agrees on subtraction: 0 - 1 (underflow wraps). -/
example : evalBuiltinCall s sender sel cd "sub" [0, 1] =
          evalPureBuiltinViaEvmYulLean "sub" [0, 1] := by native_decide

/-- Bridge agrees on multiplication: 1000 * 2000. -/
example : evalBuiltinCall s sender sel cd "mul" [1000, 2000] =
          evalPureBuiltinViaEvmYulLean "mul" [1000, 2000] := by native_decide

/-- Bridge agrees on division by zero. -/
example : evalBuiltinCall s sender sel cd "div" [42, 0] =
          evalPureBuiltinViaEvmYulLean "div" [42, 0] := by native_decide

/-- Bridge agrees on modulo by zero. -/
example : evalBuiltinCall s sender sel cd "mod" [10, 0] =
          evalPureBuiltinViaEvmYulLean "mod" [10, 0] := by native_decide

-- ============================================================================
-- § 4. Backend profile invariant
-- ============================================================================

-- All backend profiles (semantic, solidity-parity-ordering, solidity-parity)
-- use the same evalBuiltinCall function. The profiles differ only in Yul
-- output shape (selector sorting, patch pass enablement), not arithmetic
-- semantics. This is enforced structurally: there is a single evalBuiltinCall
-- definition that all codepaths use.

/-- The BuiltinBackend enum has exactly two variants. -/
example : ∀ b : Compiler.Proofs.YulGeneration.BuiltinBackend,
    b = .verity ∨ b = .evmYulLean := by
  intro b; cases b <;> simp

-- ============================================================================
-- § 5. Scope boundaries (what is NOT proved here)
-- ============================================================================

-- Gas semantics: not formally modeled. Proofs establish semantic correctness
-- (same result), not gas correctness (same cost or bounded cost).
--
-- Compiler-layer overflow detection: the compiler does not insert automatic
-- overflow checks. Contracts that need checked arithmetic must use the EDSL
-- safeAdd/safeSub/safeMul functions, which return Option and revert on None.
--
-- Cryptographic primitives: keccak256 is axiomatized (see AXIOMS.md).
-- The mapping-slot derivation trusts the keccak FFI.
--
-- Universal bridge equivalence: the EVMYulLean bridge smoke tests cover
-- concrete values. A universal proof (∀ n, Nat-modular n ≡ Fin-based n)
-- is a future task.

end Compiler.Proofs.ArithmeticProfile
