/-
  EVM-Compatible Uint256 Operations

  This module provides arithmetic operations with EVM semantics:
  - All operations wrap at 2^256 (modular arithmetic)
  - Division by zero returns 0 (matches EVM)
  - Provides overflow/underflow detection predicates

  These operations ensure semantic equivalence between EDSL
  verification and compiled EVM execution.
-/

namespace DumbContracts.EVM

-- EVM maximum value for uint256
def MAX_UINT256 : Nat := 2^256 - 1

namespace Uint256

-- Modular addition (wraps at 2^256)
def add (a b : Nat) : Nat := (a + b) % (2^256)

-- Modular subtraction (two's complement wrapping)
def sub (a b : Nat) : Nat :=
  if b ≤ a then a - b
  else (2^256) - (b - a)

-- Modular multiplication (wraps at 2^256)
def mul (a b : Nat) : Nat := (a * b) % (2^256)

-- Division (returns 0 on division by zero, matching EVM)
def div (a b : Nat) : Nat :=
  if b = 0 then 0 else a / b

-- Modulo (returns 0 on mod by zero, matching EVM)
def mod (a b : Nat) : Nat :=
  if b = 0 then 0 else a % b

  -- Overflow detection predicates for safety proofs

def willAddOverflow (a b : Nat) : Bool :=
  a + b ≥ 2^256

def willSubUnderflow (a b : Nat) : Bool :=
  b > a

  def willMulOverflow (a b : Nat) : Bool :=
    a * b ≥ 2^256

  -- Lemmas for modular arithmetic reasoning when no overflow/underflow occurs.

  theorem add_eq_of_lt {a b : Nat} (h : a + b < 2^256) : add a b = a + b := by
    simp [add, Nat.mod_eq_of_lt h]

  theorem sub_eq_of_le {a b : Nat} (h : b ≤ a) : sub a b = a - b := by
    simp [sub, h]

end Uint256

end DumbContracts.EVM
