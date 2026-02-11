/-
  Correctness proofs for all safe arithmetic operations in the Math stdlib.

  Covers safeAdd, safeSub, safeMul, and safeDiv: each operation returns
  the correct result when within bounds and returns none otherwise.
-/

import DumbContracts.Core
import DumbContracts.Stdlib.Math

namespace DumbContracts.Proofs.Stdlib.Math

open DumbContracts
open DumbContracts.Stdlib.Math

/-! ## safeAdd Correctness -/

/-- safeAdd returns the sum when no overflow occurs. -/
theorem safeAdd_some (a b : Uint256) (h : (a : Nat) + (b : Nat) ≤ MAX_UINT256) :
  safeAdd a b = some (a + b) := by
  simp only [safeAdd]
  have h_not : ¬((a : Nat) + (b : Nat) > MAX_UINT256) := Nat.not_lt.mpr h
  simp [h_not]

/-- safeAdd returns none on overflow. -/
theorem safeAdd_none (a b : Uint256) (h : (a : Nat) + (b : Nat) > MAX_UINT256) :
  safeAdd a b = none := by
  simp only [safeAdd]
  simp [h]

/-- safeAdd with zero on the left returns the other operand (when within bounds). -/
theorem safeAdd_zero_left (b : Uint256) (h : (b : Nat) ≤ MAX_UINT256) :
  safeAdd 0 b = some b := by
  have h_not : ¬((b : Nat) > MAX_UINT256) := Nat.not_lt.mpr h
  simp [safeAdd, h_not]

/-- safeAdd with zero on the right returns the other operand (when within bounds). -/
theorem safeAdd_zero_right (a : Uint256) (h : (a : Nat) ≤ MAX_UINT256) :
  safeAdd a 0 = some a := by
  have h_not : ¬((a : Nat) > MAX_UINT256) := Nat.not_lt.mpr h
  simp [safeAdd, h_not]

/-- safeAdd is commutative. -/
theorem safeAdd_comm (a b : Uint256) :
  safeAdd a b = safeAdd b a := by
  simp [safeAdd, Nat.add_comm]

/-- safeAdd result is always bounded by MAX_UINT256 when successful. -/
theorem safeAdd_result_bounded (a b : Uint256) (c : Uint256)
  (h : safeAdd a b = some c) : c ≤ MAX_UINT256 := by
  by_cases hsum : (a : Nat) + (b : Nat) > MAX_UINT256
  · simp [safeAdd, hsum] at h
  · have hsum_le : (a : Nat) + (b : Nat) ≤ MAX_UINT256 := Nat.not_lt.mp hsum
    have hlt : (a : Nat) + (b : Nat) < DumbContracts.Core.Uint256.modulus := by
      have hlt' : (a : Nat) + (b : Nat) < MAX_UINT256 + 1 := Nat.lt_succ_of_le hsum_le
      simpa [DumbContracts.Core.Uint256.max_uint256_succ_eq_modulus] using hlt'
    simp [safeAdd, hsum] at h
    have hc : a + b = c := by simpa using h
    have hle : (c : Nat) ≤ MAX_UINT256 := by
      have hadd : ((a + b : Uint256) : Nat) = (a : Nat) + (b : Nat) :=
        DumbContracts.Core.Uint256.add_eq_of_lt hlt
      simpa [hc.symm, hadd] using hsum_le
    simpa using hle

/-! ## safeSub Correctness -/

/-- safeSub returns the difference when no underflow occurs. -/
theorem safeSub_some (a b : Uint256) (h : (a : Nat) ≥ (b : Nat)) :
  safeSub a b = some (a - b) := by
  simp only [safeSub]
  have h_not : ¬((b : Nat) > (a : Nat)) := Nat.not_lt.mpr h
  simp [h_not]

/-- safeSub returns none on underflow. -/
theorem safeSub_none (a b : Uint256) (h : (b : Nat) > (a : Nat)) :
  safeSub a b = none := by
  simp only [safeSub]
  simp [h]

/-- safeSub of zero from any value is always safe. -/
theorem safeSub_zero (a : Uint256) :
  safeSub a 0 = some a := by
  simp [safeSub]

/-- safeSub of a value from itself returns zero. -/
theorem safeSub_self (a : Uint256) :
  safeSub a a = some 0 := by
  simp [safeSub]

/-- safeSub result never exceeds the minuend. -/
theorem safeSub_result_le (a b : Uint256) (c : Uint256)
  (h : safeSub a b = some c) : c ≤ a := by
  by_cases hlt : (b : Nat) > (a : Nat)
  · simp [safeSub, hlt] at h
  · have hle' : (b : Nat) ≤ (a : Nat) := Nat.not_lt.mp hlt
    simp [safeSub, hlt] at h
    have hc : a - b = c := by simpa using h
    have hle : (c : Nat) ≤ (a : Nat) := by
      have hsub : ((a - b : Uint256) : Nat) = (a : Nat) - (b : Nat) :=
        DumbContracts.Core.Uint256.sub_eq_of_le hle'
      simp [hc.symm, hsub]
    simpa using hle

/-! ## safeMul Correctness -/

/-- safeMul returns the product when no overflow occurs. -/
theorem safeMul_some (a b : Uint256) (h : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
  safeMul a b = some (a * b) := by
  simp only [safeMul]
  have h_not : ¬((a : Nat) * (b : Nat) > MAX_UINT256) := Nat.not_lt.mpr h
  simp [h_not]

/-- safeMul returns none on overflow. -/
theorem safeMul_none (a b : Uint256) (h : (a : Nat) * (b : Nat) > MAX_UINT256) :
  safeMul a b = none := by
  simp only [safeMul]
  simp [h]

/-- safeMul of zero is always safe and returns zero. -/
theorem safeMul_zero_left (b : Uint256) :
  safeMul 0 b = some 0 := by
  simp [safeMul]

/-- safeMul of zero is always safe and returns zero. -/
theorem safeMul_zero_right (a : Uint256) :
  safeMul a 0 = some 0 := by
  simp [safeMul]

/-- safeMul of one returns the other operand (when within bounds). -/
theorem safeMul_one_left (b : Uint256) (h : (b : Nat) ≤ MAX_UINT256) :
  safeMul 1 b = some b := by
  have h_not : ¬((b : Nat) > MAX_UINT256) := Nat.not_lt.mpr h
  simp [safeMul, h_not]

/-- safeMul of one returns the other operand (when within bounds). -/
theorem safeMul_one_right (a : Uint256) (h : (a : Nat) ≤ MAX_UINT256) :
  safeMul a 1 = some a := by
  have h_not : ¬((a : Nat) > MAX_UINT256) := Nat.not_lt.mpr h
  simp [safeMul, h_not]

/-- safeMul is commutative. -/
theorem safeMul_comm (a b : Uint256) :
  safeMul a b = safeMul b a := by
  simp [safeMul, Nat.mul_comm]

/-! ## safeDiv Correctness -/

/-- safeDiv returns the quotient when divisor is nonzero. -/
theorem safeDiv_some (a b : Uint256) (h : b ≠ 0) :
  safeDiv a b = some (a / b) := by
  have h_not : b.val ≠ 0 := by
    intro hval
    apply h
    apply DumbContracts.Core.Uint256.ext
    simpa using hval
  simp [safeDiv, h_not]

/-- safeDiv returns none when divisor is zero. -/
theorem safeDiv_none (a : Uint256) :
  safeDiv a 0 = none := by
  simp only [safeDiv]
  simp

/-- safeDiv of zero always returns zero (when divisor is nonzero). -/
theorem safeDiv_zero_numerator (b : Uint256) (h : b ≠ 0) :
  safeDiv 0 b = some 0 := by
  have h_not : b.val ≠ 0 := by
    intro hval
    apply h
    apply DumbContracts.Core.Uint256.ext
    simpa using hval
  simp [safeDiv, h_not]

/-- safeDiv by one returns the numerator. -/
theorem safeDiv_by_one (a : Uint256) :
  safeDiv a 1 = some a := by
  simp [safeDiv]

/-- safeDiv of a value by itself returns 1 (when nonzero). -/
theorem safeDiv_self (a : Uint256) (h : a ≠ 0) :
  safeDiv a a = some 1 := by
  have h_not : a.val ≠ 0 := by
    intro hzero
    apply h
    apply DumbContracts.Core.Uint256.ext
    simpa using hzero
  have hpos : 0 < (a : Nat) := Nat.pos_of_ne_zero h_not
  have hdiv : a / a = (1 : Uint256) := by
    apply DumbContracts.Core.Uint256.ext
    have hlt : (1 : Nat) < DumbContracts.Core.Uint256.modulus := by
      dsimp [DumbContracts.Core.Uint256.modulus, DumbContracts.Core.UINT256_MODULUS]
      decide
    calc
      (a / a).val = (a.val / a.val) % DumbContracts.Core.Uint256.modulus := by
        simp [HDiv.hDiv, DumbContracts.Core.Uint256.div, h_not, DumbContracts.Core.Uint256.ofNat]
      _ = 1 % DumbContracts.Core.Uint256.modulus := by
        simp [Nat.div_self hpos]
      _ = 1 := by
        simp [Nat.mod_eq_of_lt hlt]
  simp [safeDiv, h_not, hdiv]

/-! ## Cross-Operation Properties -/

/-- safeMul result is always bounded by MAX_UINT256 when successful. -/
theorem safeMul_result_bounded (a b : Uint256) (c : Uint256)
  (h : safeMul a b = some c) : c ≤ MAX_UINT256 := by
  by_cases hprod : (a : Nat) * (b : Nat) > MAX_UINT256
  · simp [safeMul, hprod] at h
  · have hprod_le : (a : Nat) * (b : Nat) ≤ MAX_UINT256 := Nat.not_lt.mp hprod
    have hlt : (a : Nat) * (b : Nat) < DumbContracts.Core.Uint256.modulus := by
      have hlt' : (a : Nat) * (b : Nat) < MAX_UINT256 + 1 := Nat.lt_succ_of_le hprod_le
      simpa [DumbContracts.Core.Uint256.max_uint256_succ_eq_modulus] using hlt'
    simp [safeMul, hprod] at h
    have hc : a * b = c := by simpa using h
    have hle : (c : Nat) ≤ MAX_UINT256 := by
      have hmul : ((a * b : Uint256) : Nat) = (a : Nat) * (b : Nat) :=
        DumbContracts.Core.Uint256.mul_eq_of_lt hlt
      simpa [hc.symm, hmul] using hprod_le
    simpa using hle

/-- safeDiv result never exceeds the numerator. -/
theorem safeDiv_result_le_numerator (a b : Uint256) (c : Uint256)
  (h_div : safeDiv a b = some c) : c ≤ a := by
  by_cases hzero : b.val = 0
  · simp [safeDiv, hzero] at h_div
  · simp [safeDiv, hzero] at h_div
    have hc : a / b = c := by simpa using h_div
    have hle : (c : Nat) ≤ (a : Nat) := by
      have hdiv : ((a / b : Uint256) : Nat) = (a : Nat) / (b : Nat) := by
        have hdiv_lt : (a : Nat) / (b : Nat) < DumbContracts.Core.Uint256.modulus := by
          have hle' : (a : Nat) / (b : Nat) ≤ (a : Nat) := Nat.div_le_self _ _
          exact Nat.lt_of_le_of_lt hle' a.isLt
        calc
          ((a / b : Uint256) : Nat) = ((a : Nat) / (b : Nat)) % DumbContracts.Core.Uint256.modulus := by
            simp [HDiv.hDiv, DumbContracts.Core.Uint256.div, hzero, DumbContracts.Core.Uint256.ofNat]
          _ = (a : Nat) / (b : Nat) := by
            exact Nat.mod_eq_of_lt hdiv_lt
      simpa [hc.symm, hdiv] using Nat.div_le_self (a : Nat) (b : Nat)
    simpa using hle

/-! ## Summary

All 25 theorems fully proven with zero sorry:

safeAdd:
1. safeAdd_some — returns sum when no overflow
2. safeAdd_none — returns none on overflow
3. safeAdd_zero_left — 0 + b = b when bounded
4. safeAdd_zero_right — a + 0 = a when bounded
5. safeAdd_comm — commutativity
6. safeAdd_result_bounded — successful result ≤ MAX_UINT256

safeSub:
7. safeSub_some — returns difference when no underflow
8. safeSub_none — returns none on underflow
9. safeSub_zero — a - 0 = a always safe
10. safeSub_self — a - a = 0 always safe
11. safeSub_result_le — result never exceeds minuend

safeMul:
12. safeMul_some — returns product when no overflow
13. safeMul_none — returns none on overflow
14. safeMul_zero_left — 0 * b = 0 always safe
15. safeMul_zero_right — a * 0 = 0 always safe
16. safeMul_one_left — 1 * b = b when bounded
17. safeMul_one_right — a * 1 = a when bounded
18. safeMul_comm — commutativity
19. safeMul_result_bounded — successful result ≤ MAX_UINT256

safeDiv:
20. safeDiv_some — returns quotient when divisor nonzero
21. safeDiv_none — returns none on division by zero
22. safeDiv_zero_numerator — 0 / b = 0
23. safeDiv_by_one — a / 1 = a
24. safeDiv_self — a / a = 1
25. safeDiv_result_le_numerator — result never exceeds numerator
-/

end DumbContracts.Proofs.Stdlib.Math
