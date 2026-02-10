import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Add a delta to a slot only if the delta is non-zero and below a max. -/

def addIfNonZeroAndLessFun : Fun :=
  { name := "addIfNonZeroAndLess"
    args := ["slot", "delta", "max"]
    body :=
      requireNonZeroAndLt
        (v "delta")
        (v "max")
        (sstoreAdd (v "slot") (v "delta"))
    ret := none }

def addIfNonZeroAndLessSpecR (slot delta max : Nat) : SpecR Store :=
  { requires := fun _ => delta != 0 ∧ delta < max
    ensures := fun s s' => s' = updateStore s slot (s slot + delta)
    reverts := fun _ => delta = 0 ∨ delta >= max }

theorem addIfNonZeroAndLess_meets_specR_ok (s : Store) (slot delta max : Nat) :
    (addIfNonZeroAndLessSpecR slot delta max).requires s ->
    (match execFun addIfNonZeroAndLessFun [slot, delta, max] s [] with
      | ExecResult.ok _ s' => (addIfNonZeroAndLessSpecR slot delta max).ensures s s'
      | _ => False) := by
  intro hreq
  rcases hreq with ⟨hnonzero, hlt⟩
  simp [addIfNonZeroAndLessSpecR, addIfNonZeroAndLessFun, requireNonZeroAndLt, requireAnd, require,
    neq, eq, sstoreAdd, v, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore,
    hnonzero, hlt]

theorem addIfNonZeroAndLess_meets_specR_reverts (s : Store) (slot delta max : Nat) :
    (addIfNonZeroAndLessSpecR slot delta max).reverts s ->
    execFun addIfNonZeroAndLessFun [slot, delta, max] s [] = ExecResult.reverted := by
  intro hrev
  rcases hrev with hzero | hge
  · simp [addIfNonZeroAndLessSpecR, addIfNonZeroAndLessFun, requireNonZeroAndLt, requireAnd, require,
      neq, eq, sstoreAdd, v, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore,
      hzero]
  · by_cases hnonzero : delta != 0
    · have hnotlt : ¬ delta < max := by
        exact Nat.not_lt.mpr hge
      simp [addIfNonZeroAndLessSpecR, addIfNonZeroAndLessFun, requireNonZeroAndLt, requireAnd, require,
        neq, eq, sstoreAdd, v, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore,
        hnonzero, hnotlt]
    · have hnot : ¬ delta != 0 := by
        exact hnonzero
      simp [addIfNonZeroAndLessSpecR, addIfNonZeroAndLessFun, requireNonZeroAndLt, requireAnd, require,
        neq, eq, sstoreAdd, v, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore,
        hnot]

end DumbContracts.Examples
