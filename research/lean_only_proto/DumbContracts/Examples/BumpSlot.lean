import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Increment a slot by one. -/

def bumpSlotFun : Fun :=
  { name := "bumpSlot"
    args := ["slot"]
    body := sstoreAdd (v "slot") (n 1)
    ret := none }

def bumpSlotSpec (slot : Nat) : Spec Store :=
  { requires := fun _ => True
    ensures := fun s s' => s' = updateStore s slot (s slot + 1) }

theorem bumpSlot_meets_spec (s : Store) (slot : Nat) :
    (bumpSlotSpec slot).requires s ->
    (match execFun bumpSlotFun [slot] s [] with
      | ExecResult.ok _ s' => (bumpSlotSpec slot).ensures s s'
      | _ => False) := by
  intro _hreq
  simp [bumpSlotSpec, bumpSlotFun, sstoreAdd, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, v, n]

end DumbContracts.Examples
