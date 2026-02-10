import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Increment a slot by one, but only if it is already non-zero. -/

def bumpIfNonZeroFun : Fun :=
  { name := "bumpIfNonZero"
    args := ["slot"]
    body := requireNonZero (Expr.sload (v "slot")) (sstoreInc (v "slot"))
    ret := none }

def bumpIfNonZeroSpecR (slot : Nat) : SpecR Store :=
  { requires := fun s => s slot != 0
    ensures := fun s s' => s' = updateStore s slot (s slot + 1)
    reverts := fun s => s slot = 0 }

theorem bumpIfNonZero_meets_specR_ok (s : Store) (slot : Nat) :
    (bumpIfNonZeroSpecR slot).requires s ->
    (match execFun bumpIfNonZeroFun [slot] s [] with
      | ExecResult.ok _ s' => (bumpIfNonZeroSpecR slot).ensures s s'
      | _ => False) := by
  intro hreq
  have hnonzero : s slot != 0 := by exact hreq
  simp [bumpIfNonZeroSpecR, bumpIfNonZeroFun, requireNonZero, requireNeq, neq, eq, require, sstoreInc,
    sstoreAdd, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, v, n, hnonzero]

theorem bumpIfNonZero_meets_specR_reverts (s : Store) (slot : Nat) :
    (bumpIfNonZeroSpecR slot).reverts s ->
    execFun bumpIfNonZeroFun [slot] s [] = ExecResult.reverted := by
  intro hrev
  simp [bumpIfNonZeroSpecR, bumpIfNonZeroFun, requireNonZero, requireNeq, neq, eq, require, sstoreInc,
    sstoreAdd, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, v, n, hrev]

end DumbContracts.Examples
