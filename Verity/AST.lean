/-
  Verity.AST: Unified Contract AST

  A single deep embedding that maps 1:1 to EDSL primitives. Used by both:
  - `denote` (AST → Contract α) for proofs — see Verity/Denote.lean
  - The compiler (AST → Yul) for code generation (future)

  Design invariant: every constructor corresponds to exactly one EDSL
  primitive, so `denote ast = handwritten_fn` holds by `rfl`.

  Storage slots are `Nat` (matching `StorageSlot.mk n`), not string field
  names. This eliminates the name→slot lookup that the current ContractSpec
  compiler does and makes `rfl` proofs possible.

  Well-formedness convention: Effectful reads (storage, mappings, msgSender)
  must appear only in `Stmt.bind` position. Value expressions inside
  `sstore`/`mstore`/`require` reference only bound variables and literals.
-/

import Verity.Core

namespace Verity.AST

open Verity

/-- Expressions. Two flavors by convention:
    - *Effectful* (storage, storageAddr, mapping, sender): only in Stmt.bind position
    - *Pure* (lit, var, add, sub, ...): anywhere -/
inductive Expr where
  | lit         : Uint256 → Expr                -- literal value
  | var         : String → Expr                 -- bound Uint256 variable
  | varAddr     : String → Expr                 -- bound Address variable
  | storage     : Nat → Expr                    -- getStorage ⟨slot⟩  [effectful]
  | storageAddr : Nat → Expr                    -- getStorageAddr ⟨slot⟩  [effectful]
  | mapping     : Nat → Expr → Expr             -- getMapping ⟨slot⟩ key  [effectful]
  | sender      : Expr                          -- msgSender  [effectful]
  | add         : Expr → Expr → Expr            -- EVM.Uint256.add
  | sub         : Expr → Expr → Expr            -- EVM.Uint256.sub
  | mul         : Expr → Expr → Expr            -- EVM.Uint256.mul
  | eqAddr      : Expr → Expr → Expr            -- Address equality (BEq on Address)
  | ge          : Expr → Expr → Expr            -- Uint256 ≥ (GE.ge on Uint256)
  | gt          : Expr → Expr → Expr            -- Uint256 > (GT.gt on Uint256)
  | safeAdd     : Expr → Expr → Expr            -- Stdlib.Math.safeAdd [Option-returning]
  | safeSub     : Expr → Expr → Expr            -- Stdlib.Math.safeSub [Option-returning]
  deriving Repr

/-- Statements. Each constructor maps to one EDSL operation.
    The continuation-passing style (`rest : Stmt`) mirrors do-notation
    desugaring into chains of `Verity.bind`. -/
inductive Stmt where
  -- Terminals
  | ret         : Expr → Stmt                   -- return Uint256 value
  | retAddr     : Expr → Stmt                   -- return Address value
  | stop        : Stmt                          -- return ()
  -- Monadic binds (effectful read → named variable → continuation)
  | bindUint    : String → Expr → Stmt → Stmt   -- let x ← [Contract Uint256]; rest
  | bindAddr    : String → Expr → Stmt → Stmt   -- let x ← [Contract Address]; rest
  | bindBool    : String → Expr → Stmt → Stmt   -- let x ← [Contract Bool]; rest
  -- Pure let (no monadic effect, just name a computed value)
  | letUint     : String → Expr → Stmt → Stmt   -- let x := [pure Uint256]; rest
  -- Storage writes (effectful, with continuation)
  | sstore      : Nat → Expr → Stmt → Stmt      -- setStorage ⟨slot⟩ value; rest
  | sstoreAddr  : Nat → Expr → Stmt → Stmt      -- setStorageAddr ⟨slot⟩ value; rest
  | mstore      : Nat → Expr → Expr → Stmt → Stmt  -- setMapping ⟨slot⟩ key value; rest
  -- Guards
  | require     : Expr → String → Stmt → Stmt   -- require cond msg; rest
  | requireSome : String → Expr → String → Stmt → Stmt  -- let x ← requireSomeUint expr msg; rest
  -- Control flow
  | ite         : Expr → Stmt → Stmt → Stmt     -- if cond then t else e
  deriving Repr

end Verity.AST
