import Compiler.Codegen
import Compiler.Proofs.IRGeneration.Expr
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness

/-!
Computed native lowering witness for the G3 minimal ERC-4626 Vault IR
fixture.

Mirrors `Compiler/SimpleStorageNativeWitness.lean`: this file is deliberately
outside `Compiler/Proofs` and `Contracts/` so the executable
`native_decide` packaging stays out of the proof-hygiene scope.
-/

namespace Compiler.VaultMinimalNativeWitness

open Compiler.Proofs.IRGeneration

theorem lowerRuntimeContractNative_ok :
    ∃ nativeContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul vaultMinimalIRContract).runtimeCode = .ok nativeContract := by
  have hOk :
      (match
          Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
            (Compiler.emitYul vaultMinimalIRContract).runtimeCode with
        | .ok _ => true
        | .error _ => false) = true := by
    native_decide
  cases hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul vaultMinimalIRContract).runtimeCode with
  | ok nativeContract =>
      exact ⟨nativeContract, rfl⟩
  | error _ =>
      have := hOk
      rw [hLower] at this
      cases this

def nativeContract : EvmYul.Yul.Ast.YulContract :=
  match
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul vaultMinimalIRContract).runtimeCode with
  | .ok nativeContract => nativeContract
  | .error _ => { dispatcher := .Block [], functions := ∅ }

@[simp] theorem lowerRuntimeContractNative_eq :
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul vaultMinimalIRContract).runtimeCode =
        .ok nativeContract :=
  by
    have hOk :
        (match
            Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
              (Compiler.emitYul vaultMinimalIRContract).runtimeCode with
          | .ok _ => true
          | .error _ => false) = true := by
      native_decide
    cases hLower :
        Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
          (Compiler.emitYul vaultMinimalIRContract).runtimeCode with
    | ok lowered =>
        unfold nativeContract
        rw [hLower]
    | error err =>
        rw [hLower] at hOk
        cases hOk

end Compiler.VaultMinimalNativeWitness
