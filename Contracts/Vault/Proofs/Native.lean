/-
  Concrete G3 native theorems for the minimal ERC-4626 Vault IR fixture.

  Proves that:
  - `vaultMinimalIRContract.functions` bodies are `BridgedStmts`.
  - The emitted Yul runtime lowers to a concrete native `YulContract`
    consumable by `nativeResultsMatchOn`.

  These are the smallest concrete native-side theorems for an
  ERC-4626-shaped contract. Larger entrypoints (`deposit` with storage
  writes + overflow guards, `balanceOf` with mapping reads) follow the
  same lowering chain and are deferred to subsequent per-entrypoint
  native theorems.
-/

import Compiler.VaultMinimalNativeWitness
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates
import Compiler.Proofs.EndToEnd

namespace Contracts.Vault.Proofs.Native

open Compiler
open Compiler.Yul
open Compiler.Proofs
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration.Backends
open Compiler.Proofs.EndToEnd

/-- Each function body in the minimal Vault IR fixture is in the
EVMYulLean-bridged Yul fragment. The single `totalAssets()` body is
`[mstore(0, sload(0)), return(0, 32)]`. -/
theorem vaultMinimal_functions_bridged :
    ∀ fn, fn ∈ vaultMinimalIRContract.functions →
      BridgedStmts fn.body := by
  intro fn hmem
  simp [vaultMinimalIRContract] at hmem
  subst hmem
  refine BridgedStmts_cons_mstore (Yul.YulExpr.lit 0) _ (BridgedExpr.lit 0) ?_ ?_
  · refine BridgedExpr.call "sload" [Yul.YulExpr.lit 0] (Or.inl ?_) ?_
    · simp [bridgedBuiltins]
    · intro arg harg
      simp at harg
      subst arg
      exact BridgedExpr.lit 0
  · exact BridgedStmts_singleton_return (Yul.YulExpr.lit 0) (Yul.YulExpr.lit 32)
      (BridgedExpr.lit 0) (BridgedExpr.lit 32)

/-- The native lowering of the minimal Vault IR fixture's emitted Yul
runtime exists. Pins the native lowering for downstream
`nativeResultsMatchOn` use. -/
theorem vaultMinimal_runtime_lowers_native :
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul vaultMinimalIRContract).runtimeCode =
        .ok Compiler.VaultMinimalNativeWitness.nativeContract :=
  Compiler.VaultMinimalNativeWitness.lowerRuntimeContractNative_eq

/-- The lone function in the minimal Vault IR fixture. -/
def totalAssetsFunction : IRFunction :=
  vaultMinimalIRContract.functions.head (by simp [vaultMinimalIRContract])

/-- Concrete `nativeResultsMatchOn` projection for the minimal Vault fixture's
`totalAssets()` entrypoint: a non-zero `msg.value` on this non-payable view
function makes both the IR interpreter AND any aligned native result revert
observably-equally.

This is a concrete `nativeResultsMatchOn`-shaped theorem for an
ERC-4626-shaped contract.  The successful-execution path requires the full
per-case dispatcher-match-bridge machinery and is therefore deferred to a
subsequent native theorem. -/
theorem vaultMinimal_totalAssets_nativeResultsMatchOn_revert_of_nonzero_value
    (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat)
    (hSelector : tx.functionSelector = 0x01e1d114)
    (hNonzero : tx.msgValue % Compiler.Constants.evmModulus ≠ 0) :
    nativeResultsMatchOn observableSlots
      (interpretIR vaultMinimalIRContract tx state)
      (.ok
        { success := false
          returnValue := none
          finalStorage := state.storage
          finalMappings := storageAsMappings state.storage
          events := state.events }) := by
  have hFind : vaultMinimalIRContract.functions.find?
      (fun fn => fn.selector == tx.functionSelector) = some totalAssetsFunction := by
    simp [vaultMinimalIRContract, totalAssetsFunction, hSelector]
  have hPayable : totalAssetsFunction.payable = false := by
    simp [totalAssetsFunction, vaultMinimalIRContract]
  exact nativeResultsMatchOn_interpretIR_revert_of_nonpayable_nonzero
    vaultMinimalIRContract tx state observableSlots totalAssetsFunction
    hFind hPayable hNonzero

end Contracts.Vault.Proofs.Native
