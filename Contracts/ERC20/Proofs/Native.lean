/-
  Concrete G3 native theorems for the minimal ERC-20 IR fixture.

  Proves that:
  - `erc20MinimalIRContract.functions` bodies are `BridgedStmts` (the
    fragment EVMYulLean's native lowering admits).
  - The emitted Yul runtime lowers to a concrete native `YulContract`
    consumable by `nativeResultsMatchOn`.

  These are the smallest concrete native-side theorems for an ERC-20-shaped
  contract.  Larger entrypoints (`transfer`, `balanceOf` with mapping reads)
  follow the same lowering chain and are deferred to a subsequent
  per-entrypoint native theorem.
-/

import Compiler.ERC20MinimalNativeWitness
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates
import Compiler.Proofs.EndToEnd

namespace Contracts.ERC20.Proofs.Native

open Compiler
open Compiler.Yul
open Compiler.Proofs
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration.Backends
open Compiler.Proofs.EndToEnd

/-- Each function body in the minimal ERC-20 IR fixture is in the
EVMYulLean-bridged Yul fragment. The single `totalSupply()` body is
`[mstore(0, sload(1)), return(0, 32)]`, every primitive of which is
`bridgedBuiltins`. -/
theorem erc20Minimal_functions_bridged :
    ∀ fn, fn ∈ erc20MinimalIRContract.functions →
      BridgedStmts fn.body := by
  intro fn hmem
  simp [erc20MinimalIRContract] at hmem
  subst hmem
  refine BridgedStmts_cons_mstore (Yul.YulExpr.lit 0) _ (BridgedExpr.lit 0) ?_ ?_
  · refine BridgedExpr.call "sload" [Yul.YulExpr.lit 1] (Or.inl ?_) ?_
    · simp [bridgedBuiltins]
    · intro arg harg
      simp at harg
      subst arg
      exact BridgedExpr.lit 1
  · exact BridgedStmts_singleton_return (Yul.YulExpr.lit 0) (Yul.YulExpr.lit 32)
      (BridgedExpr.lit 0) (BridgedExpr.lit 32)

/-- The native lowering of the minimal ERC-20 IR fixture's emitted Yul
runtime exists.  This is the "concrete" half of any
`nativeResultsMatchOn`-projecting theorem for the fixture: the native
contract value witnessing the run is `Compiler.ERC20MinimalNativeWitness.nativeContract`,
and the equation below pins the lowering. -/
theorem erc20Minimal_runtime_lowers_native :
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul erc20MinimalIRContract).runtimeCode =
        .ok Compiler.ERC20MinimalNativeWitness.nativeContract :=
  Compiler.ERC20MinimalNativeWitness.lowerRuntimeContractNative_eq

/-- The lone function in the minimal ERC-20 IR fixture — pinned to
provide a stable handle without needing to project out of a `find?`. -/
def totalSupplyFunction : IRFunction :=
  erc20MinimalIRContract.functions.head (by simp [erc20MinimalIRContract])

/-- Concrete `nativeResultsMatchOn` projection for the minimal ERC-20 fixture's
`totalSupply()` entrypoint: a non-zero `msg.value` on this non-payable view
function makes both the IR interpreter AND any aligned native result revert
observably-equally (no storage/event changes, returnValue = none).

This is a concrete `nativeResultsMatchOn`-shaped theorem for an
ERC-20-shaped contract, using only the public revert-path projector and
the `totalSupply` selector match. The successful-execution path requires
the full per-case dispatcher-match-bridge machinery that lives behind the
file-local `simpleStorageNative*MatchBridge` family and is therefore not
duplicated here. -/
theorem erc20Minimal_totalSupply_nativeResultsMatchOn_revert_of_nonzero_value
    (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat)
    (hSelector : tx.functionSelector = 0x18160ddd)
    (hNonzero : tx.msgValue % Compiler.Constants.evmModulus ≠ 0) :
    nativeResultsMatchOn observableSlots
      (interpretIR erc20MinimalIRContract tx state)
      (.ok
        { success := false
          returnValue := none
          finalStorage := state.storage
          finalMappings := storageAsMappings state.storage
          events := state.events }) := by
  have hFind : erc20MinimalIRContract.functions.find?
      (fun fn => fn.selector == tx.functionSelector) = some totalSupplyFunction := by
    simp [erc20MinimalIRContract, totalSupplyFunction, hSelector]
  have hPayable : totalSupplyFunction.payable = false := by
    simp [totalSupplyFunction, erc20MinimalIRContract]
  exact nativeResultsMatchOn_interpretIR_revert_of_nonpayable_nonzero
    erc20MinimalIRContract tx state observableSlots totalSupplyFunction
    hFind hPayable hNonzero

end Contracts.ERC20.Proofs.Native
