import Contracts.Common

namespace Contracts

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract LocalObligationMacroSmoke where
  storage
    initialized : Uint256 := slot 0
    lastValue : Uint256 := slot 1

  constructor () local_obligations [constructor_storage_layout := unchecked "Constructor storage aliasing must be checked separately across deployments."] := do
    pure ()

  function unsafeEdge () local_obligations [manual_delegatecall_refinement := assumed "Caller must separately prove the handwritten assembly path refines the intended state transition."] : Unit := do
    pure ()

  function dischargedEdge (value : Uint256) local_obligations [checked_patch_pack := proved "Patch-pack proof already discharges this handwritten lowering boundary."] : Uint256 := do
    setStorage lastValue value
    return value

end Contracts
