import Contracts.LocalObligationMacroSmoke.Proofs.Basic

namespace Contracts.LocalObligationMacroSmoke.Proofs.Correctness

open Verity
open Contracts.LocalObligationMacroSmoke.Spec
open Contracts.LocalObligationMacroSmoke.Proofs

theorem dischargedEdge_roundtrip (s : ContractState) (value : Uint256) :
  let output := (Contracts.LocalObligationMacroSmoke.dischargedEdge value).run s
  output.fst = value := by
  unfold Contracts.LocalObligationMacroSmoke.dischargedEdge
  simp [Contracts.LocalObligationMacroSmoke.lastValue, Verity.Contract.run, Verity.bind, Bind.bind, Verity.setStorage, Verity.pure, Pure.pure]

end Contracts.LocalObligationMacroSmoke.Proofs.Correctness
