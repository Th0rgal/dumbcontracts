import Verity.Specs.Common
import Contracts.LocalObligationMacroSmoke.LocalObligationMacroSmoke

namespace Contracts.LocalObligationMacroSmoke.Spec

open Verity

def unsafeEdge_spec (s s' : ContractState) : Prop :=
  s' = s

def dischargedEdge_spec (value result : Uint256) (_s s' : ContractState) : Prop :=
  result = value ∧ s'.storage 1 = value

end Contracts.LocalObligationMacroSmoke.Spec
