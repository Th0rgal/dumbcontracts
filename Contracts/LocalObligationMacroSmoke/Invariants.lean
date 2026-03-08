import Verity.Specs.Common

namespace Contracts.LocalObligationMacroSmoke.Invariants

open Verity

def slotZeroUnchanged (s s' : ContractState) : Prop :=
  s'.storage 0 = s.storage 0

abbrev context_preserved := Verity.Specs.sameContext

end Contracts.LocalObligationMacroSmoke.Invariants
