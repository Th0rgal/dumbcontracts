/-
  State invariants for Ledger contract.
-/

import Verity.Core
import Verity.Specs.Common

namespace Verity.Specs.Ledger

open Verity

/-! ## State Invariants -/

/-- Well-formed state -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""

/-- Context preserved across operations -/
abbrev context_preserved := Specs.sameContext

/-- Non-mapping storage unchanged by all Ledger operations -/
def non_mapping_storage_unchanged (s s' : ContractState) : Prop :=
  s'.storage = s.storage ∧ s'.storageAddr = s.storageAddr

end Verity.Specs.Ledger
