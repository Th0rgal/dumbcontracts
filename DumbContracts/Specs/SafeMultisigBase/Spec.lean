/-
  Formal specifications for Safe Multisig base operations (Scaffold).

  These specs are intentionally minimal placeholders. They will be
  expanded to match the Safe base contract behavior precisely.
-/

import DumbContracts.Core
import DumbContracts.Examples.SafeMultisigBase

namespace DumbContracts.Specs.SafeMultisigBase

open DumbContracts
open DumbContracts.Examples.SafeMultisigBase

/-- Upstream Safe repo pin (for spec + bytecode parity). -/
def upstreamRepo : String := "safe-fndn/safe-smart-account"

/-- Upstream release tag targeted for this proof. -/
def upstreamTag : String := "v1.5.0"

/-- Upstream commit for the pinned Safe base contract. -/
def upstreamCommit : String := "dc437e8"

/-- Path to the base contract within the upstream repo. -/
def upstreamSafeSolPath : String := "contracts/Safe.sol"

/-- Base contract name in the upstream repo. -/
def upstreamBaseContractName : String := "Safe"

/-- Solidity pragma range in the pinned Safe base contract. -/
def upstreamPragmaRange : String := ">=0.7.0 <0.9.0"

/-- Safe contract version constant in the pinned source. -/
def upstreamVersionString : String := "1.5.0"

/-- SHA256 of the pinned Safe.sol source snapshot. -/
def upstreamSafeSolSha256 : String :=
  "4b54dce0ad9d9c1264ecd5c146c82b7bc17d24f981bd42525487be3bf6a40366"

/-- Constructor spec: Safe singleton initializes threshold = 1 and preserves all other state. -/
def constructor_spec (s s' : ContractState) : Prop :=
  s'.storage 4 = 1 ∧
  (∀ slot : Nat, slot ≠ 4 → s'.storage slot = s.storage slot) ∧
  s'.storageAddr = s.storageAddr ∧
  s'.storageMap = s.storageMap ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp

/-- Getter spec: threshold equals current storage slot 4. -/
def getThreshold_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 4

end DumbContracts.Specs.SafeMultisigBase
