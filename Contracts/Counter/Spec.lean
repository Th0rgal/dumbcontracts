/-
  Formal specifications for Counter operations.
-/

import Verity.Specs.Common
import Verity.Macro
import Verity.EVM.Uint256
import Contracts.Counter.Counter

namespace Contracts.Counter.Spec

open Verity
open Verity.Specs
open Contracts.Counter
open Verity.EVM.Uint256

/-! ## Operation Specifications -/

-- Increment: increases count by 1
#gen_spec increment_spec (0, (fun st => add (st.storage 0) 1), sameAddrMapContext)

-- Decrement: decreases count by 1
#gen_spec decrement_spec (0, (fun st => sub (st.storage 0) 1), sameAddrMapContext)

/-- getCount: returns the current count -/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

/-! ## Combined Specifications -/

/-- Increment followed by getCount returns the incremented value -/
def increment_getCount_spec (s : ContractState) (result : Uint256) : Prop :=
  result = add (s.storage 0) 1

/-- Decrement followed by getCount returns the decremented value -/
def decrement_getCount_spec (s : ContractState) (result : Uint256) : Prop :=
  result = sub (s.storage 0) 1

/-- Increment then decrement returns to original value -/
def increment_decrement_cancel (s s' : ContractState) : Prop :=
  s'.storage 0 = s.storage 0

/-- Two increments add 2 to the count -/
def two_increments_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = add (add (s.storage 0) 1) 1

end Contracts.Counter.Spec
