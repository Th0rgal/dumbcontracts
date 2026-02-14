/-
  Unlink Privacy Protocol: Shared Types

  Types shared between the specification (Spec.lean) and
  implementation (UnlinkPool.lean). Having a single definition
  eliminates type mismatches in correctness proofs.
-/

import DumbContracts.Core

namespace DumbContracts.Specs.Unlink

open DumbContracts

/-! ## Core Types -/

abbrev Commitment := Uint256
abbrev NullifierHash := Uint256
abbrev MerkleRoot := Uint256

structure Note where
  npk : Uint256
  token : Uint256
  amount : Uint256
  deriving Repr

end DumbContracts.Specs.Unlink
