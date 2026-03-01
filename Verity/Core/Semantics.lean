import Verity.Core

namespace Verity

abbrev World := ContractState
abbrev Exit (α : Type) := ContractResult α

structure Env where
  sender : Address
  thisAddress : Address
  msgValue : Uint256
  blockTimestamp : Uint256
  deriving Repr

def Env.ofWorld (w : World) : Env where
  sender := w.sender
  thisAddress := w.thisAddress
  msgValue := w.msgValue
  blockTimestamp := w.blockTimestamp

def World.withEnv (w : World) (env : Env) : World :=
  { w with
    sender := env.sender
    thisAddress := env.thisAddress
    msgValue := env.msgValue
    blockTimestamp := env.blockTimestamp
  }

end Verity
