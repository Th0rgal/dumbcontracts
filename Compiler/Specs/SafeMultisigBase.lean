/-
  Compiler.Specs.SafeMultisigBase (Scaffold)

  Minimal ContractSpec placeholder for the Safe base contract.
  This will be replaced with a faithful spec that mirrors the
  latest Safe base contract from safe-smart-account.
-/

import Compiler.ContractSpec

namespace Compiler.Specs.SafeMultisigBase

open Compiler.ContractSpec

/-- Placeholder Safe Multisig base spec (storage layout pinned). -/
def safeMultisigBaseSpec : ContractSpec := {
  name := "SafeMultisigBase"
  fields := [
    { name := "singleton", ty := FieldType.address },
    { name := "modules", ty := FieldType.mapping },
    { name := "owners", ty := FieldType.mapping },
    { name := "ownerCount", ty := FieldType.uint256 },
    { name := "threshold", ty := FieldType.uint256 },
    { name := "nonce", ty := FieldType.uint256 },
    { name := "deprecatedDomainSeparator", ty := FieldType.uint256 },
    { name := "signedMessages", ty := FieldType.mapping },
    { name := "approvedHashes", ty := FieldType.mapping }
  ]
  constructor := some {
    params := []
    body := [
      Stmt.setStorage "threshold" (Expr.literal 1)
    ]
  }
  functions := [
    { name := "getThreshold"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "threshold")
      ]
    }
  ]
}

end Compiler.Specs.SafeMultisigBase
