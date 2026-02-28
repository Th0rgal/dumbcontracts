/-
  Compiler.Specs: Declarative Contract Specifications

  Declarative contract specification system.
  Each contract is specified once, and IR is generated automatically.
-/

import Compiler.CompilationModel

namespace Compiler.Specs

open Compiler.CompilationModel

/-!
## Shared Helpers
-/

def requireOwner : Stmt :=
  Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner"

@[reducible] def ownerConstructor : ConstructorSpec := {
  params := [{ name := "initialOwner", ty := ParamType.address }]
  body := [
    Stmt.setStorage "owner" (Expr.constructorArg 0)
  ]
}

/-- Transfer body for mapping-based balance contracts.
    Handles self-transfer safely by computing a zero delta when caller == to. -/
@[reducible] def transferBody (mappingName : String) : List Stmt := [
  -- Pre-load both balances to match EDSL semantics (prevents self-transfer bug)
  Stmt.letVar "senderBal" (Expr.mapping mappingName Expr.caller),
  Stmt.letVar "recipientBal" (Expr.mapping mappingName (Expr.param "to")),
  Stmt.require
    (Expr.ge (Expr.localVar "senderBal") (Expr.param "amount"))
    "Insufficient balance",
  -- If caller == to, delta = 0 so both updates become no-ops.
  Stmt.letVar "sameAddr" (Expr.eq Expr.caller (Expr.param "to")),
  Stmt.letVar "delta" (Expr.sub (Expr.literal 1) (Expr.localVar "sameAddr")),
  Stmt.letVar "amountDelta" (Expr.mul (Expr.param "amount") (Expr.localVar "delta")),
  -- Overflow check: newRecipientBal must be >= recipientBal (wrapping add overflow detection)
  Stmt.letVar "newRecipientBal" (Expr.add (Expr.localVar "recipientBal") (Expr.localVar "amountDelta")),
  Stmt.require (Expr.ge (Expr.localVar "newRecipientBal") (Expr.localVar "recipientBal")) "Recipient balance overflow",
  Stmt.setMapping mappingName Expr.caller
    (Expr.sub (Expr.localVar "senderBal") (Expr.localVar "amountDelta")),
  Stmt.setMapping mappingName (Expr.param "to") (Expr.localVar "newRecipientBal"),
  Stmt.stop
]

/-!
## SimpleStorage Specification
-/

def simpleStorageSpec : CompilationModel := {
  name := "SimpleStorage"
  fields := [
    { name := "storedData", ty := FieldType.uint256 }
  ]
  constructor := none  -- No initialization needed
  functions := [
    { name := "store"
      params := [{ name := "value", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setStorage "storedData" (Expr.param "value"),
        Stmt.stop
      ]
    },
    { name := "retrieve"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "storedData")
      ]
    }
  ]
}


/-!
## Counter Specification
-/

def counterSpec : CompilationModel := {
  name := "Counter"
  fields := [
    { name := "count", ty := FieldType.uint256 }
  ]
  constructor := none
  functions := [
    { name := "increment"
      params := []
      returnType := none
      body := [
        Stmt.setStorage "count" (Expr.add (Expr.storage "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "decrement"
      params := []
      returnType := none
      body := [
        Stmt.setStorage "count" (Expr.sub (Expr.storage "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "getCount"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "count")
      ]
    }
  ]
}


/-!
## Owned Specification
-/

def ownedSpec : CompilationModel := {
  name := "Owned"
  fields := [
    { name := "owner", ty := FieldType.address }
  ]
  constructor := some ownerConstructor
  functions := [
    { name := "transferOwnership"
      params := [{ name := "newOwner", ty := ParamType.address }]
      returnType := none
      body := [
        requireOwner,
        Stmt.setStorage "owner" (Expr.param "newOwner"),
        Stmt.stop
      ]
    },
    { name := "getOwner"
      params := []
      returnType := some FieldType.address
      body := [
        Stmt.return (Expr.storage "owner")
      ]
    }
  ]
}


/-!
## Ledger Specification
-/

def ledgerSpec : CompilationModel := {
  name := "Ledger"
  fields := [
    { name := "balances", ty := FieldType.mappingTyped (.simple .address) }
  ]
  constructor := none
  functions := [
    { name := "deposit"
      params := [{ name := "amount", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.letVar "senderBal" (Expr.mapping "balances" Expr.caller),
        Stmt.setMapping "balances" Expr.caller
          (Expr.add (Expr.localVar "senderBal") (Expr.param "amount")),
        Stmt.stop
      ]
    },
    { name := "withdraw"
      params := [{ name := "amount", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.letVar "senderBal" (Expr.mapping "balances" Expr.caller),
        Stmt.require
          (Expr.ge (Expr.localVar "senderBal") (Expr.param "amount"))
          "Insufficient balance",
        Stmt.setMapping "balances" Expr.caller
          (Expr.sub (Expr.localVar "senderBal") (Expr.param "amount")),
        Stmt.stop
      ]
    },
    { name := "transfer"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      body := transferBody "balances"
    },
    { name := "getBalance"
      params := [{ name := "addr", ty := ParamType.address }]
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.mapping "balances" (Expr.param "addr"))
      ]
    }
  ]
}


/-!
## OwnedCounter Specification (Combines Owned + Counter)
-/

def ownedCounterSpec : CompilationModel := {
  name := "OwnedCounter"
  fields := [
    { name := "owner", ty := FieldType.address },
    { name := "count", ty := FieldType.uint256 }
  ]
  constructor := some ownerConstructor
  functions := [
    { name := "increment"
      params := []
      returnType := none
      body := [
        requireOwner,
        Stmt.setStorage "count" (Expr.add (Expr.storage "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "decrement"
      params := []
      returnType := none
      body := [
        requireOwner,
        Stmt.setStorage "count" (Expr.sub (Expr.storage "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "getCount"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "count")
      ]
    },
    { name := "getOwner"
      params := []
      returnType := some FieldType.address
      body := [
        Stmt.return (Expr.storage "owner")
      ]
    },
    { name := "transferOwnership"
      params := [{ name := "newOwner", ty := ParamType.address }]
      returnType := none
      body := [
        requireOwner,
        Stmt.setStorage "owner" (Expr.param "newOwner"),
        Stmt.stop
      ]
    }
  ]
}


/-!
## SimpleToken Specification (Owned + Balances + Supply)
-/

def simpleTokenSpec : CompilationModel := {
  name := "SimpleToken"
  fields := [
    { name := "owner", ty := FieldType.address },
    { name := "balances", ty := FieldType.mappingTyped (.simple .address) },
    { name := "totalSupply", ty := FieldType.uint256 }
  ]
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := [
      Stmt.setStorage "owner" (Expr.constructorArg 0),
      Stmt.setStorage "totalSupply" (Expr.literal 0)
    ]
  }
  functions := [
    { name := "mint"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        requireOwner,
        -- Checks-before-effects: compute and validate both new values before any mutations
        Stmt.letVar "recipientBal" (Expr.mapping "balances" (Expr.param "to")),
        Stmt.letVar "newBalance" (Expr.add (Expr.localVar "recipientBal") (Expr.param "amount")),
        Stmt.require (Expr.ge (Expr.localVar "newBalance") (Expr.localVar "recipientBal")) "Balance overflow",
        Stmt.letVar "supply" (Expr.storage "totalSupply"),
        Stmt.letVar "newSupply" (Expr.add (Expr.localVar "supply") (Expr.param "amount")),
        Stmt.require (Expr.ge (Expr.localVar "newSupply") (Expr.localVar "supply")) "Supply overflow",
        -- Effects: all checks passed, now apply state mutations
        Stmt.setMapping "balances" (Expr.param "to") (Expr.localVar "newBalance"),
        Stmt.setStorage "totalSupply" (Expr.localVar "newSupply"),
        Stmt.stop
      ]
    },
    { name := "transfer"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      body := transferBody "balances"
    },
    { name := "balanceOf"
      params := [{ name := "addr", ty := ParamType.address }]
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.mapping "balances" (Expr.param "addr"))
      ]
    },
    { name := "totalSupply"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "totalSupply")
      ]
    },
    { name := "owner"
      params := []
      returnType := some FieldType.address
      body := [
        Stmt.return (Expr.storage "owner")
      ]
    }
  ]
}


/-!
## ERC20 Specification (Owner + Balances + Allowances + Supply)

Full ERC-20 token with owner-controlled minting, transfer, approve,
and transferFrom (with infinite allowance when MAX_UINT256).
Uses double-mapping `allowances` field.
-/

/-- Maximum uint256 value (2^256 - 1), used for infinite-allowance semantics. -/
private def maxUint256 : Nat := 2^256 - 1

def erc20Spec : CompilationModel := {
  name := "ERC20"
  fields := [
    { name := "owner", ty := FieldType.address },
    { name := "totalSupply", ty := FieldType.uint256 },
    { name := "balances", ty := FieldType.mappingTyped (.simple .address) },
    { name := "allowances", ty := FieldType.mappingTyped (.nested .address .address) }
  ]
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := [
      Stmt.setStorage "owner" (Expr.constructorArg 0),
      Stmt.setStorage "totalSupply" (Expr.literal 0)
    ]
  }
  functions := [
    { name := "mint"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        requireOwner,
        Stmt.letVar "currentBalance" (Expr.mapping "balances" (Expr.param "to")),
        Stmt.letVar "newBalance" (Expr.add (Expr.localVar "currentBalance") (Expr.param "amount")),
        Stmt.require (Expr.ge (Expr.localVar "newBalance") (Expr.localVar "currentBalance")) "Balance overflow",
        Stmt.letVar "currentSupply" (Expr.storage "totalSupply"),
        Stmt.letVar "newSupply" (Expr.add (Expr.localVar "currentSupply") (Expr.param "amount")),
        Stmt.require (Expr.ge (Expr.localVar "newSupply") (Expr.localVar "currentSupply")) "Supply overflow",
        Stmt.setMapping "balances" (Expr.param "to") (Expr.localVar "newBalance"),
        Stmt.setStorage "totalSupply" (Expr.localVar "newSupply"),
        Stmt.stop
      ]
    },
    { name := "transfer"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.letVar "senderBalance" (Expr.mapping "balances" Expr.caller),
        Stmt.require (Expr.ge (Expr.localVar "senderBalance") (Expr.param "amount")) "Insufficient balance",
        Stmt.ite (Expr.eq Expr.caller (Expr.param "to"))
          [-- self-transfer: no-op
           Stmt.stop]
          [-- different recipient: update both balances
           Stmt.letVar "recipientBalance" (Expr.mapping "balances" (Expr.param "to")),
           Stmt.letVar "newRecipientBalance" (Expr.add (Expr.localVar "recipientBalance") (Expr.param "amount")),
           Stmt.require (Expr.ge (Expr.localVar "newRecipientBalance") (Expr.localVar "recipientBalance")) "Recipient balance overflow",
           Stmt.setMapping "balances" Expr.caller
             (Expr.sub (Expr.localVar "senderBalance") (Expr.param "amount")),
           Stmt.setMapping "balances" (Expr.param "to") (Expr.localVar "newRecipientBalance"),
           Stmt.stop]
      ]
    },
    { name := "approve"
      params := [
        { name := "spender", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.setMapping2 "allowances" Expr.caller (Expr.param "spender") (Expr.param "amount"),
        Stmt.stop
      ]
    },
    { name := "transferFrom"
      params := [
        { name := "from", ty := ParamType.address },
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.letVar "currentAllowance" (Expr.mapping2 "allowances" (Expr.param "from") Expr.caller),
        Stmt.require (Expr.ge (Expr.localVar "currentAllowance") (Expr.param "amount")) "Insufficient allowance",
        Stmt.letVar "fromBalance" (Expr.mapping "balances" (Expr.param "from")),
        Stmt.require (Expr.ge (Expr.localVar "fromBalance") (Expr.param "amount")) "Insufficient balance",
        Stmt.ite (Expr.eq (Expr.param "from") (Expr.param "to"))
          []  -- self-transfer: no balance updates needed
          [-- different: update both balances
           Stmt.letVar "toBalance" (Expr.mapping "balances" (Expr.param "to")),
           Stmt.letVar "newToBalance" (Expr.add (Expr.localVar "toBalance") (Expr.param "amount")),
           Stmt.require (Expr.ge (Expr.localVar "newToBalance") (Expr.localVar "toBalance")) "Recipient balance overflow",
           Stmt.setMapping "balances" (Expr.param "from")
             (Expr.sub (Expr.localVar "fromBalance") (Expr.param "amount")),
           Stmt.setMapping "balances" (Expr.param "to") (Expr.localVar "newToBalance")],
        -- Deduct allowance unless MAX_UINT256 (infinite allowance convention)
        Stmt.ite (Expr.eq (Expr.localVar "currentAllowance") (Expr.literal maxUint256))
          []  -- infinite allowance: no deduction
          [Stmt.setMapping2 "allowances" (Expr.param "from") Expr.caller
             (Expr.sub (Expr.localVar "currentAllowance") (Expr.param "amount"))],
        Stmt.stop
      ]
    },
    { name := "balanceOf"
      params := [{ name := "addr", ty := ParamType.address }]
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.mapping "balances" (Expr.param "addr"))
      ]
    },
    { name := "allowance"
      params := [
        { name := "owner", ty := ParamType.address },
        { name := "spender", ty := ParamType.address }
      ]
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.mapping2 "allowances" (Expr.param "owner") (Expr.param "spender"))
      ]
    },
    { name := "totalSupply"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "totalSupply")
      ]
    },
    { name := "owner"
      params := []
      returnType := some FieldType.address
      body := [
        Stmt.return (Expr.storage "owner")
      ]
    }
  ]
}

/-!
## ERC721 Specification (NFT with approvals and operator support)

Mirrors `Verity/Examples/ERC721.lean`. Features:
- Uint256-keyed mappings (owners, tokenApprovals) via `Expr.mappingUint`
- Double-mapping operator approvals via `Expr.mapping2`/`Stmt.setMapping2`
- Conditional self-transfer via `Stmt.ite`
- Triple-OR authorization check via nested `Expr.logicalOr`
- Owner-gated minting with sequential token IDs
-/

/-- Address mask (2^160 - 1), used for word-to-address conversion. -/
private def addressMask : Nat := 2^160 - 1

def erc721Spec : CompilationModel := {
  name := "ERC721"
  fields := [
    { name := "owner", ty := FieldType.address },
    { name := "totalSupply", ty := FieldType.uint256 },
    { name := "nextTokenId", ty := FieldType.uint256 },
    { name := "balances", ty := FieldType.mappingTyped (.simple .address) },
    { name := "owners", ty := FieldType.mappingTyped (.simple .uint256) },
    { name := "tokenApprovals", ty := FieldType.mappingTyped (.simple .uint256) },
    { name := "operatorApprovals", ty := FieldType.mappingTyped (.nested .address .address) }
  ]
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := [
      Stmt.setStorage "owner" (Expr.constructorArg 0),
      Stmt.setStorage "totalSupply" (Expr.literal 0),
      Stmt.setStorage "nextTokenId" (Expr.literal 0)
    ]
  }
  functions := [
    { name := "balanceOf"
      params := [{ name := "addr", ty := ParamType.address }]
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.mapping "balances" (Expr.param "addr"))
      ]
    },
    { name := "ownerOf"
      params := [{ name := "tokenId", ty := ParamType.uint256 }]
      returnType := some FieldType.address
      body := [
        Stmt.letVar "ownerWord" (Expr.mappingUint "owners" (Expr.param "tokenId")),
        Stmt.require (Expr.gt (Expr.localVar "ownerWord") (Expr.literal 0)) "Token does not exist",
        Stmt.return (Expr.bitAnd (Expr.localVar "ownerWord") (Expr.literal addressMask))
      ]
    },
    { name := "getApproved"
      params := [{ name := "tokenId", ty := ParamType.uint256 }]
      returnType := some FieldType.address
      body := [
        Stmt.letVar "ownerWord" (Expr.mappingUint "owners" (Expr.param "tokenId")),
        Stmt.require (Expr.gt (Expr.localVar "ownerWord") (Expr.literal 0)) "Token does not exist",
        Stmt.letVar "approvedWord" (Expr.mappingUint "tokenApprovals" (Expr.param "tokenId")),
        Stmt.return (Expr.bitAnd (Expr.localVar "approvedWord") (Expr.literal addressMask))
      ]
    },
    { name := "isApprovedForAll"
      params := [
        { name := "ownerAddr", ty := ParamType.address },
        { name := "operator", ty := ParamType.address }
      ]
      returnType := some FieldType.uint256
      body := [
        -- Returns non-zero flag as uint256 (0 or 1 equivalent)
        Stmt.return (Expr.mapping2 "operatorApprovals" (Expr.param "ownerAddr") (Expr.param "operator"))
      ]
    },
    { name := "approve"
      params := [
        { name := "approved", ty := ParamType.address },
        { name := "tokenId", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        -- Inline ownerOf: check token exists
        Stmt.letVar "ownerWord" (Expr.mappingUint "owners" (Expr.param "tokenId")),
        Stmt.require (Expr.gt (Expr.localVar "ownerWord") (Expr.literal 0)) "Token does not exist",
        -- Require caller is token owner
        Stmt.require (Expr.eq Expr.caller
          (Expr.bitAnd (Expr.localVar "ownerWord") (Expr.literal addressMask))) "Not token owner",
        Stmt.setMappingUint "tokenApprovals" (Expr.param "tokenId") (Expr.param "approved"),
        Stmt.stop
      ]
    },
    { name := "setApprovalForAll"
      params := [
        { name := "operator", ty := ParamType.address },
        { name := "approved", ty := ParamType.bool }
      ]
      returnType := none
      body := [
        Stmt.setMapping2 "operatorApprovals" Expr.caller (Expr.param "operator") (Expr.param "approved"),
        Stmt.stop
      ]
    },
    { name := "mint"
      params := [{ name := "to", ty := ParamType.address }]
      returnType := some FieldType.uint256
      body := [
        requireOwner,
        Stmt.require (Expr.gt (Expr.param "to") (Expr.literal 0)) "Invalid recipient",
        Stmt.letVar "tokenId" (Expr.storage "nextTokenId"),
        -- Check token not already minted
        Stmt.letVar "currentOwnerWord" (Expr.mappingUint "owners" (Expr.localVar "tokenId")),
        Stmt.require (Expr.eq (Expr.localVar "currentOwnerWord") (Expr.literal 0)) "Token already minted",
        -- Update recipient balance
        Stmt.letVar "recipientBalance" (Expr.mapping "balances" (Expr.param "to")),
        Stmt.letVar "newRecipientBalance" (Expr.add (Expr.localVar "recipientBalance") (Expr.literal 1)),
        Stmt.require (Expr.ge (Expr.localVar "newRecipientBalance") (Expr.localVar "recipientBalance")) "Balance overflow",
        -- Update supply
        Stmt.letVar "currentSupply" (Expr.storage "totalSupply"),
        Stmt.letVar "newSupply" (Expr.add (Expr.localVar "currentSupply") (Expr.literal 1)),
        Stmt.require (Expr.ge (Expr.localVar "newSupply") (Expr.localVar "currentSupply")) "Supply overflow",
        -- Write storage
        Stmt.setMappingUint "owners" (Expr.localVar "tokenId") (Expr.param "to"),
        Stmt.setMapping "balances" (Expr.param "to") (Expr.localVar "newRecipientBalance"),
        Stmt.setStorage "totalSupply" (Expr.localVar "newSupply"),
        Stmt.setStorage "nextTokenId" (Expr.add (Expr.localVar "tokenId") (Expr.literal 1)),
        Stmt.return (Expr.localVar "tokenId")
      ]
    },
    { name := "transferFrom"
      params := [
        { name := "from", ty := ParamType.address },
        { name := "to", ty := ParamType.address },
        { name := "tokenId", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.require (Expr.gt (Expr.param "to") (Expr.literal 0)) "Invalid recipient",
        -- Inline ownerOf: check token exists
        Stmt.letVar "ownerWord" (Expr.mappingUint "owners" (Expr.param "tokenId")),
        Stmt.require (Expr.gt (Expr.localVar "ownerWord") (Expr.literal 0)) "Token does not exist",
        -- Check from == tokenOwner
        Stmt.letVar "tokenOwner" (Expr.bitAnd (Expr.localVar "ownerWord") (Expr.literal addressMask)),
        Stmt.require (Expr.eq (Expr.localVar "tokenOwner") (Expr.param "from")) "From is not owner",
        -- Authorization: sender == from || approved == sender || operatorApproval != 0
        Stmt.letVar "approvedWord" (Expr.mappingUint "tokenApprovals" (Expr.param "tokenId")),
        Stmt.letVar "operatorFlag" (Expr.mapping2 "operatorApprovals" (Expr.param "from") Expr.caller),
        Stmt.letVar "authorized" (Expr.logicalOr
          (Expr.logicalOr
            (Expr.eq Expr.caller (Expr.param "from"))
            (Expr.eq (Expr.localVar "approvedWord") Expr.caller))
          (Expr.gt (Expr.localVar "operatorFlag") (Expr.literal 0))),
        Stmt.require (Expr.localVar "authorized") "Not authorized",
        -- Conditional balance update
        Stmt.ite (Expr.eq (Expr.param "from") (Expr.param "to"))
          []  -- self-transfer: no balance change
          [-- different recipient: update both balances
           Stmt.letVar "fromBalance" (Expr.mapping "balances" (Expr.param "from")),
           Stmt.require (Expr.ge (Expr.localVar "fromBalance") (Expr.literal 1)) "Insufficient balance",
           Stmt.letVar "toBalance" (Expr.mapping "balances" (Expr.param "to")),
           Stmt.letVar "newToBalance" (Expr.add (Expr.localVar "toBalance") (Expr.literal 1)),
           Stmt.require (Expr.ge (Expr.localVar "newToBalance") (Expr.localVar "toBalance")) "Balance overflow",
           Stmt.setMapping "balances" (Expr.param "from")
             (Expr.sub (Expr.localVar "fromBalance") (Expr.literal 1)),
           Stmt.setMapping "balances" (Expr.param "to") (Expr.localVar "newToBalance")],
        -- Update ownership and clear approval
        Stmt.setMappingUint "owners" (Expr.param "tokenId") (Expr.param "to"),
        Stmt.setMappingUint "tokenApprovals" (Expr.param "tokenId") (Expr.literal 0),
        Stmt.stop
      ]
    },
    { name := "totalSupply"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "totalSupply")
      ]
    },
    { name := "owner"
      params := []
      returnType := some FieldType.address
      body := [
        Stmt.return (Expr.storage "owner")
      ]
    }
  ]
}

/-!
## CryptoHash Specification (External Library Linking Demo)

Demonstrates `Expr.externalCall` for linking external Yul libraries at
compile time.  The EDSL placeholder in `Verity/Examples/CryptoHash.lean`
uses simple addition; the CompilationModel below calls the real library
functions (`PoseidonT3_hash`, `PoseidonT4_hash`) which are injected by
the Linker when you pass `--link examples/external-libs/PoseidonT3.yul`.
-/

def cryptoHashSpec : CompilationModel := {
  name := "CryptoHash"
  fields := [
    { name := "lastHash", ty := FieldType.uint256 }
  ]
  constructor := none
  externals := [
    { name := "PoseidonT3_hash"
      params := [ParamType.uint256, ParamType.uint256]
      returnType := some ParamType.uint256
      axiomNames := ["poseidon_t3_deterministic", "poseidon_t3_collision_resistant"] },
    { name := "PoseidonT4_hash"
      params := [ParamType.uint256, ParamType.uint256, ParamType.uint256]
      returnType := some ParamType.uint256
      axiomNames := ["poseidon_t4_deterministic", "poseidon_t4_collision_resistant"] }
  ]
  functions := [
    { name := "storeHashTwo"
      params := [
        { name := "a", ty := ParamType.uint256 },
        { name := "b", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.letVar "h" (Expr.externalCall "PoseidonT3_hash" [Expr.param "a", Expr.param "b"]),
        Stmt.setStorage "lastHash" (Expr.localVar "h"),
        Stmt.stop
      ]
    },
    { name := "storeHashThree"
      params := [
        { name := "a", ty := ParamType.uint256 },
        { name := "b", ty := ParamType.uint256 },
        { name := "c", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.letVar "h" (Expr.externalCall "PoseidonT4_hash" [Expr.param "a", Expr.param "b", Expr.param "c"]),
        Stmt.setStorage "lastHash" (Expr.localVar "h"),
        Stmt.stop
      ]
    },
    { name := "getLastHash"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "lastHash")
      ]
    }
  ]
}


/-!
## SafeCounter Specification (Counter with overflow/underflow checks)
-/
def safeCounterSpec : CompilationModel := {
  name := "SafeCounter"
  fields := [
    { name := "count", ty := FieldType.uint256 }
  ]
  constructor := none
  functions := [
    { name := "increment"
      params := []
      returnType := none
      body := [
        -- Overflow check: require (count + 1 > count)
        -- On overflow, MAX_UINT + 1 = 0, which is NOT > MAX_UINT, so this will revert
        Stmt.letVar "count" (Expr.storage "count"),
        Stmt.letVar "newCount" (Expr.add (Expr.localVar "count") (Expr.literal 1)),
        Stmt.require (Expr.gt (Expr.localVar "newCount") (Expr.localVar "count")) "Overflow in increment",
        Stmt.setStorage "count" (Expr.localVar "newCount"),
        Stmt.stop
      ]
    },
    { name := "decrement"
      params := []
      returnType := none
      body := [
        Stmt.letVar "count" (Expr.storage "count"),
        Stmt.require (Expr.ge (Expr.localVar "count") (Expr.literal 1)) "Underflow in decrement",
        Stmt.setStorage "count" (Expr.sub (Expr.localVar "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "getCount"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "count")
      ]
    }
  ]
}


/-!
## Generate All Contracts

`allSpecs` lists every contract that compiles without external dependencies.
`cryptoHashSpec` is excluded because it requires `--link` flags for external
Yul libraries (PoseidonT3/T4). Use `lake exe verity-compiler --link ...` to
compile it separately.

**Adding a new contract**: After adding `myCompilationModel` here, also ensure
each function's selector is pre-computed in `Compiler/Selectors.lean` via
`computeSelectors`. The compiler will fail at runtime if a function has no
matching selector.
-/

def allSpecs : List CompilationModel := [
  simpleStorageSpec,
  counterSpec,
  ownedSpec,
  ledgerSpec,
  ownedCounterSpec,
  simpleTokenSpec,
  safeCounterSpec,
  erc20Spec,
  erc721Spec
]

end Compiler.Specs
