/-
  Compiler.Specs: Declarative Contract Specifications

  This file demonstrates the new declarative contract specification system.
  Each contract is specified once, and IR is generated automatically.

  This replaces the manual IR definitions in Translate.lean.
-/

import Compiler.ContractSpec

namespace Compiler.Specs

open Compiler.ContractSpec

/-!
## SimpleStorage Specification
-/

def simpleStorageSpec : ContractSpec := {
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

def simpleStorageSelectors : List Nat := [0x6057361d, 0x2e64cec1]

/-!
## Counter Specification
-/

def counterSpec : ContractSpec := {
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

def counterSelectors : List Nat := [0xd09de08a, 0x2baeceb7, 0xa87d942c]

/-!
## Owned Specification
-/

def ownedSpec : ContractSpec := {
  name := "Owned"
  fields := [
    { name := "owner", ty := FieldType.address }
  ]
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := [
      Stmt.setStorage "owner" (Expr.constructorArg 0)
    ]
  }
  functions := [
    { name := "transferOwnership"
      params := [{ name := "newOwner", ty := ParamType.address }]
      returnType := none
      body := [
        Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner",
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

def ownedSelectors : List Nat := [0xf2fde38b, 0x893d20e8]

/-!
## Ledger Specification
-/

def ledgerSpec : ContractSpec := {
  name := "Ledger"
  fields := [
    { name := "balances", ty := FieldType.mapping }
  ]
  constructor := none
  functions := [
    { name := "deposit"
      params := [{ name := "amount", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setMapping "balances" Expr.caller
          (Expr.add (Expr.mapping "balances" Expr.caller) (Expr.param "amount")),
        Stmt.stop
      ]
    },
    { name := "withdraw"
      params := [{ name := "amount", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.require
          (Expr.ge (Expr.mapping "balances" Expr.caller) (Expr.param "amount"))
          "Insufficient balance",
        Stmt.setMapping "balances" Expr.caller
          (Expr.sub (Expr.mapping "balances" Expr.caller) (Expr.param "amount")),
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
        Stmt.require
          (Expr.ge (Expr.mapping "balances" Expr.caller) (Expr.param "amount"))
          "Insufficient balance",
        Stmt.setMapping "balances" Expr.caller
          (Expr.sub (Expr.mapping "balances" Expr.caller) (Expr.param "amount")),
        Stmt.setMapping "balances" (Expr.param "to")
          (Expr.add (Expr.mapping "balances" (Expr.param "to")) (Expr.param "amount")),
        Stmt.stop
      ]
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

def ledgerSelectors : List Nat := [0xb6b55f25, 0x2e1a7d4d, 0xa9059cbb, 0xf8b2cb4f]

/-!
## OwnedCounter Specification (Combines Owned + Counter)
-/

def ownedCounterSpec : ContractSpec := {
  name := "OwnedCounter"
  fields := [
    { name := "owner", ty := FieldType.address },
    { name := "count", ty := FieldType.uint256 }
  ]
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := [
      Stmt.setStorage "owner" (Expr.constructorArg 0)
    ]
  }
  functions := [
    { name := "increment"
      params := []
      returnType := none
      body := [
        Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner",
        Stmt.setStorage "count" (Expr.add (Expr.storage "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "decrement"
      params := []
      returnType := none
      body := [
        Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner",
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
        Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner",
        Stmt.setStorage "owner" (Expr.param "newOwner"),
        Stmt.stop
      ]
    }
  ]
}

def ownedCounterSelectors : List Nat := [0xd09de08a, 0x2baeceb7, 0xa87d942c, 0x893d20e8, 0xf2fde38b]

/-!
## SimpleToken Specification (Owned + Balances + Supply)
-/

def simpleTokenSpec : ContractSpec := {
  name := "SimpleToken"
  fields := [
    { name := "owner", ty := FieldType.address },
    { name := "balances", ty := FieldType.mapping },
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
        Stmt.require (Expr.eq Expr.caller (Expr.storage "owner")) "Not owner",
        Stmt.setMapping "balances" (Expr.param "to")
          (Expr.add (Expr.mapping "balances" (Expr.param "to")) (Expr.param "amount")),
        Stmt.setStorage "totalSupply"
          (Expr.add (Expr.storage "totalSupply") (Expr.param "amount")),
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
        Stmt.require
          (Expr.ge (Expr.mapping "balances" Expr.caller) (Expr.param "amount"))
          "Insufficient balance",
        Stmt.setMapping "balances" Expr.caller
          (Expr.sub (Expr.mapping "balances" Expr.caller) (Expr.param "amount")),
        Stmt.setMapping "balances" (Expr.param "to")
          (Expr.add (Expr.mapping "balances" (Expr.param "to")) (Expr.param "amount")),
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

def simpleTokenSelectors : List Nat := [0x40c10f19, 0xa9059cbb, 0x70a08231, 0x18160ddd, 0x8da5cb5b]

/-!
## SafeCounter Specification (Counter with overflow/underflow checks)
-/

-- We need additional expression types for overflow checking
-- For now, use simplified version without full overflow protection
def safeCounterSpec : ContractSpec := {
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
        -- TODO: Add overflow check (current + 1 >= current)
        Stmt.setStorage "count" (Expr.add (Expr.storage "count") (Expr.literal 1)),
        Stmt.stop
      ]
    },
    { name := "decrement"
      params := []
      returnType := none
      body := [
        Stmt.require (Expr.ge (Expr.storage "count") (Expr.literal 1)) "Underflow",
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

def safeCounterSelectors : List Nat := [0xd09de08a, 0x2baeceb7, 0xa87d942c]

/-!
## Generate All Contracts
-/

def allSpecs : List (ContractSpec × List Nat) := [
  (simpleStorageSpec, simpleStorageSelectors),
  (counterSpec, counterSelectors),
  (ownedSpec, ownedSelectors),
  (ledgerSpec, ledgerSelectors),
  (ownedCounterSpec, ownedCounterSelectors),
  (simpleTokenSpec, simpleTokenSelectors),
  (safeCounterSpec, safeCounterSelectors)
]

end Compiler.Specs
