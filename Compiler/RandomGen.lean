/-
  Compiler.RandomGen: Random Transaction Generator

  Generates random but valid transactions for differential testing.
  Uses a simple pseudo-random number generator for reproducibility.
-/

import DumbContracts.Core
import Compiler.DiffTestTypes
import Compiler.Hex

namespace Compiler.RandomGen

open DumbContracts
open Compiler.DiffTestTypes
open Compiler.Hex

/-!
## Simple PRNG

Linear Congruential Generator for reproducible randomness.
-/

structure RNG where
  seed : Nat
  deriving Repr

def RNG.next (rng : RNG) : RNG × Nat :=
  let a := 1103515245
  let c := 12345
  let m := 2^31
  let newSeed := (a * rng.seed + c) % m
  ({ seed := newSeed }, newSeed)

def RNG.init (seed : Nat) : RNG := { seed := seed }

/-!
## Random Value Generation
-/

-- Generate random uint256 (bounded for practical testing)
def genUint256 (rng : RNG) : RNG × Nat :=
  let (rng', n) := rng.next
  (rng', n % 1000000)  -- Keep values reasonable for testing

-- Convert Address to Nat for calldata args (keeps parity with Interpreter)
private def addressToNatNormalized (addr : Address) : Nat :=
  addressToNat (normalizeAddress addr)

-- Generate random address (from a small pool for collision testing)
def genAddress (rng : RNG) : RNG × Address :=
  let (rng', n) := rng.next
  let addresses := ["0xalice", "0xbob", "0xcarol", "0xdave", "0xeve"]
  (rng', normalizeAddress (addresses.get! (n % addresses.length)))

-- Generate random bool
def genBool (rng : RNG) : RNG × Bool :=
  let (rng', n) := rng.next
  (rng', n % 2 == 0)

-- Convert Address to Nat for calldata args (keeps parity with Interpreter)

/-!
## Contract-Specific Transaction Generation
-/

-- Generate random SimpleStorage transaction
def genSimpleStorageTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, useStore) := genBool rng
  if useStore then
    let (rng, value) := genUint256 rng
    (rng, { sender := sender, functionName := "store", args := [value] })
  else
    (rng, { sender := sender, functionName := "retrieve", args := [] })

-- Generate random Counter transaction
def genCounterTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, choice) := genUint256 rng
  match choice % 3 with
  | 0 => (rng, { sender := sender, functionName := "increment", args := [] })
  | 1 => (rng, { sender := sender, functionName := "decrement", args := [] })
  | _ => (rng, { sender := sender, functionName := "getCount", args := [] })

-- Generate random SafeCounter transaction
def genSafeCounterTx (rng : RNG) : RNG × Transaction :=
  genCounterTx rng

-- Generate random Owned transaction
def genOwnedTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, choice) := genUint256 rng
  if choice % 2 == 0 then
    (rng, { sender := sender, functionName := "getOwner", args := [] })
  else
    let (rng, newOwner) := genAddress rng
    (rng, { sender := sender, functionName := "transferOwnership", args := [addressToNatNormalized newOwner] })

-- Generate random Ledger transaction
def genLedgerTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, choice) := genUint256 rng
  match choice % 4 with
  | 0 =>
      let (rng, amount) := genUint256 rng
      (rng, { sender := sender, functionName := "deposit", args := [amount] })
  | 1 =>
      let (rng, amount) := genUint256 rng
      (rng, { sender := sender, functionName := "withdraw", args := [amount] })
  | 2 =>
      let (rng, toAddr) := genAddress rng
      let (rng, amount) := genUint256 rng
      (rng, { sender := sender, functionName := "transfer", args := [addressToNatNormalized toAddr, amount] })
  | _ =>
      let (rng, addr) := genAddress rng
      (rng, { sender := sender, functionName := "getBalance", args := [addressToNatNormalized addr] })

-- Generate random OwnedCounter transaction
def genOwnedCounterTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, choice) := genUint256 rng
  match choice % 5 with
  | 0 => (rng, { sender := sender, functionName := "increment", args := [] })
  | 1 => (rng, { sender := sender, functionName := "decrement", args := [] })
  | 2 => (rng, { sender := sender, functionName := "getCount", args := [] })
  | 3 => (rng, { sender := sender, functionName := "getOwner", args := [] })
  | _ =>
      let (rng, newOwner) := genAddress rng
      (rng, { sender := sender, functionName := "transferOwnership", args := [addressToNatNormalized newOwner] })

-- Generate random SimpleToken transaction
def genSimpleTokenTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, choice) := genUint256 rng
  match choice % 5 with
  | 0 =>
      let (rng, toAddr) := genAddress rng
      let (rng, amount) := genUint256 rng
      (rng, { sender := sender, functionName := "mint", args := [addressToNatNormalized toAddr, amount] })
  | 1 =>
      let (rng, toAddr) := genAddress rng
      let (rng, amount) := genUint256 rng
      (rng, { sender := sender, functionName := "transfer", args := [addressToNatNormalized toAddr, amount] })
  | 2 =>
      let (rng, addr) := genAddress rng
      (rng, { sender := sender, functionName := "balanceOf", args := [addressToNatNormalized addr] })
  | 3 =>
      (rng, { sender := sender, functionName := "totalSupply", args := [] })
  | _ =>
      (rng, { sender := sender, functionName := "owner", args := [] })

-- Generate random transaction for any contract
def genTransaction (contractType : ContractType) (rng : RNG) : Except String (RNG × Transaction) :=
  match contractType with
  | ContractType.simpleStorage => Except.ok (genSimpleStorageTx rng)
  | ContractType.counter => Except.ok (genCounterTx rng)
  | ContractType.safeCounter => Except.ok (genSafeCounterTx rng)
  | ContractType.owned => Except.ok (genOwnedTx rng)
  | ContractType.ledger => Except.ok (genLedgerTx rng)
  | ContractType.ownedCounter => Except.ok (genOwnedCounterTx rng)
  | ContractType.simpleToken => Except.ok (genSimpleTokenTx rng)

/-!
## Generate Test Sequence
-/

-- Generate N random transactions
partial def genTransactions (contractType : ContractType) (count : Nat) (rng : RNG) : Except String (List Transaction) :=
  if count == 0 then
    Except.ok []
  else
    match genTransaction contractType rng with
    | Except.error msg => Except.error msg
    | Except.ok (rng', tx) =>
        match genTransactions contractType (count - 1) rng' with
        | Except.ok rest => Except.ok (tx :: rest)
        | Except.error msg => Except.error msg

-- Generate test sequence with a seed
def genTestSequence (contractType : ContractType) (count : Nat) (seed : Nat) : Except String (List Transaction) :=
  let rng := RNG.init seed
  genTransactions contractType count rng

end Compiler.RandomGen

/-!
## CLI Entry Point

For generating test sequences from command line.
-/

open Compiler.RandomGen
open Compiler.DiffTestTypes

def main (args : List String) : IO Unit := do
  match args with
  | [contractType, countStr, seedStr] =>
    let count := countStr.toNat!
    let seed := seedStr.toNat!
    let contractTypeEnum? : Option ContractType := match contractType with
      | "SimpleStorage" => some ContractType.simpleStorage
      | "Counter" => some ContractType.counter
      | "Owned" => some ContractType.owned
      | "Ledger" => some ContractType.ledger
      | "OwnedCounter" => some ContractType.ownedCounter
      | "SimpleToken" => some ContractType.simpleToken
      | "SafeCounter" => some ContractType.safeCounter
      | _ => none
    match contractTypeEnum? with
    | some contractTypeEnum =>
      match genTestSequence contractTypeEnum count seed with
      | Except.error msg =>
          throw <| IO.userError msg
      | Except.ok txs =>
          -- Output as JSON array
          IO.println "["
          let mut isFirst := true
          for tx in txs do
            if !isFirst then IO.println ","
            let argsStr := String.intercalate "," (tx.args.map toString)
            let jsonStr := "  {" ++ "\"sender\":\"" ++ tx.sender ++ "\",\"function\":\"" ++ tx.functionName ++ "\",\"args\":[" ++ argsStr ++ "]}"
            IO.print jsonStr
            isFirst := false
          IO.println ""
          IO.println "]"
    | none =>
      throw <| IO.userError
        s!"Unknown contract type: {contractType}. Supported: SimpleStorage, Counter, Owned, Ledger, OwnedCounter, SimpleToken, SafeCounter"
  | _ =>
    IO.println "Usage: random-gen <contract> <count> <seed>"
    IO.println "Example: random-gen SimpleStorage 100 42"
