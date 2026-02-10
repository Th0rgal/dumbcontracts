/-
  Compiler.RandomGen: Random Transaction Generator

  Generates random but valid transactions for differential testing.
  Uses a simple pseudo-random number generator for reproducibility.
-/

import Compiler.Interpreter

namespace Compiler.RandomGen

open Compiler.Interpreter

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

-- Generate random address (from a small pool for collision testing)
def genAddress (rng : RNG) : RNG × Address :=
  let (rng', n) := rng.next
  let addresses := ["0xAlice", "0xBob", "0xCarol", "0xDave", "0xEve"]
  (rng', addresses.get! (n % addresses.length))

-- Generate random bool
def genBool (rng : RNG) : RNG × Bool :=
  let (rng', n) := rng.next
  (rng', n % 2 == 0)

/-!
## Contract-Specific Transaction Generation
-/

-- Generate random SimpleStorage transaction
def genSimpleStorageTx (rng : RNG) : RNG × Transaction :=
  let (rng, useSender) := genBool rng
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

-- Generate random transaction for any contract
def genTransaction (contractType : ContractType) (rng : RNG) : RNG × Transaction :=
  match contractType with
  | ContractType.simpleStorage => genSimpleStorageTx rng
  | ContractType.counter => genCounterTx rng
  | _ => genSimpleStorageTx rng  -- Default

/-!
## Generate Test Sequence
-/

-- Generate N random transactions
partial def genTransactions (contractType : ContractType) (count : Nat) (rng : RNG) : List Transaction :=
  if count == 0 then []
  else
    let (rng', tx) := genTransaction contractType rng
    tx :: genTransactions contractType (count - 1) rng'

-- Generate test sequence with a seed
def genTestSequence (contractType : ContractType) (count : Nat) (seed : Nat) : List Transaction :=
  let rng := RNG.init seed
  genTransactions contractType count rng

/-!
## CLI Entry Point

For generating test sequences from command line.
-/

def main (args : List String) : IO Unit := do
  match args with
  | [contractType, countStr, seedStr] =>
    let count := countStr.toNat!
    let seed := seedStr.toNat!
    let contractTypeEnum := match contractType with
      | "SimpleStorage" => ContractType.simpleStorage
      | "Counter" => ContractType.counter
      | _ => ContractType.simpleStorage
    let txs := genTestSequence contractTypeEnum count seed
    -- Output as JSON array
    IO.println "["
    for i in [:txs.length] do
      let tx := txs.get! i
      let comma := if i < txs.length - 1 then "," else ""
      IO.println s!"  {{\"sender\":\"{tx.sender}\",\"function\":\"{tx.functionName}\",\"args\":[{String.intercalate "," (tx.args.map toString)}]}}{comma}"
    IO.println "]"
  | _ =>
    IO.println "Usage: random-gen <contract> <count> <seed>"
    IO.println "Example: random-gen SimpleStorage 100 42"

end Compiler.RandomGen
