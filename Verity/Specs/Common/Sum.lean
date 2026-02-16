/-
  Sum helper functions for proving sum properties.

  This module provides utilities for summing balances over finite address sets.
-/

import Verity.Core
import Verity.EVM.Uint256

namespace Verity.Specs.Common

open Verity
open Verity.Core
open Verity.EVM.Uint256

/-- Sum balances from a mapping over a finite set of addresses -/
def sumBalances (slot : Nat) (addrs : FiniteAddressSet) (balances : Nat → Address → Uint256) : Uint256 :=
  addrs.addresses.sum (fun addr => balances slot addr)

/-- Invariant: only known addresses have non-zero balances -/
def balancesFinite (slot : Nat) (s : ContractState) : Prop :=
  ∀ addr, addr ∉ (s.knownAddresses slot).addresses.elements →
    s.storageMap slot addr = 0

/-- Helper: sum is preserved when adding to known address -/
theorem sumBalances_insert_existing {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256}
    (h : addr ∈ addrs.addresses.elements) :
    sumBalances slot (addrs.insert addr) balances = sumBalances slot addrs balances := by
  unfold sumBalances FiniteAddressSet.insert FiniteSet.insert
  simp [h]

/-- Helper: sum increases when adding balance to new address -/
theorem sumBalances_insert_new {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} {amount : Uint256}
    (h : addr ∉ addrs.addresses.elements)
    (h_zero : balances slot addr = 0) :
    sumBalances slot (addrs.insert addr) (fun s a =>
      if s == slot && a == addr then amount else balances s a) =
    add (sumBalances slot addrs balances) amount := by
  -- This proof requires developing lemmas about:
  -- 1. List.foldl with Uint256 addition
  -- 2. Function extensionality over list elements
  -- 3. Uint256.add commutativity and associativity
  -- This is complex theorem proving work that requires careful development
  sorry  -- Proof requires foldl lemmas - to be completed in Phase 2

/-- Helper: sum changes when updating balance of existing address -/
theorem sumBalances_update_existing {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} {old_amount new_amount : Uint256}
    (h : addr ∈ addrs.addresses.elements)
    (h_old : balances slot addr = old_amount) :
    sumBalances slot addrs (fun s a =>
      if s == slot && a == addr then new_amount else balances s a) =
    add (sub (sumBalances slot addrs balances) old_amount) new_amount := by
  -- Strategy:
  -- 1. Split the sum into addr and the rest
  -- 2. Replace old_amount with new_amount for addr
  -- 3. Recompose using Uint256 arithmetic
  sorry

/-- Helper: foldl of addition over zeros starting from zero gives zero -/
private theorem foldl_add_zero_acc (l : List α) (f : α → Uint256)
    (h : ∀ x ∈ l, f x = 0) (acc : Uint256) :
    l.foldl (fun a x => a + f x) acc = acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have ha : f a = 0 := h a (List.mem_cons_self a t)
    rw [ha, Uint256.add_zero]
    exact ih (fun x hx => h x (List.mem_cons_of_mem a hx)) acc

/-- Helper: sumBalances equals zero when all balances are zero -/
theorem sumBalances_zero_of_all_zero {slot : Nat} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} :
    (∀ addr ∈ addrs.addresses.elements, balances slot addr = 0) →
    sumBalances slot addrs balances = 0 := by
  intro h
  unfold sumBalances FiniteSet.sum
  exact foldl_add_zero_acc addrs.addresses.elements (fun addr => balances slot addr) h 0

/-- Helper: balancesFinite preserved by setMapping (deposit) -/
theorem balancesFinite_preserved_deposit {slot : Nat} (s : ContractState)
    (addr : Address) (amount : Uint256) :
    balancesFinite slot s →
    balancesFinite slot { s with
      storageMap := fun s' a =>
        if s' == slot && a == addr then amount else s.storageMap s' a,
      knownAddresses := fun s' =>
        if s' == slot then (s.knownAddresses s').insert addr
        else s.knownAddresses s' } := by
  -- Revert to sorry for now — this proof requires careful goal inspection
  -- that depends on how simp normalizes the knownAddresses/storageMap ite terms.
  -- The key facts are established: addr' ≠ addr implies the storageMap ite
  -- returns the old value, and addr' ∉ original set implies it's zero.
  sorry

end Verity.Specs.Common
