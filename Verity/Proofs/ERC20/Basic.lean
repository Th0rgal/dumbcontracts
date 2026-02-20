/-
  Basic proofs for ERC20 foundation scaffold.
-/

import Verity.Specs.ERC20.Spec
import Verity.Examples.ERC20
import Verity.Proofs.Stdlib.Math

namespace Verity.Proofs.ERC20

open Verity
open Verity.Specs.ERC20
open Verity.Examples.ERC20
open Verity.Stdlib.Math (MAX_UINT256 requireSomeUint)
open Verity.Proofs.Stdlib.Math (safeAdd_some)

/-- `constructor` sets owner slot 0 and initializes supply slot 1. -/
theorem constructor_meets_spec (s : ContractState) (initialOwner : Address) :
    constructor_spec initialOwner s ((constructor initialOwner).runState s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [constructor, owner, setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]
  · simp [constructor, totalSupply, setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]
  · intro slot h_neq
    simp [constructor, owner, setStorageAddr, setStorage, Contract.runState, Verity.bind,
      Bind.bind, h_neq]
  · intro slot h_neq
    simp [constructor, owner, totalSupply, setStorageAddr, setStorage, Contract.runState,
      Verity.bind, Bind.bind, h_neq]
  · simp [Specs.sameStorageMap, constructor, owner, totalSupply, setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageMap2, constructor, owner, totalSupply, setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameContext, constructor, owner, totalSupply, setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]

/-- `approve` writes allowance(sender, spender) and leaves other state unchanged. -/
theorem approve_meets_spec (s : ContractState) (spender : Address) (amount : Uint256) :
    approve_spec s.sender spender amount s ((approve spender amount).runState s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [approve, allowances, setMapping2, msgSender, Contract.runState, Verity.bind, Bind.bind]
  · intro o' sp' h_neq
    simp [approve, allowances, setMapping2, msgSender, Contract.runState, Verity.bind, Bind.bind,
      h_neq]
  · intro sp' h_neq
    simp [approve, allowances, setMapping2, msgSender, Contract.runState, Verity.bind, Bind.bind,
      h_neq]
  · simp [Specs.sameStorage, approve, allowances, setMapping2, msgSender,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageAddr, approve, allowances, setMapping2, msgSender,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageMap, approve, allowances, setMapping2, msgSender,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameContext, approve, allowances, setMapping2, msgSender,
      Contract.runState, Verity.bind, Bind.bind]

/-- `balanceOf` returns the value stored in balances slot 2 for `addr`. -/
theorem balanceOf_meets_spec (s : ContractState) (addr : Address) :
    balanceOf_spec addr ((balanceOf addr).runValue s) s := by
  simp [balanceOf, balanceOf_spec, getMapping, Contract.runValue, balances]

/-- `allowanceOf` returns the value stored in allowances slot 3 for `(owner, spender)`. -/
theorem allowanceOf_meets_spec (s : ContractState) (ownerAddr spender : Address) :
    allowance_spec ownerAddr spender ((allowanceOf ownerAddr spender).runValue s) s := by
  simp [allowanceOf, allowance_spec, getMapping2, Contract.runValue, allowances]

/-- `getTotalSupply` returns slot 1. -/
theorem totalSupply_meets_spec (s : ContractState) :
    totalSupply_spec ((getTotalSupply).runValue s) s := by
  simp [getTotalSupply, totalSupply_spec, getStorage, Contract.runValue, totalSupply]

/-- `getOwner` returns owner slot 0. -/
theorem getOwner_meets_spec (s : ContractState) :
    getOwner_spec ((getOwner).runValue s) s := by
  simp [getOwner, getOwner_spec, getStorageAddr, Contract.runValue, owner]

/-- Helper: unfold `mint` on the successful owner/non-overflow path. -/
private theorem mint_unfold (s : ContractState) (to : Address) (amount : Uint256)
    (h_owner : s.sender = s.storageAddr 0)
    (h_no_bal_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
    (h_no_sup_overflow : (s.storage 1 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    (mint to amount).run s = ContractResult.success ()
      { storage := fun slot =>
          if slot == 1 then EVM.Uint256.add (s.storage 1) amount else s.storage slot,
        storageAddr := s.storageAddr,
        storageMap := fun slot addr =>
          if (slot == 2 && addr == to) = true then EVM.Uint256.add (s.storageMap 2 to) amount
          else s.storageMap slot addr,
        storageMapUint := s.storageMapUint,
        storageMap2 := s.storageMap2,
        sender := s.sender,
        thisAddress := s.thisAddress,
        msgValue := s.msgValue,
        blockTimestamp := s.blockTimestamp,
        knownAddresses := fun slot =>
          if slot == 2 then (s.knownAddresses slot).insert to else s.knownAddresses slot,
        events := s.events } := by
  have h_safe_bal := safeAdd_some (s.storageMap 2 to) amount h_no_bal_overflow
  have h_safe_sup := safeAdd_some (s.storage 1) amount h_no_sup_overflow
  simp only [mint, onlyOwner, isOwner, owner, balances, totalSupply,
    msgSender, getStorageAddr, getStorage, getMapping, setMapping, setStorage,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_owner, beq_self_eq_true, ite_true]
  unfold requireSomeUint
  rw [h_safe_bal]
  simp only [Verity.pure, Pure.pure, Verity.bind, Bind.bind,
    getStorage, Contract.run, ContractResult.snd, ContractResult.fst]
  rw [h_safe_sup]
  simp only [Verity.pure, Pure.pure, Verity.bind, Bind.bind,
    setMapping, setStorage, Contract.run, ContractResult.snd, ContractResult.fst]
  simp only [HAdd.hAdd, Add.add, h_owner]

/-- `mint` satisfies `mint_spec` under owner and no-overflow preconditions. -/
theorem mint_meets_spec_when_owner (s : ContractState) (to : Address) (amount : Uint256)
    (h_owner : s.sender = s.storageAddr 0)
    (h_no_bal_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
    (h_no_sup_overflow : (s.storage 1 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    mint_spec to amount s ((mint to amount).runState s) := by
  have h_unfold := mint_unfold s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  simp only [Contract.runState, mint_spec]
  rw [show (mint to amount) s = (mint to amount).run s from rfl, h_unfold]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mint_spec, ContractResult.snd, beq_iff_eq]
  · simp [mint_spec, ContractResult.snd, beq_iff_eq]
  · refine ⟨?_, ?_⟩
    · intro addr h_ne
      simp [mint_spec, ContractResult.snd, beq_iff_eq, h_ne]
    · intro slot h_ne addr
      simp [mint_spec, ContractResult.snd, beq_iff_eq, h_ne]
  · intro slot h_ne
    simp [mint_spec, ContractResult.snd, h_ne]
  · rfl
  · rfl
  · exact Specs.sameContext_rfl _

/-- Under successful-owner assumptions, `mint` increases recipient balance by `amount`. -/
theorem mint_increases_balance_when_owner (s : ContractState) (to : Address) (amount : Uint256)
    (h_owner : s.sender = s.storageAddr 0)
    (h_no_bal_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
    (h_no_sup_overflow : (s.storage 1 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    ((mint to amount).runState s).storageMap 2 to = EVM.Uint256.add (s.storageMap 2 to) amount := by
  have h := mint_meets_spec_when_owner s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  exact h.1

/-- Under successful-owner assumptions, `mint` increases total supply by `amount`. -/
theorem mint_increases_supply_when_owner (s : ContractState) (to : Address) (amount : Uint256)
    (h_owner : s.sender = s.storageAddr 0)
    (h_no_bal_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
    (h_no_sup_overflow : (s.storage 1 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    ((mint to amount).runState s).storage 1 = EVM.Uint256.add (s.storage 1) amount := by
  have h := mint_meets_spec_when_owner s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  exact h.2.1

end Verity.Proofs.ERC20
