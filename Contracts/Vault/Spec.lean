import Verity.Specs.Common
import Verity.Specs.Common.Sum
import Verity.Macro
import Verity.EVM.Uint256
import Contracts.Vault.Vault

namespace Contracts.Vault.Spec

open Verity
open Verity.Specs
open Contracts.Vault
open Verity.EVM.Uint256
open Verity.Specs.Common (sumBalances balancesFinite)

def storageUnchangedExceptAssetSlots (s s' : ContractState) : Prop :=
  ∀ slotIdx : Nat, slotIdx ≠ 0 → slotIdx ≠ 1 → s'.storage slotIdx = s.storage slotIdx

def sameStorageExceptAssetSlots (s s' : ContractState) : Prop :=
  storageUnchangedExceptAssetSlots s s' ∧
  Specs.sameStorageAddr s s' ∧
  Specs.sameContext s s'

#gen_spec_map deposit_spec for (assets : Uint256)
  (2, s.sender, (fun st => add (st.storageMap 2 st.sender) assets),
    sameStorageExceptAssetSlots)

#gen_spec_map withdraw_spec for (shares : Uint256)
  (2, s.sender, (fun st => sub (st.storageMap 2 st.sender) shares),
    sameStorageExceptAssetSlots)

def balanceOf_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 2 addr

def totalAssets_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

def totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

def totalShares (s : ContractState) : Uint256 :=
  sumBalances 2 (s.knownAddresses 2) s.storageMap

def deposit_share_sum_equation (assets : Uint256) (s s' : ContractState) : Prop :=
  totalShares s' = add (totalShares s) assets

def withdraw_share_sum_equation (shares : Uint256) (s s' : ContractState) : Prop :=
  totalShares s' = sub (totalShares s) shares

def assets_supply_synced (s : ContractState) : Prop :=
  s.storage 0 = s.storage 1

end Contracts.Vault.Spec
