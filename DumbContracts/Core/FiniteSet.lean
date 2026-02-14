/-
  Minimal finite set implementation for address tracking.

  This module provides a simple finite set structure to enable
  proving sum properties over contract balances.
-/

namespace DumbContracts.Core

/-- A finite set implemented as a list without duplicates -/
structure FiniteSet (α : Type) [BEq α] where
  elements : List α
  nodup : elements.Nodup
  deriving Repr

namespace FiniteSet

variable {α : Type} [BEq α]

/-- Create an empty finite set -/
def empty : FiniteSet α :=
  ⟨[], List.nodup_nil⟩

/-- Check if an element is in the set -/
def mem (a : α) (s : FiniteSet α) : Bool :=
  a ∈ s.elements

instance : Membership α (FiniteSet α) where
  mem a s := s.mem a

/-- Insert an element into the set (maintains no duplicates) -/
def insert (a : α) (s : FiniteSet α) : FiniteSet α :=
  if a ∈ s.elements then
    s
  else
    ⟨a :: s.elements, List.nodup_cons.mpr ⟨by simp, s.nodup⟩⟩

/-- Get the size of the set -/
def card (s : FiniteSet α) : Nat :=
  s.elements.length

/-- Sum a function over all elements in the set -/
def sum [Add β] [OfNat β 0] (s : FiniteSet α) (f : α → β) : β :=
  s.elements.foldl (fun acc x => acc + f x) 0

/-- Theorem: inserting an element that's already in the set doesn't change it -/
theorem insert_of_mem {a : α} {s : FiniteSet α} (h : a ∈ s.elements) :
    insert a s = s := by
  unfold insert
  simp [h]

/-- Theorem: inserting into empty set creates singleton -/
theorem insert_empty (a : α) :
    (insert a empty).elements = [a] := by
  unfold insert empty
  simp

end FiniteSet

/-- Finite set of addresses with size bound for Ethereum (2^160 addresses) -/
structure FiniteAddressSet where
  addresses : FiniteSet String  -- Address is String
  -- We don't enforce the 2^160 bound in the type for simplicity
  -- but it's implicitly guaranteed by EVM constraints
  deriving Repr

namespace FiniteAddressSet

/-- Create an empty address set -/
def empty : FiniteAddressSet :=
  ⟨FiniteSet.empty⟩

/-- Insert an address into the set -/
def insert (addr : String) (s : FiniteAddressSet) : FiniteAddressSet :=
  ⟨s.addresses.insert addr⟩

/-- Check if an address is in the set -/
def mem (addr : String) (s : FiniteAddressSet) : Bool :=
  s.addresses.mem addr

instance : Membership String FiniteAddressSet where
  mem := mem

/-- Get the number of addresses in the set -/
def card (s : FiniteAddressSet) : Nat :=
  s.addresses.card

end FiniteAddressSet

end DumbContracts.Core
