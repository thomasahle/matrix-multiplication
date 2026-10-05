/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedPowerConstituent

/-!
# Recursive decoding of positive-power support addresses

Every supported address of a positive partitioned power is the legwise transpose of a word of
supported source addresses.  This semantic leaf proves that fact directly from the recursive
definition of `positivePower`, and chooses a canonical preimage for clients that need one.

The coordinate theorem comparing this transpose with functions on `Fin (n + 1)` lives in
`PartitionedPowerSupportDecodeCore`; keeping it downstream prevents support-only clients from
loading the finite-tuple equivalence API.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

namespace PartitionedTensor

/-- Every word of supported source addresses transposes to a supported positive-power address.
This is the dependency-light introduction counterpart of
`exists_positiveSupportWord_of_mem_positivePower_support_recursive`. -/
theorem positiveSupportWordBlockAddress_mem_positivePower_support_recursive
    (P : PartitionedTensor (K := K) (A := A) V) :
    ∀ n : ℕ, ∀ word : PositiveWord P.support n,
      positiveSupportWordBlockAddress P.support n word ∈ (P.positivePower n).support
  | 0, word => word.2
  | n + 1, word => by
      rcases word with ⟨initial, final⟩
      change (fun c ↦
        (positiveSupportWordBlockAddress P.support n initial c, final.1 c)) ∈
          ((P.positivePower n).external P).support
      rw [(P.positivePower n).mem_external_support P]
      exact ⟨positiveSupportWordBlockAddress_mem_positivePower_support_recursive P n initial,
        final.2⟩

/-- Recursive, existence-only decoder for a supported positive-power address.

Unlike `exists_positiveSupportWord_of_mem_positivePower_support`, this theorem does not construct
or import the global finite-set equivalence.  Its conclusion is the same recovery equation needed
by constituent-level clients. -/
theorem exists_positiveSupportWord_of_mem_positivePower_support_recursive
    (P : PartitionedTensor (K := K) (A := A) V) :
    ∀ n : ℕ, ∀ {address : BlockAddress (fun c ↦ PositiveWord (A c) n)},
      address ∈ (P.positivePower n).support →
        ∃ word : PositiveWord P.support n,
          positiveSupportWordBlockAddress P.support n word = address
  | 0, address, haddress => ⟨⟨address, haddress⟩, rfl⟩
  | n + 1, address, haddress => by
      change address ∈ ((P.positivePower n).external P).support at haddress
      have hparts := ((P.positivePower n).mem_external_support P address).mp haddress
      obtain ⟨initial, hinitial⟩ :=
        exists_positiveSupportWord_of_mem_positivePower_support_recursive P n hparts.1
      let final : P.support := ⟨fun c ↦ (address c).2, hparts.2⟩
      refine ⟨(initial, final), ?_⟩
      funext c
      change (positiveSupportWordBlockAddress P.support n initial c, final.1 c) = address c
      rw [congrFun hinitial c]
      exact Prod.eta (address c)

/-- Canonical supported source word decoded from a supported positive-power address.

The choice is made once at this generic boundary.  Clients that only need a recovered word can
therefore avoid re-elaborating the dependent recursive existence proof at every specialization. -/
noncomputable def positiveSupportWordOfAddress
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (support : (P.positivePower n).support) : PositiveWord P.support n :=
  Classical.choose
    (P.exists_positiveSupportWord_of_mem_positivePower_support_recursive n support.2)

/-- Transposing the canonical decoded word recovers the original supported address.

Proof sketch: this is exactly the witness equation returned by the recursive support decoder. -/
theorem positiveSupportWordBlockAddress_positiveSupportWordOfAddress
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (support : (P.positivePower n).support) :
    positiveSupportWordBlockAddress P.support n
        (P.positiveSupportWordOfAddress n support) = support.1 :=
  Classical.choose_spec
    (P.exists_positiveSupportWord_of_mem_positivePower_support_recursive n support.2)

end PartitionedTensor
end AlgebraicComplexity.Tensor
