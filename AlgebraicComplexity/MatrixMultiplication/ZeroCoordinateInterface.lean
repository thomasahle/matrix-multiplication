/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibilityInterfaceCore

/-!
# Exact zero-coordinate interface supports

For any fine-legal partition whose block labels inject into ternary split words, selecting an
exact interface term with zero `Z` coordinate produces one common `Z` block word.  Moreover,
either the `X` or the `Y` block word determines the whole selected address.  This is the generic
shared-leg support theorem behind zero/easy C-tensor extraction; no CW-specific tensor algebra or
counting theorem occurs here.
-/

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u v w

section

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {depth n : ℕ}

/-- If one exact coordinate has total zero, its native positive-power label is the constant word
on the unique native label whose encoding is zero. -/
theorem selectedExactInterfaceTerm_leg_eq_const_of_count_eq_zero
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (c : Leg) (hzero : term.index.count c = 0)
    (zeroLabel : A c) (hencodeZero : encode c zeroLabel = 0)
    (hencode : Function.Injective (encode c))
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (haddress : address ∈
      (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support) :
    address c = positiveWordConst zeroLabel n := by
  apply (positiveWordEquiv (A c) n).injective
  funext sample
  apply hencode
  rw [positiveWordEquiv_const, hencodeZero]
  apply CompatibilityModel.splitWord_eq_zero_of_weight_eq_zero
  exact (selectedExactInterfaceTerm_chunkWeight P encode term hmultiplicity
    address haddress c sample).trans hzero

/-- On a selected zero-`Z` interface, the encoded `Y` chunk at each sample is the digitwise
complement of the encoded `X` chunk. -/
theorem selectedExactInterfaceTerm_yChunk_eq_complement_xChunk_of_z_eq_zero
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (haddress : address ∈
      (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (sample : Fin (n + 1)) :
    encode .Y (positiveWordEquiv (A .Y) n (address .Y) sample) =
      complementSplitWord
        (encode .X (positiveWordEquiv (A .X) n (address .X) sample)) := by
  let partAt : Fin (n + 1) → Unit := fun _ ↦ ()
  let model := encodedPositiveWordCompatibilityModel encode partAt
  have hlegal : model.IsFineLegal address :=
    encodedPositiveWordCompatibilityModel_isFineLegal_of_mem_exactInterfaceTerm_support
      P encode partAt hlegalSupport term hmultiplicity address haddress
  have hweights : model.HasCoarseWeights address :=
    encodedPositiveWordCompatibilityModel_hasCoarseWeights encode partAt address
  have hzCoarse : (model.coarse address sample).z = 0 := by
    change splitWordWeight
      (encode .Z (positiveWordEquiv (A .Z) n (address .Z) sample)) = 0
    exact (selectedExactInterfaceTerm_chunkWeight P encode term hmultiplicity
      address haddress .Z sample).trans hz
  exact model.y_eq_complement_x_of_z_eq_zero address hlegal hweights sample hzCoarse

/-- Equality of selected `X` labels on a zero-`Z` interface forces equality of the selected `Y`
labels. -/
theorem selectedExactInterfaceTerm_y_eq_of_x_eq_of_z_eq_zero
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hencodeY : Function.Injective (encode .Y))
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (left right : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (hleft : left ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (hright : right ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (hx : left .X = right .X) :
    left .Y = right .Y := by
  apply (positiveWordEquiv (A .Y) n).injective
  funext sample
  apply hencodeY
  rw [selectedExactInterfaceTerm_yChunk_eq_complement_xChunk_of_z_eq_zero
      P encode hlegalSupport term hmultiplicity hz left hleft sample,
    selectedExactInterfaceTerm_yChunk_eq_complement_xChunk_of_z_eq_zero
      P encode hlegalSupport term hmultiplicity hz right hright sample,
    hx]

/-- Equality of selected `Y` labels on a zero-`Z` interface forces equality of the selected `X`
labels. -/
theorem selectedExactInterfaceTerm_x_eq_of_y_eq_of_z_eq_zero
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hencodeX : Function.Injective (encode .X))
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (left right : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (hleft : left ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (hright : right ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (hy : left .Y = right .Y) :
    left .X = right .X := by
  apply (positiveWordEquiv (A .X) n).injective
  funext sample
  apply hencodeX
  have hleftComplement := congrArg complementSplitWord
    (selectedExactInterfaceTerm_yChunk_eq_complement_xChunk_of_z_eq_zero
      P encode hlegalSupport term hmultiplicity hz left hleft sample)
  have hrightComplement := congrArg complementSplitWord
    (selectedExactInterfaceTerm_yChunk_eq_complement_xChunk_of_z_eq_zero
      P encode hlegalSupport term hmultiplicity hz right hright sample)
  rw [hy] at hleftComplement
  simpa using hleftComplement.symm.trans hrightComplement

/-- **Generic shared-leg support law.**  On a zero-`Z` exact interface term, the native `Z`
positive word is constant and either side block is injective on the entire selected support. -/
theorem selectedExactInterfaceTerm_zeroZ_support_isSharedFiber
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hencode : ∀ c, Function.Injective (encode c))
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (zeroZ : A .Z) (hzeroZ : encode .Z zeroZ = 0) :
    (∀ address ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support,
        address .Z = positiveWordConst zeroZ n) ∧
      Set.InjOn (fun address ↦ address .X)
        (↑(P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support :
          Set (BlockAddress fun c ↦ PositiveWord (A c) n)) ∧
      Set.InjOn (fun address ↦ address .Y)
        (↑(P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support :
          Set (BlockAddress fun c ↦ PositiveWord (A c) n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro address haddress
    exact selectedExactInterfaceTerm_leg_eq_const_of_count_eq_zero
      P encode term hmultiplicity .Z hz zeroZ hzeroZ (hencode .Z) address haddress
  · intro left hleft right hright hx
    simp only [Finset.mem_coe] at hleft hright
    funext c
    cases c with
    | X => exact hx
    | Y =>
        exact selectedExactInterfaceTerm_y_eq_of_x_eq_of_z_eq_zero
          P encode (hencode .Y) hlegalSupport term hmultiplicity hz
          left right hleft hright hx
    | Z =>
        exact (selectedExactInterfaceTerm_leg_eq_const_of_count_eq_zero
          P encode term hmultiplicity .Z hz zeroZ hzeroZ (hencode .Z) left hleft).trans
          (selectedExactInterfaceTerm_leg_eq_const_of_count_eq_zero
            P encode term hmultiplicity .Z hz zeroZ hzeroZ (hencode .Z) right hright).symm
  · intro left hleft right hright hy
    simp only [Finset.mem_coe] at hleft hright
    funext c
    cases c with
    | X =>
        exact selectedExactInterfaceTerm_x_eq_of_y_eq_of_z_eq_zero
          P encode (hencode .X) hlegalSupport term hmultiplicity hz
          left right hleft hright hy
    | Y => exact hy
    | Z =>
        exact (selectedExactInterfaceTerm_leg_eq_const_of_count_eq_zero
          P encode term hmultiplicity .Z hz zeroZ hzeroZ (hencode .Z) left hleft).trans
          (selectedExactInterfaceTerm_leg_eq_const_of_count_eq_zero
            P encode term hmultiplicity .Z hz zeroZ hzeroZ (hencode .Z) right hright).symm

end

end MoreAsymmetryCompatibility
end AlgebraicComplexity
