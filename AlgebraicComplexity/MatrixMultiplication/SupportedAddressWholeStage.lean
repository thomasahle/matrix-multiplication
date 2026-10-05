/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume
import AlgebraicComplexity.Tensor.PartitionedDirectSum
import AlgebraicComplexity.Tensor.HoleRepair

set_option autoImplicit false

/-!
# One supported address as a one-copy whole-constituent stage

`MatrixMultiplication/CoarsenedConstituentWholeStage.lean` packages *one coarse constituent* with
an inner extraction of its localized box.  This module is its **sibling**, not a specialisation:
the source here is the whole `P.realize`, and the argument is the singleton box plus legwise
injectivity rather than a coarsening.  Keeping a single supported address is the degenerate
cleanup in which no hashing, no fiber and no repair budget appears at all --- one address, one
matrix-multiplication leaf, one copy.

The index type is `PUnit`, so the stage is available in every universe; a client that has already
fixed its own index universe gets it without a `ULift`.  This is the content of the `private`
`wholeStageOfSupportedPartitionAddress`
(`Examples/CoppersmithWinogradRecursiveExactTargetBoxJointReferenceStage.lean:45`), stated once
and publicly.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **One supported address, one matrix-multiplication leaf, one copy.**

Zeroing every partition variable off `address` leaves a single-constituent tensor, whose support
is trivially legwise injective, so the whole realization restricts to that one constituent; the
supplied leaf extraction finishes it.  The index type is `PUnit`, so `I` is free in every
universe. -/
def Tensor.Restricts.supportedAddress_oneCopyWholeStage
    (P : PartitionedTensor (K := K) (A := A) V)
    (address : BlockAddress A) (haddress : address ∈ P.support)
    (xSize ySize zSize : ℕ)
    (hleaf : Restricts (P.constituent address)
      (matrixMultiplication (K := K) xSize ySize zSize)) :
    WholeConstituentLaserVolumeStage.{u, max v w, z} K P.realize 1 xSize ySize zSize where
  I := PUnit
  card_I := Fintype.card_punit
  source_restricts := by
    classical
    set parts : ∀ c, Finset (A c) := fun c ↦ ({address c} : Finset (A c)) with hparts
    set Q := P.box parts with hQ
    have hsupport : Q.support = {address} := by
      ext candidate
      rw [hQ, hparts, PartitionedTensor.mem_box_support, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hlabels⟩
        funext c
        exact Finset.mem_singleton.mp (hlabels c)
      · rintro rfl
        exact ⟨haddress, fun c ↦ Finset.mem_singleton_self _⟩
    have hmem : ∀ s ∈ Q.support, s = address := by
      intro s hs
      rw [hsupport] at hs
      exact Finset.mem_singleton.mp hs
    have hinjective : IsLegwiseInjective Q.support := by
      intro c left hleft right hright _
      exact (hmem left hleft).trans (hmem right hright).symm
    have hbox : Restricts P.realize Q.realize :=
      Tensor.Restricts.partitionedBox P parts
    have hconstituents :=
      Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum Q hinjective
    have hleaves : Restricts
        (Tensor.indexedDirectSum (V := SelectedBlockFamily (V := V) Q.support)
          (fun selected : Q.support ↦ Q.constituent selected.1))
        (Tensor.indexedDirectSum (V := fun _ : Q.support ↦ MMSpace K xSize ySize zSize)
          (fun _ : Q.support ↦ matrixMultiplication (K := K) xSize ySize zSize)) := by
      refine Tensor.Restricts.indexedDirectSum fun selected ↦ ?_
      obtain ⟨s, hs⟩ := selected
      obtain rfl : s = address := hmem s hs
      exact hleaf
    have hone : Fintype.card Q.support = Fintype.card PUnit.{z + 1} := by
      simp [Fintype.card_coe, hsupport]
    have hreindex := Tensor.Restricts.indexedDirectSum_const_equiv (K := K)
      (Fintype.equivOfCardEq hone)
      (matrixMultiplication (K := K) xSize ySize zSize)
    exact hbox.trans (hconstituents.trans (hleaves.trans hreindex))

end AlgebraicComplexity
