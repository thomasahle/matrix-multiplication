/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareCounting

/-!
# Marked outer hashing for the Coppersmith--Winograd tensor square

This file connects the exact word combinatorics in `CoppersmithWinogradSquareCounting` to the
semantic partitioned-tensor API.  Legwise zeroing first retains every supported square word with
the prescribed three marginal types.  Marked affine hashing then isolates the chosen symmetric
joint type against that entire ambient marginal family.

The endpoint is an exact tensor restriction to an indexed direct sum of the marked square-power
constituents.  It does not yet identify those constituents with matrix-multiplication tensors;
that orbitwise assembly is the next client layer.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

section

variable (K : Type u) [CommRing K]
variable (q a b c d k : ℕ)

/-- The positive power of the coarsened CW square after retaining exactly the prescribed
five-coordinate type on each leg. -/
noncomputable def cwSquareAmbientPartitionedPower :
    PartitionedTensor (K := K)
      (A := fun _ : Leg ↦ PositiveWord (Fin 5) (cwSquareDepth a b c d k))
      (PositivePowerBlockSpace K (CWSquareBlockSpace K q)
        (cwSquareDepth a b c d k)) :=
  ((cwSquarePartitionedTensor K q).positivePower (cwSquareDepth a b c d k)).select
    (cwSquareKeepMarginal a b c d k)

/-- The ambient zeroed power has exactly the block addresses modeled by supported square words
with the prescribed three marginals.

Proof sketch: the complete positive-power support is the image of all supported address words;
the generic filter theorem converts the three leg predicates into the ambient source-word
family. -/
theorem cwSquareAmbientPartitionedPower_support
    {R : Type*} [Field R]
    (H : PartitionHashEncoding (R := R) cwSquareSupport) :
    (cwSquareAmbientPartitionedPower K q a b c d k).support =
      H.modeledAddresses (cwSquareDepth a b c d k)
        (H.legalTargets (cwSquareDepth a b c d k)
          (cwSquareAmbientWords a b c d k)) := by
  classical
  unfold cwSquareAmbientPartitionedPower
  change
    (((cwSquarePartitionedTensor K q).positivePower
      (cwSquareDepth a b c d k)).support.filter
        (fun s ↦ ∀ leg, cwSquareKeepMarginal a b c d k leg (s leg))) = _
  rw [H.positivePower_support_eq_modeledLegalTargets
    (cwSquarePartitionedTensor K q) (cwSquareDepth a b c d k)]
  exact H.filter_modeledLegalTargets_eq_of_mem_iff
    (cwSquareDepth a b c d k) (cwSquareAmbientWords a b c d k)
    (cwSquareKeepMarginal a b c d k)
    (mem_cwSquareAmbientWords_iff_keepMarginals a b c d k)

/-- A power of the realized CW square restricts to the ambient three-marginal partition by first
expanding it as the positive partition power and then zeroing the unwanted leg blocks. -/
theorem cwSquarePower_restricts_ambientPartitionedPower :
    Restricts
      (Tensor.power (cwSquarePartitionedTensor K q).realize
        (cwSquareDepth a b c d k + 1))
      (cwSquareAmbientPartitionedPower K q a b c d k).realize := by
  exact (Tensor.Restricts.power_partitionedPositivePower
      (cwSquarePartitionedTensor K q) (cwSquareDepth a b c d k)).trans
    (Tensor.Restricts.partitionedSelect
      ((cwSquarePartitionedTensor K q).positivePower
        (cwSquareDepth a b c d k))
      (cwSquareKeepMarginal a b c d k))

/-- The ambient partition restricts to a genuine indexed direct sum of marked joint-type
constituents isolated against every ambient competitor. -/
theorem cwSquareAmbientPartitionedPower_restricts_markedIndexedDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1))) :
    Restricts
      (cwSquareAmbientPartitionedPower K q a b c d k).realize
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K (CWSquareBlockSpace K q)
            (cwSquareDepth a b c d k))
          (H.markedLegwiseIsolatedPowerAddresses
            (cwSquareDepth a b c d k)
            (cwSquareAmbientWords a b c d k)
            (cwSquareMarkedWords a b c d k) B seed))
        (fun s : H.markedLegwiseIsolatedPowerAddresses
            (cwSquareDepth a b c d k)
            (cwSquareAmbientWords a b c d k)
            (cwSquareMarkedWords a b c d k) B seed ↦
          (cwSquareAmbientPartitionedPower K q a b c d k).constituent s.1)) := by
  exact Tensor.Restricts.modeledTargets_to_markedLegwiseIsolatedIndexedDirectSum
    H (cwSquareAmbientWords a b c d k) (cwSquareMarkedWords a b c d k)
    (cwSquareMarkedWords_subset_ambientWords a b c d k) B hB seed
    (cwSquareAmbientPartitionedPower K q a b c d k)
    (cwSquareAmbientPartitionedPower_support K q a b c d k H)

/-- Complete finite outer extraction: a square-tensor power restricts to the indexed direct sum
of all marked targets retained by one hashing seed. -/
theorem cwSquarePower_restricts_markedIndexedDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1))) :
    Restricts
      (Tensor.power (cwSquarePartitionedTensor K q).realize
        (cwSquareDepth a b c d k + 1))
      (indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K (CWSquareBlockSpace K q)
            (cwSquareDepth a b c d k))
          (H.markedLegwiseIsolatedPowerAddresses
            (cwSquareDepth a b c d k)
            (cwSquareAmbientWords a b c d k)
            (cwSquareMarkedWords a b c d k) B seed))
        (fun s : H.markedLegwiseIsolatedPowerAddresses
            (cwSquareDepth a b c d k)
            (cwSquareAmbientWords a b c d k)
            (cwSquareMarkedWords a b c d k) B seed ↦
          (cwSquareAmbientPartitionedPower K q a b c d k).constituent s.1)) := by
  exact (cwSquarePower_restricts_ambientPartitionedPower K q a b c d k).trans
    (cwSquareAmbientPartitionedPower_restricts_markedIndexedDirectSum
      K q a b c d k H B hB seed)

end

end AlgebraicComplexity.Examples
