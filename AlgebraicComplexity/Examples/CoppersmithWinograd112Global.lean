/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112CTensor
import AlgebraicComplexity.Tensor.IndexedDegeneration
import AlgebraicComplexity.Tensor.PartitionedGrouping

/-!
# Global shared-Z grouping for the exceptional CW `112` constituent

The fixed-fiber development in `CoppersmithWinograd112CTensor` identifies every shared-Z fiber
of the X/Y-isolated support with a C-tensor.  This file performs the missing global routing step:
one legwise linear map separates *all* Z fibers at once, after which the fixed-fiber restriction
can be applied independently in every indexed summand.

The result is deliberately finite and exact.  The file also combines the three cyclic
orientations, keeps only matching occupied Z fibers, and applies the generic C-tensor
degeneration.  Its endpoint `cw112PowerCyclicProduct_degenerates_squareFamilies` is the stable
finite semantic handoff for rational typed-leaf and certificate clients.  Aggregate counting is
kept separately in `CoppersmithWinograd112GlobalCounting.lean`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

section TensorPower

universe u

variable (K : Type u) [CommRing K]
variable (q L G : ℕ)
variable {R : Type*} [Field R] [NeZero (2 : R)]

/-- The X/Y-isolated partitioned tensor before its addresses are grouped by their Z word. -/
noncomputable def cw112XYIsolatedPartition
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :=
  (cw112TypePartitionedPower K q L G).withSupport
    ((cw112PartitionHashEncoding (R := R)).xyIsolatedPowerAddresses
      (cw112TypeDepth L G) (cw112TypeWords L G) B seed)

/-- A canonical fallback Z word.  It is used only to define routing maps on block labels absent
from the selected support. -/
def cw112FirstCornerWord : PositiveWord CW112ZBlock (cw112TypeDepth L G) :=
  (positiveWordEquiv CW112ZBlock (cw112TypeDepth L G)).symm
    (fun _ ↦ CW112ZBlock.firstCorner)

/-- The legwise-readable grouping of the X/Y-isolated support by its complete Z word. -/
noncomputable def cw112XYIsolatedZGrouping
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    (cw112XYIsolatedPartition K q L G B seed).LegGrouping
      (PositiveWord CW112ZBlock (cw112TypeDepth L G)) := by
  apply PartitionedTensor.LegGrouping.byZ
    (cw112XYIsolatedPartition K q L G B seed) (cw112FirstCornerWord L G)
  · simpa [cw112XYIsolatedPartition] using
      cw112XYIsolatedPowerAddresses_xInjective L G B hB seed
  · simpa [cw112XYIsolatedPartition] using
      cw112XYIsolatedPowerAddresses_yInjective L G B hB seed

/-- A fiber of the generic Z grouping is exactly the previously defined CW shared-Z fiber. -/
theorem cw112XYIsolatedZGrouping_fiber
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :
    (cw112XYIsolatedZGrouping K q L G B hB seed).fiber z =
      (cw112TypePartitionedPower K q L G).withSupport
        (cw112XYIsolatedZFiber L G B seed z) := by
  apply PartitionedTensor.ext
  · rfl
  · rfl

/-- The isolated realization restricts to the indexed direct sum of all of its shared-Z fibers.

Proof sketch: X/Y isolation makes the Z word recoverable from each surviving X or Y block;
the Z leg reads it directly.  The generic grouping theorem therefore routes every constituent
to the summand indexed by its common Z word. -/
theorem cw112XYIsolated_restricts_groupedZFibers
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    Restricts
      (cw112XYIsolatedPartition K q L G B seed).realize
      (Tensor.indexedDirectSum
        (fun z : PositiveWord CW112ZBlock (cw112TypeDepth L G) ↦
          ((cw112XYIsolatedZGrouping K q L G B hB seed).fiber z).realize)) :=
  (cw112XYIsolatedZGrouping K q L G B hB seed).restricts_groupedIndexedDirectSum

/-- All shared-Z fibers can be retyped as C-tensors simultaneously in one indexed direct sum.

Proof sketch: first apply the global Z-grouping restriction, then use the fixed-fiber C-tensor
restriction independently on every indexed summand. -/
theorem cw112XYIsolated_restricts_indexedCTensors
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    Restricts
      (cw112XYIsolatedPartition K q L G B seed).realize
      (Tensor.indexedDirectSum
        (fun z : PositiveWord CW112ZBlock (cw112TypeDepth L G) ↦
          (CTensor.partitioned
            (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent).realize)) := by
  apply (cw112XYIsolated_restricts_groupedZFibers K q L G B hB seed).trans
  apply Tensor.Restricts.indexedDirectSum
  intro z
  rw [cw112XYIsolatedZGrouping_fiber K q L G B hB seed z]
  exact cw112ZFiber_restricts_cTensor (K := K) q L G B hB seed z

/-- The canonical power of the `112` tensor restricts to the indexed direct sum of every C-tensor
formed by the X/Y-isolated shared-Z fibers.

Proof sketch: compose the already-proved type selection and hashing restriction with the global
grouping-and-retyping theorem above. -/
theorem cw112Power_restricts_indexedCTensors
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    Restricts
      (Tensor.power (cw112PartitionedTensor K q).realize (cw112TypeDepth L G + 1))
      (Tensor.indexedDirectSum
        (fun z : PositiveWord CW112ZBlock (cw112TypeDepth L G) ↦
          (CTensor.partitioned
            (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent).realize)) :=
  (cw112Power_restricts_xyIsolated K q L G B hB seed).trans
    (cw112XYIsolated_restricts_indexedCTensors K q L G B hB seed)

/-! ## Nonempty fibers and the global cyclic product -/

/-- Z words whose X/Y-isolated fiber contains at least one constituent. -/
noncomputable def cw112OccupiedZWords
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    Finset (PositiveWord CW112ZBlock (cw112TypeDepth L G)) :=
  Finset.univ.filter fun z ↦ (cw112XYIsolatedZFiber L G B seed z).Nonempty

/-- Membership in the occupied-Z family is equivalent to nonemptiness of the corresponding
shared-Z fiber. -/
@[simp] theorem mem_cw112OccupiedZWords
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :
    z ∈ cw112OccupiedZWords L G B seed ↔
      (cw112XYIsolatedZFiber L G B seed z).Nonempty := by
  simp [cw112OccupiedZWords]

/-- The C-tensor realization attached to one shared-Z fiber. -/
noncomputable def cw112ZCTensor
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :=
  (CTensor.partitioned
    (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent).realize

/-- After global grouping, discard the formally present but empty Z fibers. -/
theorem cw112Power_restricts_occupiedIndexedCTensors
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    Restricts
      (Tensor.power (cw112PartitionedTensor K q).realize (cw112TypeDepth L G + 1))
      (Tensor.indexedDirectSum
        (fun z : cw112OccupiedZWords L G B seed ↦
          cw112ZCTensor K q L G B hB seed z.1)) := by
  apply (cw112Power_restricts_indexedCTensors K q L G B hB seed).trans
  simpa only [cw112ZCTensor] using
    (Tensor.Restricts.indexedDirectSum_subfamily
      (fun z : PositiveWord CW112ZBlock (cw112TypeDepth L G) ↦
        (CTensor.partitioned
          (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent).realize)
      (cw112OccupiedZWords L G B seed))

/-- Three-orientation cyclic product of the canonical selected `112` tensor power. -/
noncomputable def cw112PowerCyclicProduct :=
  let T := Tensor.power (cw112PartitionedTensor K q).realize (cw112TypeDepth L G + 1)
  Tensor.external
    (Tensor.external T (Tensor.permute cycle T))
    (Tensor.permute cycle.symm T)

/-- Side length of every square matrix-multiplication tensor extracted from a finite `112` leaf.

The exponent `4G + 2L` is the sum of the three cyclically oriented constituent dimensions. -/
abbrev cw112FiniteLeafSquareSide : ℕ :=
  q ^ (4 * G + 2 * L)

/-- The complete finite output of shared-Z grouping and C-tensor extraction.

There is one outer summand for every occupied shared-Z word and one inner summand for every
minimum-weight antidiagonal address in that word's C-tensor.  Naming this dependent tensor keeps
downstream asymptotic clients independent of its implementation-level block spaces. -/
noncomputable def cw112FiniteLeafSquareFamilies
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :=
  Tensor.indexedDirectSum
    (fun z : cw112OccupiedZWords L G B seed ↦
      Tensor.indexedDirectSum
        (fun _ : (CTensor.antidiagonal
          (cw112ZFiberRetyping
            (K := K) q L G B hB seed z.1).targetConstituent).support ↦
          matrixMultiplication (K := K)
            (cw112FiniteLeafSquareSide q L G)
            (cw112FiniteLeafSquareSide q L G)
            (cw112FiniteLeafSquareSide q L G)))

/-- The cyclic product of the `112` power restricts to the indexed direct sum of the cyclic
products of all occupied shared-Z C-tensors.

Proof sketch: apply the occupied-fiber restriction independently to the three cyclic
orientations.  The generic cyclic diagonal map then kills products whose Z-fiber indices differ,
leaving exactly one componentwise cyclic C-tensor for every occupied Z word. -/
theorem cw112PowerCyclicProduct_restricts_indexedCyclicCTensors
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    Restricts
      (cw112PowerCyclicProduct K q L G)
      (Tensor.indexedDirectSum
        (fun z : cw112OccupiedZWords L G B seed ↦
          CTensor.cyclicTensor
            (cw112ZFiberRetyping (K := K) q L G B hB seed z.1).targetConstituent)) := by
  let T := Tensor.power (cw112PartitionedTensor K q).realize (cw112TypeDepth L G + 1)
  let C := fun z : cw112OccupiedZWords L G B seed ↦
    cw112ZCTensor K q L G B hB seed z.1
  have h : Restricts T (Tensor.indexedDirectSum C) :=
    cw112Power_restricts_occupiedIndexedCTensors K q L G B hB seed
  have hthree : Restricts
      (Tensor.external
        (Tensor.external T (Tensor.permute cycle T))
        (Tensor.permute cycle.symm T))
      (Tensor.external
        (Tensor.external (Tensor.indexedDirectSum C)
          (Tensor.permute cycle (Tensor.indexedDirectSum C)))
        (Tensor.permute cycle.symm (Tensor.indexedDirectSum C))) :=
    (h.external (h.permute cycle)).external (h.permute cycle.symm)
  apply hthree.trans
  simpa [C, cw112ZCTensor, CTensor.cyclicTensor, cw112PowerCyclicProduct, T] using
    (Tensor.Restricts.cyclic_indexedDirectSum_diagonal C)

/-- All occupied shared-Z C-tensors degenerate simultaneously to their antidiagonal square
families, even though their fiber sizes and displayed leading degrees may differ.

Proof sketch: occupied fibers have positive cardinality, hence positive antidiagonal degree
`3*h^2`.  Apply the degree-aware fixed-fiber theorem componentwise and synchronize the finitely
many positive degrees using their product. -/
theorem cw112IndexedCyclicCTensors_degenerates_squareFamilies
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    PolynomialDegenerates
      (Tensor.indexedDirectSum
        (fun z : cw112OccupiedZWords L G B seed ↦
          CTensor.cyclicTensor
            (cw112ZFiberRetyping (K := K) q L G B hB seed z.1).targetConstituent))
      (cw112FiniteLeafSquareFamilies K q L G B hB seed) := by
  unfold cw112FiniteLeafSquareFamilies
  let d := fun z : cw112OccupiedZWords L G B seed ↦
    CTensor.antidiagonalDegree (cw112XYIsolatedZFiber L G B seed z.1).card
  apply Tensor.PolynomialDegenerates.indexedDirectSum_of_pos_degrees d
  · intro z
    have hz : 0 < (cw112XYIsolatedZFiber L G B seed z.1).card :=
      Finset.card_pos.mpr ((mem_cw112OccupiedZWords L G B seed z.1).mp z.2)
    unfold d CTensor.antidiagonalDegree
    exact Nat.mul_pos (by omega) (Nat.pow_pos hz)
  · intro z
    exact cw112ZFiber_cyclicTensor_degeneratesAt_squareDirectSum
      (K := K) q L G B hB seed z.1

/-- The full cyclic `112` power degenerates to the nested indexed direct sum of all square
matrix-multiplication tensors contributed by occupied Z fibers. -/
theorem cw112PowerCyclicProduct_degenerates_squareFamilies
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    PolynomialDegenerates
      (cw112PowerCyclicProduct K q L G)
      (cw112FiniteLeafSquareFamilies K q L G B hB seed) :=
  (Tensor.PolynomialDegenerates.of_restricts
      (cw112PowerCyclicProduct_restricts_indexedCyclicCTensors
        K q L G B hB seed)).trans
    (cw112IndexedCyclicCTensors_degenerates_squareFamilies
      K q L G B hB seed)

end TensorPower

end AlgebraicComplexity.Examples
