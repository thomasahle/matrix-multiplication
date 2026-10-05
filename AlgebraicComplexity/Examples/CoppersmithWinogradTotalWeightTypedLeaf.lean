/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotient
import AlgebraicComplexity.Examples.CoppersmithWinogradChunkTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.CoarsenedRationalTypedLeaf

set_option autoImplicit false

/-!
# Fine typed leaves inside total-weight CW constituents

The total-weight quotient is used only as a block alphabet.  A retained quotient constituent is
the sum of all fine constituents in its fiber.  This module proves that an exact pushed-forward
joint type is enough to project every retained quotient constituent to a prescribed fine rational
typed leaf, with the same output index and the original matrix dimensions.

There are two sound interfaces, deliberately kept distinct:

* selecting the three pushed-forward quotient **marginal** types preserves the entire fine
  marginal-type-selected tensor;
* extracting one matrix-multiplication tensor from each individual quotient constituent requires
  its full **joint** quotient-support type (or an equivalent injective shape-type witness).

Thus collapsing fine beta tables is not licensed by marginal quotient laws alone.  In the total
weight quotient, however, the three-coordinate total-weight shape is injective on the quotient
support, so the certificate's full joint shape law (`alpha`) is an exact replacement for the
joint-type premise.
-/

namespace AlgebraicComplexity.WordType

universe u v

/-- Pushforward of natural-valued multiplicities along an injective alphabet map is injective.
This is the elementary exact-type bridge used when a certificate records an injective feature of
the joint support rather than the support type itself. -/
theorem mappedType_injective_of_injective
    {A : Type u} {B : Type v} [Fintype A]
    (f : A → B) (hf : Function.Injective f) :
    Function.Injective (mappedType f) := by
  classical
  intro left right h
  funext a
  have ha := congrFun h (f a)
  have hfiber : letterFiber f (f a) = {a} := by
    ext x
    simp only [mem_letterFiber, Finset.mem_singleton]
    exact hf.eq_iff
  unfold mappedType at ha
  rw [hfiber] at ha
  simpa using ha

end AlgebraicComplexity.WordType

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-- Native CW chunks coarsened only by their total complete-split weight. -/
def cwTotalWeightChunkCoarsening (depth : ℕ) :
    ∀ _c : Leg,
      PositiveWord CWBlock (2 ^ depth - 1) → CWCoarseDigit depth :=
  fun _c ↦ cwChunkCoarseDigit depth

@[simp] theorem cwTotalWeightChunkCoarsening_apply
    (depth : ℕ) (c : Leg)
    (chunk : PositiveWord CWBlock (2 ^ depth - 1)) :
    cwTotalWeightChunkCoarsening depth c chunk = cwChunkCoarseDigit depth chunk :=
  rfl

/-- The actual joint support alphabet of one total-weight-coarsened CW chunk. -/
noncomputable abbrev CWTotalWeightCoarseSupport
    (K : Type u) [CommRing K] (q depth : ℕ) :=
  ((cwChunkPartitionedTensor K q depth).coarsen
    (cwTotalWeightChunkCoarsening depth)).support

/-- Recover the supported total-weight joint word underlying a quotient positive-power
address. -/
noncomputable def cwTotalWeightCoarseWordOfAddress
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support) :
    PositiveWord (CWTotalWeightCoarseSupport K q depth) n :=
  Classical.choose
    (((cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)
        ).exists_positiveSupportWord_of_mem_positivePower_support n haddress)

/-- Transposing the recovered supported total-weight word gives the original address. -/
theorem positiveSupportWordBlockAddress_cwTotalWeightCoarseWordOfAddress
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support) :
    positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n
        (cwTotalWeightCoarseWordOfAddress K q depth n address haddress) = address :=
  Classical.choose_spec
    (((cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)
        ).exists_positiveSupportWord_of_mem_positivePower_support n haddress)

/-- A concrete supported chunk letter.  This supplies the `Nonempty` witness required by the
generic rational typed-leaf API uniformly in `q` and `depth`. -/
noncomputable def cwChunkSupportWitness
    (K : Type u) [CommRing K] (q depth : ℕ) :
    (cwChunkPartitionedTensor K q depth).support := by
  classical
  let base : (cwPartitionedTensor K q).support := ⟨cw200, by
    change cw200 ∈ cwBlockSupport
    decide⟩
  let word : PositiveWord (cwPartitionedTensor K q).support (2 ^ depth - 1) :=
    positiveWordConst base (2 ^ depth - 1)
  refine ⟨positiveSupportWordBlockAddress
    (cwPartitionedTensor K q).support (2 ^ depth - 1) word, ?_⟩
  change _ ∈ ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).support
  rw [(cwPartitionedTensor K q).positivePower_support_eq_image_positiveSupportWordBlockAddress]
  exact Finset.mem_image.mpr ⟨word, Finset.mem_univ _, rfl⟩

/-- The full three-coordinate total-weight shape of a supported quotient letter. -/
def cwTotalWeightSupportedShape
    (K : Type u) [CommRing K] (q depth : ℕ)
    (address : CWTotalWeightCoarseSupport K q depth) : Leg → ℕ :=
  fun c ↦ (address.1 c : ℕ)

/-- A total-weight quotient support letter is completely determined by its three-coordinate
shape.  Unlike the sorted-pair refinement, no conditional rigidity calculation is needed. -/
theorem cwTotalWeightSupportedShape_injective
    (K : Type u) [CommRing K] (q depth : ℕ) :
    Function.Injective (cwTotalWeightSupportedShape K q depth) := by
  intro left right h
  apply Subtype.ext
  funext c
  apply Fin.ext
  exact congrFun h c

/-- Equality of the full joint total-weight shape law is exactly equality of joint quotient
support types.  This is the finite theorem identifying a fixed `alpha` table with the joint-type
premise required by constituent-level coarse-to-fine extraction. -/
theorem cwTotalWeight_jointType_eq_of_shapeType
    (K : Type u) [CommRing K] (q depth : ℕ)
    (left right : CWTotalWeightCoarseSupport K q depth → ℕ)
    (hshape : WordType.mappedType (cwTotalWeightSupportedShape K q depth) left =
      WordType.mappedType (cwTotalWeightSupportedShape K q depth) right) :
    left = right :=
  WordType.mappedType_injective_of_injective
    (cwTotalWeightSupportedShape K q depth)
    (cwTotalWeightSupportedShape_injective K q depth) hshape

/-- Marginal-level quotient bridge for a whole selected quotient tensor.  Selecting the
pushed-forward total-weight type on each leg preserves the entire tensor selected by the original
three fine types.  This theorem does not start from one fixed quotient constituent; for that
localized situation use `cwTotalWeight_coarseConstituent_to_localizedFineTypes`. -/
theorem cwTotalWeight_selectCoarsenedPositiveMappedTypes_to_fineTypes
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (fineType : ∀ _c,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ) :
    Restricts
      (((cwChunkPartitionedTensor K q depth).selectCoarsenedPositiveTypes
        (cwTotalWeightChunkCoarsening depth) n
        (fun c ↦ WordType.mappedType
          (cwTotalWeightChunkCoarsening depth c) (fineType c))).realize)
      ((((cwChunkPartitionedTensor K q depth).positivePower n).select
        (fun c word ↦ word ∈ positiveTypeClass
          (PositiveWord CWBlock (2 ^ depth - 1)) n (fineType c))).realize) :=
  Restricts.selectCoarsenedPositiveMappedTypes_to_fineTypes
    (cwChunkPartitionedTensor K q depth)
    (cwTotalWeightChunkCoarsening depth) n fineType

/-- Constituent-level total-weight quotient bridge.  Every quotient support word of the full
pushed-forward **joint** fine type contains the same fine rational typed leaf, with exactly the
original rectangular dimensions. -/
theorem cwTotalWeight_coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c =
        cwChunkConstituentDimension K q depth support c)
    {r k : ℕ}
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) r)
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q depth).support (r + 1))
    (hcoarse : coarseWord ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) r
      (WordType.mappedType
        ((cwChunkPartitionedTensor K q depth).coarsenSupportMap
          (cwTotalWeightChunkCoarsening depth))
        (WordType.proportionalCounts leaf.profile.count k))) :
    Restricts
      (((cwChunkPartitionedTensor K q depth).coarsenedPositivePower
          (cwTotalWeightChunkCoarsening depth) r).constituent
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) r coarseWord))
      (matrixMultiplication (K := K)
        (leaf.dimensionProduct .X ^ k)
      (leaf.dimensionProduct .Y ^ k)
      (leaf.dimensionProduct .Z ^ k)) := by
  letI : Nonempty (cwChunkPartitionedTensor K q depth).support :=
    ⟨cwChunkSupportWitness K q depth⟩
  apply RationalTypedLeaf.coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType
    (cwChunkPartitionedTensor K q depth)
      (cwTotalWeightChunkCoarsening depth) leaf
      (cwChunk_constituent_restricts_of_leaf_dimension_eq
        K q depth leaf hdimension)
      coarseWord hlegal hcoarse

/-- Copy-preserving indexed form of the total-weight constituent bridge.  The quotient method
gets exactly one original fine rectangular leaf for every already-isolated quotient constituent;
the output family is neither shrunk nor multiplied by a quotient-fiber cardinality. -/
theorem cwTotalWeight_indexedDirectSum_coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType
    (K : Type u) [CommRing K] (q depth : ℕ)
    {I : Type*} [Fintype I]
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c =
        cwChunkConstituentDimension K q depth support c)
    {r k : ℕ}
    (coarseWord : I → PositiveWord (CWTotalWeightCoarseSupport K q depth) r)
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q depth).support (r + 1))
    (hcoarse : ∀ i, coarseWord i ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) r
      (WordType.mappedType
        ((cwChunkPartitionedTensor K q depth).coarsenSupportMap
          (cwTotalWeightChunkCoarsening depth))
        (WordType.proportionalCounts leaf.profile.count k))) :
    Restricts
      (Tensor.indexedDirectSum (fun i ↦
        ((cwChunkPartitionedTensor K q depth).coarsenedPositivePower
          (cwTotalWeightChunkCoarsening depth) r).constituent
            (positiveSupportWordBlockAddress
              (CWTotalWeightCoarseSupport K q depth) r (coarseWord i))))
      (Tensor.indexedDirectSum (fun _i : I ↦
        matrixMultiplication (K := K)
          (leaf.dimensionProduct .X ^ k)
          (leaf.dimensionProduct .Y ^ k)
          (leaf.dimensionProduct .Z ^ k))) := by
  letI : Nonempty (cwChunkPartitionedTensor K q depth).support :=
    ⟨cwChunkSupportWitness K q depth⟩
  apply RationalTypedLeaf.indexedDirectSum_coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType
    (cwChunkPartitionedTensor K q depth)
      (cwTotalWeightChunkCoarsening depth) leaf
      (cwChunk_constituent_restricts_of_leaf_dimension_eq
        K q depth leaf hdimension)
      coarseWord hlegal hcoarse

/-- Alpha-facing constituent corollary.  It is enough to know that the coarse word's full
three-coordinate shape type equals that of the pushed-forward fine type, because the total-weight
shape is injective on the actual quotient support. -/
theorem cwTotalWeight_coarsenedPositivePower_constituent_matrixMultiplication_of_shapeType
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c =
        cwChunkConstituentDimension K q depth support c)
    {r k : ℕ}
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) r)
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q depth).support (r + 1))
    (hshape : WordType.mappedType (cwTotalWeightSupportedShape K q depth)
        (WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) r coarseWord)) =
      WordType.mappedType (cwTotalWeightSupportedShape K q depth)
        (WordType.mappedType
          ((cwChunkPartitionedTensor K q depth).coarsenSupportMap
            (cwTotalWeightChunkCoarsening depth))
          (WordType.proportionalCounts leaf.profile.count k))) :
    Restricts
      (((cwChunkPartitionedTensor K q depth).coarsenedPositivePower
          (cwTotalWeightChunkCoarsening depth) r).constituent
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) r coarseWord))
      (matrixMultiplication (K := K)
        (leaf.dimensionProduct .X ^ k)
        (leaf.dimensionProduct .Y ^ k)
        (leaf.dimensionProduct .Z ^ k)) := by
  apply cwTotalWeight_coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType
    K q depth leaf hdimension coarseWord hlegal
  rw [mem_positiveTypeClass]
  exact cwTotalWeight_jointType_eq_of_shapeType K q depth _ _ hshape

end AlgebraicComplexity.Examples
