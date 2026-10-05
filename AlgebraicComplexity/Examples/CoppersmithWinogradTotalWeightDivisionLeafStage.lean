/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightNestedComposition
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionLeafStage
import AlgebraicComplexity.MatrixMultiplication.OuterConstituentWholeStage

/-!
# Total-weight nested extraction as an exact division leaf

Total-weight hashing separates whole coarse constituents.  Each survivor still contains its
complete localized fine typed family, and an exact inner extraction may be transported from one
canonical coarse word to every survivor of the same exact coarse type.  This file flattens those
two exact index families and packages the result as a positive leaf of an exact recursive
division tree.

This is the quotient-route alternative to fine compatibility cleanup and hole repair.  The outer
restriction, exact coarse-type membership, and canonical inner restriction remain explicit.  The
constructor does not assume a restriction of an assembled division tree and does not attach an
asymptotic count.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w x

/-- Flatten an exact family of same-coarse-type total-weight survivors and the complete exact
inner family carried by each survivor.

Unlike the polynomial nested-stage interface, this theorem assumes an exact restriction for the
canonical inner family.  That stronger local input is exactly what permits the result to populate
an `ExactInterfaceTermDivisionTree`, whose leaf stages are restriction based. -/
noncomputable def cwTotalWeightLocalizedOuter_wholeStage_of_fixedCoarseType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    (source : Tensor3 K Source)
    {I : Type w} [Fintype I]
    (coarseWord : I → PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (reference : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (coarseType : CWTotalWeightCoarseSupport K q depth → ℕ)
    (hreference : reference ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) n coarseType)
    (hcoarseWord : ∀ i, coarseWord i ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) n coarseType)
    (fineType : ∀ _c, PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    {J : Type x} [Fintype J]
    (outerCopies innerCopies xSize ySize zSize : ℕ)
    (hcardI : Fintype.card I = outerCopies)
    (hcardJ : Fintype.card J = innerCopies)
    (houter : Restricts source
      (Tensor.indexedDirectSum (fun i : I ↦
        (cwTotalWeightLocalizedFineTypes K q depth n
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n (coarseWord i))
          fineType).realize)))
    (hcanonical : Restricts
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n reference)
        fineType).realize
      (Tensor.indexedDirectSum (fun _j : J ↦
        matrixMultiplication (K := K) xSize ySize zSize))) :
    WholeConstituentLaserVolumeStage K source
      (outerCopies * innerCopies) xSize ySize zSize := by
  let outer := cwTotalWeightLocalizedOuterConstituentStage
    K q depth n source coarseWord fineType outerCopies hcardI houter
  letI := outer.addCommMonoidW
  letI := outer.moduleW
  apply OuterConstituentStage.toWholeConstituentLaserVolumeStage_of_exactInner K
    outer (fun _i ↦ J) (fun _i ↦ hcardJ)
  intro i
  exact (cwTotalWeightLocalizedOuter_isomorphicToReference_of_fixedCoarseType
    K q depth n source coarseWord reference coarseType hreference hcoarseWord
      fineType outerCopies hcardI houter i).restricts.trans hcanonical

/-- An exact nested total-weight extraction supplies one positive leaf of the recursive CW
division tree.

The output copy count is the literal product of the outer whole-coarse survivor count and the
inner typed-family count.  Successful elaboration checks that the source of the supplied outer
restriction is exactly the selected positive interface term computed by the division leaf. -/
noncomputable def cwTotalWeightLocalizedOuter_fixedCoarseTypeDivisionLeafStage
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {I : Type w} [Fintype I]
    (coarseWord : I → PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (reference : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (coarseType : CWTotalWeightCoarseSupport K q depth → ℕ)
    (hreference : reference ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) n coarseType)
    (hcoarseWord : ∀ i, coarseWord i ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) n coarseType)
    (fineType : ∀ _c, PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    {J : Type x} [Fintype J]
    (outerCopies innerCopies xSize ySize zSize : ℕ)
    (hcardI : Fintype.card I = outerCopies)
    (hcardJ : Fintype.card J = innerCopies)
    (houter : Restricts
      ((cwChunkPartitionedTensor K q depth).exactInterfaceTermPowerRestriction
        (fun _c ↦ cwChunkSplitWord depth) (.positive n hmultiplicity)).target
      (Tensor.indexedDirectSum (fun i : I ↦
        (cwTotalWeightLocalizedFineTypes K q depth n
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n (coarseWord i))
          fineType).realize)))
    (hcanonical : Restricts
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n reference)
        fineType).realize
      (Tensor.indexedDirectSum (fun _j : J ↦
        matrixMultiplication (K := K) xSize ySize zSize))) :
    ExactInterfaceTermDivisionTree.LeafStages K
      (cwChunkPartitionedTensor K q depth)
      (fun _c ↦ cwChunkSplitWord depth)
      (.leaf (.positive n hmultiplicity)) :=
  ExactInterfaceTermDivisionTree.LeafStages.ofNonempty K (.positive n hmultiplicity)
    ⟨cwTotalWeightLocalizedOuter_wholeStage_of_fixedCoarseType
      K q depth n
      ((cwChunkPartitionedTensor K q depth).exactInterfaceTermPowerRestriction
        (fun _c ↦ cwChunkSplitWord depth) (.positive n hmultiplicity)).target
      coarseWord reference coarseType hreference hcoarseWord fineType
      outerCopies innerCopies xSize ySize zSize hcardI hcardJ houter hcanonical⟩

end AlgebraicComplexity.Examples
