/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerExtraction
import AlgebraicComplexity.MatrixMultiplication.NestedLaserVolumeComposition

set_option autoImplicit false

/-!
# Nested total-weight extraction with the complete inner typed family

The total-weight compatibility stage retains whole coarse constituents.  The inner rational
typed-leaf extraction must subsequently be applied to the entire localized fine family inside
each survivor; choosing one fine leaf would lose the inner `E2` copy exponent.

This file instantiates the generic outer/inner composition interface.  A canonical inner
degeneration may be proved once for one coarse word and transported to every survivor in the
same exact coarse type class.  At sequence level, outer and inner copy bases multiply while the
inner extraction's final rectangular-volume base is used exactly once.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w x

section Finite

/-- Regard an exact direct sum of localized total-weight constituents as an outer stage.

No fine constituent is selected here: every summand is the realization of the whole localized
fine type-selected tensor. -/
noncomputable def cwTotalWeightLocalizedOuterConstituentStage
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    (source : Tensor3 K Source)
    {I : Type w} [Fintype I]
    (coarseWord : I → PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (fineType : ∀ _c, PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    (outerCopies : ℕ)
    (hcard : Fintype.card I = outerCopies)
    (houter : Restricts source
      (Tensor.indexedDirectSum (fun i : I ↦
        (cwTotalWeightLocalizedFineTypes K q depth n
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n (coarseWord i))
          fineType).realize))) :
    OuterConstituentStage.{u, v, w, u} K source outerCopies :=
  OuterConstituentStage.ofIndexedConstituents K hcard houter

/-- Every constituent of the localized outer stage is isomorphic to the canonical localized
tensor when all coarse words lie in one exact coarse type class. -/
theorem cwTotalWeightLocalizedOuter_isomorphicToReference_of_fixedCoarseType
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
    (outerCopies : ℕ)
    (hcard : Fintype.card I = outerCopies)
    (houter : Restricts source
      (Tensor.indexedDirectSum (fun i : I ↦
        (cwTotalWeightLocalizedFineTypes K q depth n
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n (coarseWord i))
          fineType).realize))) :
    OuterConstituentStage.IsomorphicToReference K
      (cwTotalWeightLocalizedOuterConstituentStage K q depth n source
        coarseWord fineType outerCopies hcard houter)
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n reference)
        fineType).realize := by
  intro i
  change I at i
  change Isomorphic
    (cwTotalWeightLocalizedFineTypes K q depth n
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n (coarseWord i)) fineType).realize
    (cwTotalWeightLocalizedFineTypes K q depth n
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n reference) fineType).realize
  exact cwTotalWeightLocalizedFineTypes_isomorphic_of_mem_sameCoarseType
    K q depth n fineType coarseType reference (coarseWord i)
    hreference (hcoarseWord i)

/-- One canonical degeneration to a naturally indexed *whole* inner family transports to every
same-type outer survivor, with no loss in the inner copy count. -/
theorem cwTotalWeightLocalizedOuter_hasUniformInnerExtraction_of_fixedCoarseType
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
    (hcanonical : PolynomialDegenerates
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n reference)
        fineType).realize
      (Tensor.indexedDirectSum (fun _j : J ↦
        matrixMultiplication (K := K) xSize ySize zSize))) :
    OuterConstituentStage.HasUniformInnerExtraction K
      (cwTotalWeightLocalizedOuterConstituentStage K q depth n source
        coarseWord fineType outerCopies hcardI houter)
      innerCopies xSize ySize zSize := by
  apply OuterConstituentStage.hasUniformInnerExtraction_of_isomorphicReference K
    (cwTotalWeightLocalizedOuterConstituentStage K q depth n source
      coarseWord fineType outerCopies hcardI houter)
    (cwTotalWeightLocalizedFineTypes K q depth n
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n reference)
      fineType).realize
    (cwTotalWeightLocalizedOuter_isomorphicToReference_of_fixedCoarseType
      K q depth n source coarseWord reference coarseType hreference hcoarseWord
      fineType outerCopies hcardI houter)
    hcardJ hcanonical

/-- Finite composed stage: outer quotient survivors times the full canonical inner family.

The dimensions are already the final rectangular dimensions of each inner leaf; this constructor
does not attach or multiply any additional volume factor. -/
noncomputable def cwTotalWeightLocalizedOuter_nestedStage_of_fixedCoarseType
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
    (hcanonical : PolynomialDegenerates
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n reference)
        fineType).realize
      (Tensor.indexedDirectSum (fun _j : J ↦
        matrixMultiplication (K := K) xSize ySize zSize))) :
    NestedLaserVolumeStage K source
      outerCopies innerCopies xSize ySize zSize :=
  OuterConstituentStage.nest (K := K)
    (cwTotalWeightLocalizedOuterConstituentStage K q depth n source
      coarseWord fineType outerCopies hcardI houter)
    (cwTotalWeightLocalizedOuter_hasUniformInnerExtraction_of_fixedCoarseType
      K q depth n source coarseWord reference coarseType hreference hcoarseWord
      fineType outerCopies innerCopies xSize ySize zSize hcardI hcardJ houter hcanonical)

end Finite

section Sequence

/-- A concrete outer total-weight sequence whose summands are whole localized fine families.

The structure stops before inner hashing.  In particular, `outerBase` counts only the retained
coarse constituents. -/
structure CWTotalWeightLocalizedOuterSequenceData
    (K : Type u) [CommRing K] (q depth : ℕ)
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    (T : Tensor3 K Source) (stride : ℕ) (outerBase : ℝ) where
  stride_pos : 0 < stride
  outerBase_pos : 0 < outerBase
  loss : ℕ → ℝ
  count : ℕ → ℕ
  n : ℕ → ℕ
  fineType : ℕ → Leg → PositiveWord CWBlock (2 ^ depth - 1) → ℕ
  I : ℕ → Type w
  [fintypeI : ∀ r, Fintype (I r)]
  coarseWord : ∀ r, I r → PositiveWord (CWTotalWeightCoarseSupport K q depth) (n r)
  card_I : ∀ r, Fintype.card (I r) = count r
  loss_subexponential : Growth.Subexponential loss
  loss_pos : ∀ r, 0 < r → 0 < loss r
  count_pos : ∀ r, 0 < r → 0 < count r
  source_restricts : ∀ r, 0 < r → Restricts
    (Tensor.power T (stride * r))
    (Tensor.indexedDirectSum (fun i : I r ↦
      (cwTotalWeightLocalizedFineTypes K q depth (n r)
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) (n r) (coarseWord r i))
        (fineType r)).realize))
  copy_growth : ∀ r, 0 < r → outerBase ^ r ≤ loss r * (count r : ℝ)

namespace CWTotalWeightLocalizedOuterSequenceData

/-- Forget the CW presentation and expose the generic whole-constituent outer sequence. -/
noncomputable def toOuterConstituentSequenceData
    {K : Type u} [CommRing K] {q depth : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ} {outerBase : ℝ}
    (data : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q depth T stride outerBase) :
    OuterConstituentSequenceData.{u, v, w, u} K T stride outerBase := by
  letI := data.fintypeI
  exact
    { stride_pos := data.stride_pos
      outerBase_pos := data.outerBase_pos
      loss := data.loss
      count := data.count
      loss_subexponential := data.loss_subexponential
      loss_pos := data.loss_pos
      count_pos := data.count_pos
      stage := fun r hr ↦
        cwTotalWeightLocalizedOuterConstituentStage
          K q depth (data.n r) (Tensor.power T (stride * r))
          (data.coarseWord r) (data.fineType r) (data.count r)
          (data.card_I r) (data.source_restricts r hr)
      copy_growth := data.copy_growth }

/-- Certificate-independent data for the copywise inner extraction on a concrete outer
total-weight sequence.

`J r` is the actual full inner selected-address family for the canonical coarse word.  Its exact
cardinality is `innerCount r`; no representative leaf substitutes for this family. -/
structure CanonicalInnerSequenceData
    {K : Type u} [CommRing K] {q depth : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ} {outerBase : ℝ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q depth T stride outerBase)
    (innerBase volumeBase : ℝ) where
  innerBase_pos : 0 < innerBase
  volumeBase_pos : 0 < volumeBase
  innerLoss : ℕ → ℝ
  innerCount : ℕ → ℕ
  xSize : ℕ → ℕ
  ySize : ℕ → ℕ
  zSize : ℕ → ℕ
  reference : ∀ r,
    PositiveWord (CWTotalWeightCoarseSupport K q depth) (outer.n r)
  coarseType : ℕ → CWTotalWeightCoarseSupport K q depth → ℕ
  reference_mem : ∀ r, reference r ∈ positiveTypeClass
    (CWTotalWeightCoarseSupport K q depth) (outer.n r) (coarseType r)
  coarseWord_mem : ∀ r i, outer.coarseWord r i ∈ positiveTypeClass
    (CWTotalWeightCoarseSupport K q depth) (outer.n r) (coarseType r)
  J : ℕ → Type x
  [fintypeJ : ∀ r, Fintype (J r)]
  card_J : ∀ r, Fintype.card (J r) = innerCount r
  canonical_degenerates : ∀ r, 0 < r → PolynomialDegenerates
    (cwTotalWeightLocalizedFineTypes K q depth (outer.n r)
      (positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) (outer.n r) (reference r))
      (outer.fineType r)).realize
    (Tensor.indexedDirectSum (fun _j : J r ↦
      matrixMultiplication (K := K) (xSize r) (ySize r) (zSize r)))
  innerLoss_subexponential : Growth.Subexponential innerLoss
  innerLoss_pos : ∀ r, 0 < r → 0 < innerLoss r
  innerCount_pos : ∀ r, 0 < r → 0 < innerCount r
  xSize_pos : ∀ r, 0 < r → 0 < xSize r
  ySize_pos : ∀ r, 0 < r → 0 < ySize r
  zSize_pos : ∀ r, 0 < r → 0 < zSize r
  inner_copy_growth : ∀ r, 0 < r →
    innerBase ^ r ≤ innerLoss r * (innerCount r : ℝ)
  volume_growth : ∀ r, 0 < r →
    volumeBase ^ r ≤ (((xSize r * ySize r * zSize r : ℕ) : ℝ))

namespace CanonicalInnerSequenceData

/-- Transport the canonical full inner family to every outer survivor at level `r`. -/
theorem hasUniformInnerExtraction
    {K : Type u} [CommRing K] {q depth : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ} {outerBase innerBase volumeBase : ℝ}
    {outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q depth T stride outerBase}
    (data : CanonicalInnerSequenceData.{u, v, w, x}
      outer innerBase volumeBase)
    (r : ℕ) (hr : 0 < r) :
    OuterConstituentStage.HasUniformInnerExtraction K
      (outer.toOuterConstituentSequenceData.stage r hr)
      (data.innerCount r) (data.xSize r) (data.ySize r) (data.zSize r) := by
  letI := outer.fintypeI
  letI := data.fintypeJ
  exact cwTotalWeightLocalizedOuter_hasUniformInnerExtraction_of_fixedCoarseType
    K q depth (outer.n r) (Tensor.power T (stride * r))
    (outer.coarseWord r) (data.reference r) (data.coarseType r)
    (data.reference_mem r) (data.coarseWord_mem r)
    (outer.fineType r) (outer.count r) (data.innerCount r)
    (data.xSize r) (data.ySize r) (data.zSize r)
    (outer.card_I r) (data.card_J r) (outer.source_restricts r hr)
    (data.canonical_degenerates r hr)

/-- Concrete nested sequence before flattening: it records outer quotient growth and inner `E2`
growth separately, and one final rectangular-volume growth inequality. -/
noncomputable def toNestedLaserVolumeSequenceData
    {K : Type u} [CommRing K] {q depth : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ} {outerBase innerBase volumeBase : ℝ}
    {outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q depth T stride outerBase}
    (data : CanonicalInnerSequenceData.{u, v, w, x}
      outer innerBase volumeBase) :
    NestedLaserVolumeSequenceData K T stride outerBase innerBase volumeBase := by
  exact OuterConstituentSequenceData.toNestedLaserVolumeSequenceData (K := K)
    outer.toOuterConstituentSequenceData
    data.innerBase_pos data.volumeBase_pos
    data.innerLoss data.innerCount data.xSize data.ySize data.zSize
    data.innerLoss_subexponential data.innerLoss_pos data.innerCount_pos
    data.xSize_pos data.ySize_pos data.zSize_pos
    (fun r hr ↦ data.hasUniformInnerExtraction r hr)
    data.inner_copy_growth data.volume_growth

/-- Final generic product-base endpoint.  Only copy bases multiply; `volumeBase` appears once. -/
noncomputable def toSubexponentialLaserVolumeSequence
    {K : Type u} [CommRing K] {q depth : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ} {outerBase innerBase volumeBase : ℝ}
    {outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q depth T stride outerBase}
    (data : CanonicalInnerSequenceData.{u, v, w, x}
      outer innerBase volumeBase) :
    SubexponentialLaserVolumeSequence K T stride
      (outerBase * innerBase) volumeBase :=
  NestedLaserVolumeSequenceData.toSubexponentialLaserVolumeSequence (K := K)
    data.toNestedLaserVolumeSequenceData

/-- Base-two endpoint: outer retained exponent plus inner `E2`, with no second volume term. -/
noncomputable def toSubexponentialLaserVolumeSequence_addRetained
    {K : Type u} [CommRing K] {q depth : ℕ}
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source} {stride : ℕ}
    {outerRetained innerRetained volumeBase : ℝ}
    {outer : CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q depth T stride ((2 : ℝ) ^ ((stride : ℝ) * outerRetained))}
    (data : CanonicalInnerSequenceData.{u, v, w, x} outer
      ((2 : ℝ) ^ ((stride : ℝ) * innerRetained)) volumeBase) :
    SubexponentialLaserVolumeSequence K T stride
      ((2 : ℝ) ^ ((stride : ℝ) * (outerRetained + innerRetained))) volumeBase :=
  OuterConstituentSequenceData.toSubexponentialLaserVolumeSequence_addRetained (K := K)
    outer.toOuterConstituentSequenceData
    data.volumeBase_pos data.innerLoss data.innerCount data.xSize data.ySize data.zSize
    data.innerLoss_subexponential data.innerLoss_pos data.innerCount_pos
    data.xSize_pos data.ySize_pos data.zSize_pos
    (fun r hr ↦ data.hasUniformInnerExtraction r hr)
    data.inner_copy_growth data.volume_growth

end CanonicalInnerSequenceData

end CWTotalWeightLocalizedOuterSequenceData

end Sequence

end AlgebraicComplexity.Examples
