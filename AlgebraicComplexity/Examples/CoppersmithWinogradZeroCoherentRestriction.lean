/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroDimensionRestriction
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSliceBase
import AlgebraicComplexity.MatrixMultiplication.SharedOneSliceFiber

/-!
# Coherent zero-coordinate restrictions for exact CW interfaces

The three base CW constituents with zero `Z` label use definitionally the same map on that block.
This module retains that fact while forming both nested positive powers.  It therefore upgrades the
constituentwise restrictions of `CoppersmithWinogradZeroDimensionRestriction` to one global
shared-leg C-tensor retyping and fuses the complete selected family into a single one-slice matrix
multiplication tensor.

The construction is finite and exact.  It assumes neither a restriction of the assembled family
nor a type-class cardinality estimate.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-- Canonical map on the zero `Z` block of one base CW constituent. -/
def cwZeroBaseCanonicalZMap
    (K : Type u) [CommRing K] (q : ℕ) :
    CWPartitionBlockSpace K q .Z .zero →ₗ[K] MMSpace K 1 1 1 .Z :=
  cw200OneSliceMap K q .Z

/-- A supported base constituent with zero `Z` label, together with its explicit restriction and
the retained proof that its `Z` map is the canonical one. -/
noncomputable def cwZeroBaseCoherentRestriction
    (K : Type u) [CommRing K] (q : ℕ)
    (support : cwBlockSupport) (hz : support.1 .Z = .zero) :
    { C : OneSliceRestriction (cwSupportedConstituent K q support)
        (cwBaseConstituentDimension q support .Y) //
      HEq (C.legMap .Z) (cwZeroBaseCanonicalZMap K q) } := by
  classical
  refine Classical.choice ?_
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl
  · let C : OneSliceRestriction
        (cwPartitionConstituent K q (ofLegs .last .zero .zero)) 1 :=
      { legMap := cw200OneSliceMap K q
        map_eq := by
          rw [cwPartitionConstituent_ofLegs]
          exact map_cw200OneSliceMap K q }
    exact ⟨⟨C, HEq.rfl⟩⟩
  · let C : OneSliceRestriction
        (cwPartitionConstituent K q (ofLegs .zero .last .zero)) 1 :=
      { legMap := cw020OneSliceMap K q
        map_eq := by
          rw [cwPartitionConstituent_ofLegs]
          exact map_cw020OneSliceMap K q }
    have hmap : cw020OneSliceMap K q .Z = cw200OneSliceMap K q .Z :=
      (cwZeroBaseOneSliceMap_Z_coherent K q).1.symm
    refine ⟨⟨C, ?_⟩⟩
    change HEq (cw020OneSliceMap K q .Z) (cw200OneSliceMap K q .Z)
    exact heq_of_eq hmap
  · simp [cw002, cwBlockAddress] at hz
  · simp [cw011, cwBlockAddress] at hz
  · simp [cw101, cwBlockAddress] at hz
  · let C : OneSliceRestriction
        (cwPartitionConstituent K q (ofLegs .middle .middle .zero)) q :=
      { legMap := cw110OneSliceMap K q
        map_eq := by
          rw [cwPartitionConstituent_ofLegs]
          exact map_cw110OneSliceMap K q }
    have hmap : cw110OneSliceMap K q .Z = cw200OneSliceMap K q .Z :=
      (cwZeroBaseOneSliceMap_Z_coherent K q).2.symm.trans
        (cwZeroBaseOneSliceMap_Z_coherent K q).1.symm
    refine ⟨⟨C, ?_⟩⟩
    change HEq (cw110OneSliceMap K q .Z) (cw200OneSliceMap K q .Z)
    exact heq_of_eq hmap

/-- Canonical shared-leg map for a positive word of base zero-`Z` blocks. -/
def cwZeroBaseWordCanonicalZMap
    (K : Type u) [CommRing K] (q : ℕ) :
    (r : ℕ) →
    PositivePowerBlockSpace K (CWPartitionBlockSpace K q) r .Z
        (positiveWordConst .zero r) →ₗ[K]
      MMSpace K 1 1 1 .Z
  | 0 => cwZeroBaseCanonicalZMap K q
  | r + 1 => OneSliceProduct.coordinateProductMapAfter
      (OneSliceProduct.indexProductEquiv 1 1 .Z)
      (cwZeroBaseWordCanonicalZMap K q r) (cwZeroBaseCanonicalZMap K q)

/-- Coherent one-slice data for an arbitrary supported positive word in the base zero-`Z` fibre. -/
noncomputable def cwZeroBaseWordCoherentRestriction
    (K : Type u) [CommRing K] (q : ℕ) :
    (r : ℕ) → (word : PositiveWord cwBlockSupport r) →
    positiveSupportWordBlockAddress cwBlockSupport r word .Z =
        positiveWordConst .zero r →
    { C : OneSliceRestriction
        ((cwPartitionedTensor K q).positiveSupportWordTensor r word)
        (positiveWordProduct (fun support ↦ cwBaseConstituentDimension q support .Y) r word) //
      HEq (C.legMap .Z) (cwZeroBaseWordCanonicalZMap K q r) }
  | 0, word, hz => cwZeroBaseCoherentRestriction K q word hz
  | r + 1, word, hz => by
      have hzLeft : positiveSupportWordBlockAddress cwBlockSupport r word.1 .Z =
          positiveWordConst .zero r := congrArg Prod.fst hz
      have hzRight : word.2.1 .Z = .zero := congrArg Prod.snd hz
      let left := cwZeroBaseWordCoherentRestriction K q r word.1 hzLeft
      let right := cwZeroBaseCoherentRestriction K q word.2 hzRight
      let C := left.1.external right.1
      refine ⟨C, ?_⟩
      change
        HEq (OneSliceProduct.coordinateProductMapAfter
          (OneSliceProduct.indexProductEquiv 1 1 .Z)
          (left.1.legMap .Z) (right.1.legMap .Z))
          (OneSliceProduct.coordinateProductMapAfter
          (OneSliceProduct.indexProductEquiv 1 1 .Z)
          (cwZeroBaseWordCanonicalZMap K q r) (cwZeroBaseCanonicalZMap K q))
      let family :=
        (BlockModuleFamily.of (K := K) (CWPartitionBlockSpace K q)).positivePower r
      congr 1
      · exact congrArg (fun label ↦
          PositivePowerBlockSpace K (CWPartitionBlockSpace K q) r .Z label) hzLeft
      · exact congrArg (fun label ↦ CWPartitionBlockSpace K q .Z label) hzRight
      · exact congr_arg_heq (fun label ↦ family.addCommMonoid .Z label) hzLeft
      · exact congr_arg_heq (fun label ↦ family.module .Z label) hzLeft
      · exact congr_arg_heq (fun label : CWBlock ↦
          (inferInstance : AddCommMonoid (CWBlockIndex q label → K))) hzRight
      · exact congr_arg_heq
          (fun label ↦ Pi.Function.module (CWBlockIndex q label) K K) hzRight
      · exact left.2
      · exact right.2

/-- Canonical map on the all-zero `Z` block of one recursive CW chunk. -/
def cwZeroChunkCanonicalZMap
    (K : Type u) [CommRing K] (q depth : ℕ) :
    PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1) .Z
        (cwZeroChunkWord depth) →ₗ[K] MMSpace K 1 1 1 .Z :=
  cwZeroBaseWordCanonicalZMap K q (2 ^ depth - 1)

/-- Coherent explicit restriction for every supported zero-`Z` recursive chunk. -/
noncomputable def cwZeroChunkCoherentRestriction
    (K : Type u) [CommRing K] (q depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support)
    (hz : support.1 .Z = cwZeroChunkWord depth) :
    { C : OneSliceRestriction
        ((cwChunkPartitionedTensor K q depth).constituent support.1)
        (q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X))) //
      HEq (C.legMap .Z) (cwZeroChunkCanonicalZMap K q depth) } := by
  let word : PositiveWord cwBlockSupport (2 ^ depth - 1) := by
    simpa only [cwPartitionedTensor] using
      (cwChunkSupportedWordOfAddress K q depth support)
  have haddress := positiveSupportWordBlockAddress_cwChunkSupportedWordOfAddress
    K q depth support
  have haddress' :
      positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word = support.1 := by
    simpa only [word, cwPartitionedTensor] using haddress
  have hzWord :
      positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word .Z =
        positiveWordConst .zero (2 ^ depth - 1) := by
    rw [haddress', hz]
    rfl
  let data := cwZeroBaseWordCoherentRestriction K q (2 ^ depth - 1) word hzWord
  have hdimensionWord :
      positiveWordProduct
          (fun base ↦ cwBaseConstituentDimension q base .Y)
          (2 ^ depth - 1) word =
        q ^ splitWordMiddleCount (cwChunkSplitWord depth
          (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word .X)) := by
    rw [positiveWordProduct_cwBaseDimension_Y_eq_pow_middleCount_of_z_eq_const
      q _ word hzWord]
    congr 1
    rw [← splitWordMiddleCount_cwChunkSplitWord_positiveSupportWordBlockAddress depth word]
  let dataDimension :
      { C : OneSliceRestriction
          ((cwPartitionedTensor K q).positiveSupportWordTensor (2 ^ depth - 1) word)
          (q ^ splitWordMiddleCount (cwChunkSplitWord depth
            (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word .X))) //
        HEq (C.legMap .Z) (cwZeroBaseWordCanonicalZMap K q (2 ^ depth - 1)) } := by
    rw [← hdimensionWord]
    exact data
  have hconst :=
    (cwPartitionedTensor K q).positivePower_constituent_positiveSupportWordBlockAddress
      (2 ^ depth - 1) word
  change
    ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).constituent
        (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word) =
      (cwPartitionedTensor K q).positiveSupportWordTensor (2 ^ depth - 1) word at hconst
  let dataConstituent :
      { C : OneSliceRestriction
          (((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).constituent
            (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word))
          (q ^ splitWordMiddleCount (cwChunkSplitWord depth
            (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word .X))) //
        HEq (C.legMap .Z) (cwZeroBaseWordCanonicalZMap K q (2 ^ depth - 1)) } := by
    rw [hconst]
    exact dataDimension
  change
    { C : OneSliceRestriction
        (((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).constituent support.1)
        (q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X))) //
      HEq (C.legMap .Z) (cwZeroBaseWordCanonicalZMap K q (2 ^ depth - 1)) }
  rw [← haddress']
  exact dataConstituent

/-- Canonical shared-leg map for a positive word of recursive zero-`Z` chunks. -/
def cwZeroInterfaceCanonicalZMap
    (K : Type u) [CommRing K] (q depth : ℕ) :
    (n : ℕ) →
    PositivePowerBlockSpace K
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1))
        n .Z (positiveWordConst (cwZeroChunkWord depth) n) →ₗ[K]
      MMSpace K 1 1 1 .Z
  | 0 => cwZeroChunkCanonicalZMap K q depth
  | n + 1 => OneSliceProduct.coordinateProductMapAfter
      (OneSliceProduct.indexProductEquiv 1 1 .Z)
      (cwZeroInterfaceCanonicalZMap K q depth n)
      (cwZeroChunkCanonicalZMap K q depth)

/-- Coherent one-slice data for every supported outer word in the recursive zero-`Z` fibre. -/
noncomputable def cwZeroChunkOuterWordCoherentRestriction
    (K : Type u) [CommRing K] (q depth : ℕ) :
    (n : ℕ) →
    (word : PositiveWord (cwChunkPartitionedTensor K q depth).support n) →
    positiveSupportWordBlockAddress
        (cwChunkPartitionedTensor K q depth).support n word .Z =
      positiveWordConst (cwZeroChunkWord depth) n →
    { C : OneSliceRestriction
        ((cwChunkPartitionedTensor K q depth).positiveSupportWordTensor n word)
        (positiveWordProduct
          (fun support ↦ q ^ splitWordMiddleCount
            (cwChunkSplitWord depth (support.1 .X))) n word) //
      HEq (C.legMap .Z) (cwZeroInterfaceCanonicalZMap K q depth n) }
  | 0, word, hz => cwZeroChunkCoherentRestriction K q depth word hz
  | n + 1, word, hz => by
      have hzLeft :
          positiveSupportWordBlockAddress
              (cwChunkPartitionedTensor K q depth).support n word.1 .Z =
            positiveWordConst (cwZeroChunkWord depth) n :=
        congrArg Prod.fst hz
      have hzRight : word.2.1 .Z = cwZeroChunkWord depth :=
        congrArg Prod.snd hz
      let left := cwZeroChunkOuterWordCoherentRestriction K q depth n word.1 hzLeft
      let right := cwZeroChunkCoherentRestriction K q depth word.2 hzRight
      let C := left.1.external right.1
      refine ⟨C, ?_⟩
      change
        HEq (OneSliceProduct.coordinateProductMapAfter
          (OneSliceProduct.indexProductEquiv 1 1 .Z)
          (left.1.legMap .Z) (right.1.legMap .Z))
          (OneSliceProduct.coordinateProductMapAfter
          (OneSliceProduct.indexProductEquiv 1 1 .Z)
          (cwZeroInterfaceCanonicalZMap K q depth n)
          (cwZeroChunkCanonicalZMap K q depth))
      let chunkFamily := BlockModuleFamily.of (K := K)
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1))
      let outerFamily := chunkFamily.positivePower n
      congr 1
      · exact congrArg (fun label ↦
          PositivePowerBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1))
            n .Z label) hzLeft
      · exact congrArg (fun label ↦
          PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1) .Z label)
          hzRight
      · exact congr_arg_heq (fun label ↦ outerFamily.addCommMonoid .Z label) hzLeft
      · exact congr_arg_heq (fun label ↦ outerFamily.module .Z label) hzLeft
      · exact congr_arg_heq (fun label ↦ chunkFamily.addCommMonoid .Z label) hzRight
      · exact congr_arg_heq (fun label ↦ chunkFamily.module .Z label) hzRight
      · exact left.2
      · exact right.2

/-- Every constituent of an exact zero-`Z` interface carries the canonical shared `Z` map, not
merely a proposition-level restriction to a one-slice matrix tensor. -/
noncomputable def cwSelectedExactInterfaceConstituentCoherentRestriction_zeroZ
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    { C : OneSliceRestriction
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).constituent address.1)
        (q ^ cwZeroInterfaceQExponent term) //
      HEq (C.legMap .Z) (cwZeroInterfaceCanonicalZMap K q depth n) } := by
  let outerWord := cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address
  have haddress := positiveSupportWordBlockAddress_cwSelectedExactInterfaceSupportedWord
    K q term hmultiplicity address
  have hshared :=
    (cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber
      K q term hmultiplicity hz).1 address.1 address.2
  have hzWords :
      positiveSupportWordBlockAddress (cwChunkPartitionedTensor K q depth).support n
          outerWord .Z = positiveWordConst (cwZeroChunkWord depth) n := by
    rw [haddress]
    exact hshared
  let data := cwZeroChunkOuterWordCoherentRestriction K q depth n outerWord hzWords
  have hdimension :
      positiveWordProduct
          (fun support : (cwChunkPartitionedTensor K q depth).support ↦
            q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X)))
          n outerWord = q ^ cwZeroInterfaceQExponent term := by
    rw [positiveWordProduct_eq_fin_prod, Finset.prod_pow_eq_pow_sum,
      cwSelectedExactInterfaceSupportedWord_sum_middleCount
        K q term hmultiplicity address]
  let dataDimension :
      { C : OneSliceRestriction
          ((cwChunkPartitionedTensor K q depth).positiveSupportWordTensor n outerWord)
          (q ^ cwZeroInterfaceQExponent term) //
        HEq (C.legMap .Z) (cwZeroInterfaceCanonicalZMap K q depth n) } := by
    rw [← hdimension]
    exact data
  have hconst :=
    (cwChunkPartitionedTensor K q depth).positivePower_constituent_positiveSupportWordBlockAddress
      n outerWord
  let dataConstituent :
      { C : OneSliceRestriction
          (((cwChunkPartitionedTensor K q depth).positivePower n).constituent
            (positiveSupportWordBlockAddress
              (cwChunkPartitionedTensor K q depth).support n outerWord))
          (q ^ cwZeroInterfaceQExponent term) //
        HEq (C.legMap .Z) (cwZeroInterfaceCanonicalZMap K q depth n) } := by
    rw [hconst]
    exact dataDimension
  change
    { C : OneSliceRestriction
        (((cwChunkPartitionedTensor K q depth).positivePower n).constituent address.1)
        (q ^ cwZeroInterfaceQExponent term) //
      HEq (C.legMap .Z) (cwZeroInterfaceCanonicalZMap K q depth n) }
  rw [← haddress]
  exact dataConstituent

/-- Canonical shared map after retyping the zero-`Z` target into the constituent spaces of the
one-slice C-tensor. -/
noncomputable def cwZeroInterfaceCanonicalConstituentZMap
    (K : Type u) [CommRing K] (q : ℕ) {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) (n : ℕ) :
    PositivePowerBlockSpace K
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1))
        n .Z (cwZeroInterfaceLegWord depth n) →ₗ[K]
      CTensor.ConstituentSpace
        (MMSpace K 1 (q ^ cwZeroInterfaceQExponent term) 1 .X)
        (MMSpace K 1 (q ^ cwZeroInterfaceQExponent term) 1 .Y)
        (MMSpace K 1 (q ^ cwZeroInterfaceQExponent term) 1 .Z) .Z :=
  (CTensor.oneSliceConstituentEquiv K (q ^ cwZeroInterfaceQExponent term) .Z).symm.toLinearMap
    ∘ₗ cwZeroInterfaceCanonicalZMap K q depth n

/-- The complete exact zero-`Z` support, equipped with coherent constituent maps for the generic
shared-fibre fusion theorem. -/
noncomputable def cwSelectedExactInterfaceTerm_zeroZ_sharedOneSliceData
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0) :
    CTensor.SharedOneSliceFiberData
      (cwSelectedExactInterfaceTerm K q term hmultiplicity)
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support
      (cwZeroInterfaceLegWord depth n)
      (q ^ cwZeroInterfaceQExponent term) where
  certificate := fun address ↦
    (cwSelectedExactInterfaceConstituentCoherentRestriction_zeroZ
      K q term hmultiplicity hz address).1
  zMap := cwZeroInterfaceCanonicalConstituentZMap K q term n
  z_coherent := by
    intro address
    change HEq
      ((CTensor.oneSliceConstituentEquiv K (q ^ cwZeroInterfaceQExponent term) .Z).symm.toLinearMap
        ∘ₗ
          (cwSelectedExactInterfaceConstituentCoherentRestriction_zeroZ
            K q term hmultiplicity hz address).1.legMap .Z)
      ((CTensor.oneSliceConstituentEquiv K (q ^ cwZeroInterfaceQExponent term) .Z).symm.toLinearMap
        ∘ₗ cwZeroInterfaceCanonicalZMap K q depth n)
    have hshared :=
      (cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber
        K q term hmultiplicity hz).1 address.1 address.2
    let chunkFamily := BlockModuleFamily.of (K := K)
      (PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1))
    let interfaceFamily := chunkFamily.positivePower n
    congr 1
    · exact congrArg (fun label ↦
        PositivePowerBlockSpace K
          (PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1))
          n .Z label) hshared
    · exact congr_arg_heq (fun label ↦ interfaceFamily.addCommMonoid .Z label) hshared
    · exact congr_arg_heq (fun label ↦ interfaceFamily.module .Z label) hshared
    · exact (cwSelectedExactInterfaceConstituentCoherentRestriction_zeroZ
        K q term hmultiplicity hz address).2

/-- **Exact zero-coordinate fusion.**  The entire selected interface, with no representative
selection and no loss factor, restricts to `⟨1, |support| q^e, 1⟩`.  The common-leg map is
constructed explicitly by the preceding definitions. -/
theorem cwSelectedExactInterfaceTerm_zeroZ_restricts_fusedOneSlice
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0) :
    Restricts (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      (matrixMultiplication (K := K) 1
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
          q ^ cwZeroInterfaceQExponent term) 1) := by
  let D := cwSelectedExactInterfaceTerm_zeroZ_sharedOneSliceData
    K q term hmultiplicity hz
  have hsupport := cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber
    K q term hmultiplicity hz
  exact D.restricts_oneSliceMatrixMultiplication_of_support
    hsupport.2.1 hsupport.2.2 hsupport.1

end AlgebraicComplexity.Examples
