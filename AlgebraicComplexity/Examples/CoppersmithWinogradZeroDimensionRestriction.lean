/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroDimension
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSlice

/-!
# Explicit restrictions for zero-coordinate CW interfaces

`CoppersmithWinogradZeroDimension` proves that an exact zero-`Z` interface has one common local
dimension `q ^ e`.  This module retains the actual coordinate maps witnessing that fact.  It
iterates the committed chunk-level one-slice certificates only along the recovered supported
word, then transports their product dimension along the exact complete-split identity.

Keeping this map layer separate from the numerical dimension layer bounds the import and
elaboration cost of both clients.  It also exposes the maps needed by the later shared-`Z`
C-tensor coherence theorem.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-- Explicit one-slice certificates aligned with a supported outer word whose `Z` address is the
constant zero-chunk word.  Only the chunk constituents that occur in the word are certified; no
claim is made about the nonzero-`Z` part of the ambient chunk support. -/
noncomputable def cwZeroChunkOuterWordData
    (K : Type u) [CommRing K] (q depth : ℕ) :
    (n : ℕ) →
    (word : PositiveWord (cwChunkPartitionedTensor K q depth).support n) →
    positiveSupportWordBlockAddress
        (cwChunkPartitionedTensor K q depth).support n word .Z =
      positiveWordConst (cwZeroChunkWord depth) n →
    OneSliceRestriction.PositiveSupportWordData
      (cwChunkPartitionedTensor K q depth)
      (fun support ↦ q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X))) n word
  | 0, word, hz => cwZeroChunkOneSliceRestriction K q depth word hz
  | n + 1, word, hz =>
      ⟨cwZeroChunkOuterWordData K q depth n word.1 (congrArg Prod.fst hz),
        cwZeroChunkOneSliceRestriction K q depth word.2 (congrArg Prod.snd hz)⟩

/-- Map-level strengthening of the uniform zero-interface dimension law.  Every selected
zero-`Z` constituent carries explicit maps to `⟨1,q^e,1⟩`, with `e` fixed by the stored exact
complete-split profile. -/
noncomputable def cwSelectedExactInterfaceConstituentOneSliceRestriction_zeroZ
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    OneSliceRestriction
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).constituent address.1)
      (q ^ cwZeroInterfaceQExponent term) := by
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
  let data := cwZeroChunkOuterWordData K q depth n outerWord hzWords
  let C := OneSliceRestriction.ofPositivePowerConstituentData
    (cwChunkPartitionedTensor K q depth)
    (fun support ↦ q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X)))
    n outerWord data
  have hdimension :
      positiveWordProduct
          (fun support : (cwChunkPartitionedTensor K q depth).support ↦
            q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X)))
          n outerWord = q ^ cwZeroInterfaceQExponent term := by
    rw [positiveWordProduct_eq_fin_prod, Finset.prod_pow_eq_pow_sum,
      cwSelectedExactInterfaceSupportedWord_sum_middleCount
        K q term hmultiplicity address]
  have C' := C.castDimension hdimension
  change OneSliceRestriction
    (((cwChunkPartitionedTensor K q depth).positivePower n).constituent address.1) _
  rw [← haddress]
  exact C'

/-- The proposition-level restriction obtained by forgetting the explicit maps.  The stronger
certificate above is retained for the shared-`Z` C-tensor assembly. -/
theorem cwSelectedExactInterface_constituent_restricts_oneSlice_of_zeroZ
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    Restricts
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).constituent address.1)
      (matrixMultiplication (K := K) 1 (q ^ cwZeroInterfaceQExponent term) 1) := by
  let C := cwSelectedExactInterfaceConstituentOneSliceRestriction_zeroZ
    K q term hmultiplicity hz address
  exact ⟨C.legMap, C.map_eq⟩

end AlgebraicComplexity.Examples
