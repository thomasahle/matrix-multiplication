/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSliceBase
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroWord
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroWordDimension
import AlgebraicComplexity.MatrixMultiplication.OneSlicePartitionedPower

/-!
# Explicit one-slice maps for zero-coordinate CW constituents

The base restrictions and their common zero-`Z` map are proved in the lightweight
`CoppersmithWinogradZeroOneSliceBase` module.  This file iterates those exposed maps along any
supported zero-`Z` word and obtains an explicit one-slice restriction for every zero-`Z` recursive
chunk. No representative selection, entropy estimate, or asymptotic argument occurs here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

section SupportedWords

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Every supported zero-`Z` base CW constituent has an explicit one-slice restriction with its
canonical second matrix dimension. -/
noncomputable def cwZeroBaseOneSliceRestriction
    (support : cwBlockSupport) (hz : support.1 .Z = .zero) :
    OneSliceRestriction (cwSupportedConstituent K q support)
      (cwBaseConstituentDimension q support .Y) := by
  classical
  refine Classical.choice ?_
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by simpa [cwSupportedConstituent, cw200, cwBlockAddress,
      cwBaseConstituentDimension, cwBlockMatrixDimensions] using
      cw200OneSliceRestriction K q⟩
  · exact ⟨by simpa [cwSupportedConstituent, cw020, cwBlockAddress,
      cwBaseConstituentDimension, cwBlockMatrixDimensions] using
      cw020OneSliceRestriction K q⟩
  · simp [cw002, cwBlockAddress] at hz
  · simp [cw011, cwBlockAddress] at hz
  · simp [cw101, cwBlockAddress] at hz
  · exact ⟨by simpa [cwSupportedConstituent, cw110, cwBlockAddress,
      cwBaseConstituentDimension, cwBlockMatrixDimensions] using
      cw110OneSliceRestriction K q⟩

/-- Word-aligned exposed certificates for every letter of a supported zero-`Z` word. -/
noncomputable def cwZeroBaseWordData
    (r : ℕ) (word : PositiveWord cwBlockSupport r)
    (hz : positiveSupportWordBlockAddress cwBlockSupport r word .Z =
      positiveWordConst .zero r) :
    OneSliceRestriction.PositiveSupportWordData
      (cwPartitionedTensor K q)
      (fun support ↦ cwBaseConstituentDimension q support .Y) r word := by
  induction r with
  | zero =>
      exact cwZeroBaseOneSliceRestriction K q word hz
  | succ r ih =>
      exact ⟨ih word.1 (congrArg Prod.fst hz),
        cwZeroBaseOneSliceRestriction K q word.2 (congrArg Prod.snd hz)⟩

/-- A whole supported zero-`Z` base word has an explicit one-slice restriction. -/
noncomputable def cwZeroBaseWordOneSliceRestriction
    (r : ℕ) (word : PositiveWord cwBlockSupport r)
    (hz : positiveSupportWordBlockAddress cwBlockSupport r word .Z =
      positiveWordConst .zero r) :
    OneSliceRestriction
      ((cwPartitionedTensor K q).positiveSupportWordTensor r word)
      (positiveWordProduct
        (fun support ↦ cwBaseConstituentDimension q support .Y) r word) :=
  OneSliceRestriction.ofPositiveSupportWordData
    (cwPartitionedTensor K q)
    (fun support ↦ cwBaseConstituentDimension q support .Y) r word
    (cwZeroBaseWordData K q r word hz)

/-- Every zero-`Z` recursive chunk has an explicit restriction to `⟨1,q^k,1⟩`, with `k` read
from its encoded X split word. -/
noncomputable def cwZeroChunkOneSliceRestriction
    (depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support)
    (hz : support.1 .Z = cwZeroChunkWord depth) :
    OneSliceRestriction
      ((cwChunkPartitionedTensor K q depth).constituent support.1)
      (q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X))) := by
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
  let data := cwZeroBaseWordData K q (2 ^ depth - 1) word hzWord
  let C := OneSliceRestriction.ofPositivePowerConstituentData
    (cwPartitionedTensor K q)
    (fun base ↦ cwBaseConstituentDimension q base .Y)
    (2 ^ depth - 1) word data
  have hdimension :
      positiveWordProduct
          (fun base ↦ cwBaseConstituentDimension q base .Y)
          (2 ^ depth - 1) word =
        q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X)) := by
    rw [positiveWordProduct_cwBaseDimension_Y_eq_pow_middleCount_of_z_eq_const
      q _ word hzWord]
    congr 1
    rw [← splitWordMiddleCount_cwChunkSplitWord_positiveSupportWordBlockAddress depth word,
      haddress']
  have C' := C.castDimension hdimension
  change OneSliceRestriction
    (((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).constituent support.1) _
  exact haddress' ▸ C'

end SupportedWords

end AlgebraicComplexity.Examples
