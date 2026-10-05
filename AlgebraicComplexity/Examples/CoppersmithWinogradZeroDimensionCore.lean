/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroWordDimension
import AlgebraicComplexity.Examples.CoppersmithWinogradExactSelectionCore
import AlgebraicComplexity.Tensor.PositiveWordConst

/-!
# Finite dimension data for zero-coordinate CW interfaces

This lightweight core reconstructs the supported chunk word underlying one selected exact
interface address and defines its product dimensions.  On a zero-`Z` chunk it proves the exact
shape `⟨1,q^k,1⟩`, where `k` is the middle-digit count of the encoded `X` word.

The outer proof that every selected address is zero-`Z` and that its total exponent is fixed by
the stored complete-split profile lives in `CoppersmithWinogradZeroDimension`.  Separating the
layers keeps the finite dimension client independent of compatibility cleanup.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-- A supported CW chunk whose Z block is the all-zero word has dimensions
`⟨1,q^k,1⟩`, with `k` read from its encoded X split word. -/
theorem cwChunkConstituentDimension_zeroZ
    (K : Type u) [CommRing K] (q depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support)
    (hz : support.1 .Z = positiveWordConst .zero (2 ^ depth - 1)) :
    cwChunkConstituentDimension K q depth support .X = 1 ∧
      cwChunkConstituentDimension K q depth support .Y =
        q ^ splitWordMiddleCount (cwChunkSplitWord depth (support.1 .X)) ∧
      cwChunkConstituentDimension K q depth support .Z = 1 := by
  let word : PositiveWord cwBlockSupport (2 ^ depth - 1) :=
    cwChunkSupportedWordOfAddress K q depth support
  have haddress :
      positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word = support.1 :=
    positiveSupportWordBlockAddress_cwChunkSupportedWordOfAddress K q depth support
  have hzWord : positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word .Z =
      positiveWordConst .zero (2 ^ depth - 1) := by
    rw [haddress, hz]
  refine ⟨?_, ?_, ?_⟩
  · change positiveWordProduct
      (fun s ↦ cwBaseConstituentDimension q s .X) (2 ^ depth - 1) word = 1
    exact positiveWordProduct_cwBaseDimension_X_eq_one_of_z_eq_const q _ word hzWord
  · change positiveWordProduct
      (fun s ↦ cwBaseConstituentDimension q s .Y) (2 ^ depth - 1) word = _
    rw [positiveWordProduct_cwBaseDimension_Y_eq_pow_middleCount_of_z_eq_const
      q _ word hzWord]
    congr 1
    rw [← splitWordMiddleCount_cwChunkSplitWord_positiveSupportWordBlockAddress depth word,
      haddress]
  · change positiveWordProduct
      (fun s ↦ cwBaseConstituentDimension q s .Z) (2 ^ depth - 1) word = 1
    exact positiveWordProduct_cwBaseDimension_Z_eq_one_of_z_eq_const q _ word hzWord

/-- Recover the supported word of chunk constituents underlying one address of an exact selected
interface. -/
noncomputable def cwSelectedExactInterfaceSupportedWord
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    PositiveWord (cwChunkPartitionedTensor K q depth).support n := by
  classical
  have hselected := address.2
  change address.1 ∈
    ((cwChunkPartitionedTensor K q depth).selectEncodedCompleteSplitProfiles
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c)).support at hselected
  have hambient :=
    ((cwChunkPartitionedTensor K q depth).mem_selectEncodedCompleteSplitProfiles_support
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c) address.1).mp hselected |>.1
  let P := cwChunkPartitionedTensor K q depth
  have hexists :=
    P.exists_positiveSupportWord_of_mem_positivePower_support_recursive n hambient
  exact Classical.choose hexists

/-- Transposing the recovered chunk word gives back the selected outer address. -/
theorem positiveSupportWordBlockAddress_cwSelectedExactInterfaceSupportedWord
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    positiveSupportWordBlockAddress (cwChunkPartitionedTensor K q depth).support n
        (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address) = address.1 := by
  classical
  have hselected := address.2
  change address.1 ∈
    ((cwChunkPartitionedTensor K q depth).selectEncodedCompleteSplitProfiles
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c)).support at hselected
  have hambient :=
    ((cwChunkPartitionedTensor K q depth).mem_selectEncodedCompleteSplitProfiles_support
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c) address.1).mp hselected |>.1
  let P := cwChunkPartitionedTensor K q depth
  have hexists :=
    P.exists_positiveSupportWord_of_mem_positivePower_support_recursive n hambient
  exact Classical.choose_spec hexists

/-- The exact exponent of `q` contributed by a zero-Z recursive interface term. -/
def cwZeroInterfaceQExponent {depth : ℕ} (term : ExactInterfaceTermParameters depth) : ℕ :=
  ∑ word, (term.split .X).counts word * splitWordMiddleCount word

/-- Canonical matrix dimension of one selected outer constituent, reconstructed from its unique
supported chunk word. -/
noncomputable def cwSelectedExactInterfaceConstituentDimension
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (c : Leg) : ℕ :=
  positiveWordProduct
    (fun support ↦ cwChunkConstituentDimension K q depth support c) n
    (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address)

end AlgebraicComplexity.Examples
