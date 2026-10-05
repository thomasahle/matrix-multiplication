/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradChunkDimension
import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordCore
import AlgebraicComplexity.MatrixMultiplication.CompleteSplitStatistics
import AlgebraicComplexity.Tensor.IteratedProduct
import AlgebraicComplexity.Tensor.PartitionedPowerSupportDecodeCore
import AlgebraicComplexity.MatrixMultiplication.PositiveWordProduct

/-!
# Exact dimensions of zero-coordinate CW words

On the zero-`Z` fiber of the six-block CW support, every base constituent is a one-slice tensor:
its `X` and `Z` dimensions are one, and its `Y` dimension is `q` exactly when the `X` block is
middle.  This module lifts those finite facts along a supported word and identifies the exponent
with the middle-digit statistic of the encoded split word.

The later exact-interface recurrence and tensor-restriction consequences remain in
`CoppersmithWinogradZeroDimension`.  Explicit coherent maps use this smaller word-level module.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

/-- Number of middle X blocks in a supported word of base CW addresses. -/
def cwSupportedWordXMiddleCount (r : ℕ)
    (word : PositiveWord cwBlockSupport r) : ℕ :=
  ∑ position,
    if cwBlockDigit ((positiveWordEquiv cwBlockSupport r word position).1 .X) =
        (1 : SplitDigit) then 1 else 0

/-- A supported base CW address with zero `Z` block has unit first matrix dimension. -/
theorem cwBaseConstituentDimension_X_eq_one_of_z_eq_zero
    (q : ℕ) (support : cwBlockSupport) (hz : support.1 .Z = .zero) :
    cwBaseConstituentDimension q support .X = 1 := by
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [cwBaseConstituentDimension, cwBlockMatrixDimensions,
      cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

/-- A supported base CW address with zero `Z` block has unit third matrix dimension. -/
theorem cwBaseConstituentDimension_Z_eq_one_of_z_eq_zero
    (q : ℕ) (support : cwBlockSupport) (hz : support.1 .Z = .zero) :
    cwBaseConstituentDimension q support .Z = 1 := by
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [cwBaseConstituentDimension, cwBlockMatrixDimensions,
      cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

/-- On the zero-`Z` fiber, the second base matrix dimension is `q` exactly at an X-middle
address and is `1` otherwise. -/
theorem cwBaseConstituentDimension_Y_eq_pow_middleIndicator_of_z_eq_zero
    (q : ℕ) (support : cwBlockSupport) (hz : support.1 .Z = .zero) :
    cwBaseConstituentDimension q support .Y =
      q ^ (if cwBlockDigit (support.1 .X) = (1 : SplitDigit) then 1 else 0) := by
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [cwBaseConstituentDimension, cwBlockMatrixDimensions,
      cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

/-- A constant zero transposed Z word means that every supported source letter lies in the
zero-Z fiber. -/
theorem positiveSupportWord_letter_z_eq_zero_of_address_z_eq_const
    {r : ℕ} (word : PositiveWord cwBlockSupport r)
    (hz : positiveSupportWordBlockAddress cwBlockSupport r word .Z =
      positiveWordConst .zero r) (position : Fin (r + 1)) :
    (positiveWordEquiv cwBlockSupport r word position).1 .Z = .zero := by
  have hzWords := congrArg (positiveWordEquiv CWBlock r) hz
  have hzPosition := congrFun hzWords position
  calc
    (positiveWordEquiv cwBlockSupport r word position).1 .Z =
        positiveWordEquiv CWBlock r
          (positiveSupportWordBlockAddress cwBlockSupport r word .Z) position :=
      (congrFun
        (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
          cwBlockSupport r word .Z) position).symm
    _ = positiveWordEquiv CWBlock r (positiveWordConst .zero r) position := hzPosition
    _ = .zero := by simp only [positiveWordEquiv_const]

/-- The first product dimension of a supported zero-Z base word is one. -/
theorem positiveWordProduct_cwBaseDimension_X_eq_one_of_z_eq_const
    (q r : ℕ) (word : PositiveWord cwBlockSupport r)
    (hz : positiveSupportWordBlockAddress cwBlockSupport r word .Z =
      positiveWordConst .zero r) :
    positiveWordProduct (fun support ↦ cwBaseConstituentDimension q support .X) r word = 1 := by
  rw [positiveWordProduct_eq_fin_prod]
  apply Finset.prod_eq_one
  intro position _
  exact cwBaseConstituentDimension_X_eq_one_of_z_eq_zero q _
    (positiveSupportWord_letter_z_eq_zero_of_address_z_eq_const word hz position)

/-- The third product dimension of a supported zero-Z base word is one. -/
theorem positiveWordProduct_cwBaseDimension_Z_eq_one_of_z_eq_const
    (q r : ℕ) (word : PositiveWord cwBlockSupport r)
    (hz : positiveSupportWordBlockAddress cwBlockSupport r word .Z =
      positiveWordConst .zero r) :
    positiveWordProduct (fun support ↦ cwBaseConstituentDimension q support .Z) r word = 1 := by
  rw [positiveWordProduct_eq_fin_prod]
  apply Finset.prod_eq_one
  intro position _
  exact cwBaseConstituentDimension_Z_eq_one_of_z_eq_zero q _
    (positiveSupportWord_letter_z_eq_zero_of_address_z_eq_const word hz position)

/-- The second product dimension of a supported zero-Z base word is the power of `q` counted by
its X-middle positions. -/
theorem positiveWordProduct_cwBaseDimension_Y_eq_pow_middleCount_of_z_eq_const
    (q r : ℕ) (word : PositiveWord cwBlockSupport r)
    (hz : positiveSupportWordBlockAddress cwBlockSupport r word .Z =
      positiveWordConst .zero r) :
    positiveWordProduct (fun support ↦ cwBaseConstituentDimension q support .Y) r word =
      q ^ cwSupportedWordXMiddleCount r word := by
  rw [positiveWordProduct_eq_fin_prod]
  calc
    (∏ position,
        cwBaseConstituentDimension q
          (positiveWordEquiv cwBlockSupport r word position) .Y) =
        ∏ position,
          q ^ (if cwBlockDigit
              ((positiveWordEquiv cwBlockSupport r word position).1 .X) =
                (1 : SplitDigit) then 1 else 0) := by
      apply Finset.prod_congr rfl
      intro position _
      exact cwBaseConstituentDimension_Y_eq_pow_middleIndicator_of_z_eq_zero q _
        (positiveSupportWord_letter_z_eq_zero_of_address_z_eq_const word hz position)
    _ = q ^ cwSupportedWordXMiddleCount r word := by
      rw [Finset.prod_pow_eq_pow_sum]
      rfl

/-- Encoding the X block word as a complete-split word preserves its number of middle digits. -/
theorem splitWordMiddleCount_cwChunkSplitWord
    (depth : ℕ) (word : PositiveWord CWBlock (2 ^ depth - 1)) :
    splitWordMiddleCount (cwChunkSplitWord depth word) =
      ∑ position : Fin (2 ^ depth - 1 + 1),
        if cwBlockDigit
            (positiveWordEquiv CWBlock (2 ^ depth - 1) word position) =
              (1 : SplitDigit) then 1 else 0 := by
  let e := cwChunkPositionEquiv depth
  let f : Fin (2 ^ depth - 1 + 1) → ℕ := fun position ↦
    if cwBlockDigit
        (positiveWordEquiv CWBlock (2 ^ depth - 1) word position) =
          (1 : SplitDigit) then 1 else 0
  have hsum := e.sum_comp (fun position : Fin (2 ^ depth) ↦ f (e.symm position))
  change (∑ position : Fin (2 ^ depth), f (e.symm position)) = ∑ position, f position
  calc
    _ = ∑ position, f (e.symm (e position)) := hsum.symm
    _ = _ := by simp only [Equiv.symm_apply_apply]

/-- For a supported base-address word, the encoded X chunk has exactly the recursively counted
number of middle X blocks. -/
theorem splitWordMiddleCount_cwChunkSplitWord_positiveSupportWordBlockAddress
    (depth : ℕ)
    (word : PositiveWord cwBlockSupport (2 ^ depth - 1)) :
    splitWordMiddleCount
        (cwChunkSplitWord depth
          (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) word .X)) =
      cwSupportedWordXMiddleCount (2 ^ depth - 1) word := by
  rw [splitWordMiddleCount_cwChunkSplitWord]
  unfold cwSupportedWordXMiddleCount
  apply Finset.sum_congr rfl
  intro position _
  rw [congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      cwBlockSupport (2 ^ depth - 1) word .X) position]

end AlgebraicComplexity.Examples
