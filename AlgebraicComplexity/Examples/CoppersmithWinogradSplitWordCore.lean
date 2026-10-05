/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSupportCore
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorWordCore
import AlgebraicComplexity.Tensor.PositiveWord

/-!
# Native Coppersmith--Winograd complete-split words

This dependency-light leaf identifies the three native CW block labels with the ternary digits
of a complete-split word and packages a chunk of `2^depth` labels as a `SplitWord depth`.
Tensor realizations, partitioned block spaces, and exact interface selections deliberately live
downstream in `CoppersmithWinogradInterfaceCore`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-- Ternary digit represented by one CW partition block. -/
def cwBlockDigit : CWBlock → SplitDigit
  | .zero => 0
  | .middle => 1
  | .last => 2

@[simp] theorem cwBlockDigit_zero : cwBlockDigit .zero = 0 := rfl
@[simp] theorem cwBlockDigit_middle : cwBlockDigit .middle = 1 := rfl
@[simp] theorem cwBlockDigit_last : cwBlockDigit .last = 2 := rfl

theorem cwBlockDigit_injective : Function.Injective cwBlockDigit := by
  intro left right h
  cases left <;> cases right <;> simp_all [cwBlockDigit]

/-- Encode a CW block as the one-letter split word at recursion depth zero. -/
def cwBlockSplitWord (block : CWBlock) : SplitWord 0 :=
  fun _ ↦ cwBlockDigit block

@[simp] theorem cwBlockSplitWord_apply (block : CWBlock) (position : Fin 1) :
    cwBlockSplitWord block position = cwBlockDigit block :=
  rfl

theorem cwBlockSplitWord_injective : Function.Injective cwBlockSplitWord := by
  intro left right h
  apply cwBlockDigit_injective
  exact congrFun h 0

@[simp] theorem splitWordWeight_cwBlockSplitWord (block : CWBlock) :
    splitWordWeight (cwBlockSplitWord block) = (cwBlockDigit block : ℕ) := by
  simp [splitWordWeight, cwBlockSplitWord]

/-- Natural-number form of the tight CW address equation. -/
theorem cwBlockSupport_digit_sum (address : CWBlockAddress)
    (haddress : address ∈ cwBlockSupport) :
    ∑ c, (cwBlockDigit (address c) : ℕ) = 2 := by
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress,
      cwBlockDigit, sum_leg]

/-- The positive-word parameter `2^depth - 1` indeed represents `2^depth` block labels. -/
theorem two_pow_sub_one_add_one (depth : ℕ) :
    2 ^ depth - 1 + 1 = 2 ^ depth :=
  Nat.sub_add_cancel Nat.one_le_two_pow

/-- Reindex positions in a positive word of `2^depth` CW blocks by `Fin (2^depth)`. -/
def cwChunkPositionEquiv (depth : ℕ) :
    Fin (2 ^ depth - 1 + 1) ≃ Fin (2 ^ depth) :=
  finCongr (two_pow_sub_one_add_one depth)

/-- Encode a positive word of `2^depth` native CW blocks as a depth-`depth` complete-split word. -/
def cwChunkSplitWord (depth : ℕ)
    (word : PositiveWord CWBlock (2 ^ depth - 1)) : SplitWord depth :=
  fun position ↦ cwBlockDigit
    (positiveWordEquiv CWBlock (2 ^ depth - 1) word
      ((cwChunkPositionEquiv depth).symm position))

theorem cwChunkSplitWord_injective (depth : ℕ) :
    Function.Injective (cwChunkSplitWord depth) := by
  intro left right h
  apply (positiveWordEquiv CWBlock (2 ^ depth - 1)).injective
  funext position
  apply cwBlockDigit_injective
  have hp := congrFun h (cwChunkPositionEquiv depth position)
  simpa [cwChunkSplitWord] using hp

@[simp] theorem cwChunkSplitWord_zero (block : CWBlock) :
    cwChunkSplitWord 0 block = cwBlockSplitWord block := by
  funext position
  change Fin 1 at position
  have hposition : position = 0 := Fin.eq_zero position
  subst position
  rfl

end AlgebraicComplexity.Examples
