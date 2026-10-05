/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSupport
import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerHashing

/-!
# Affine-hashing encoding of the Coppersmith--Winograd blocks

The standard CW block labels have weights `0`, `1`, and `2`, and every supported address has
total weight two.  Over a field of odd characteristic these weights give the injective
constant-sum encoding consumed by the reusable partitioned-power hashing framework.

This module is shared by the easy three-constituent client and the full six-constituent client.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-- Field label of a CW coordinate block. -/
def cwBlockFieldValue {R : Type*} [OfNat R 0] [OfNat R 1] [OfNat R 2] : CWBlock → R
  | .zero => 0
  | .middle => 1
  | .last => 2

/-- The three CW block values are distinct over every field of odd characteristic. -/
theorem cwBlockFieldValue_injective {R : Type*} [Field R] [NeZero (2 : R)] :
    Function.Injective (cwBlockFieldValue (R := R)) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · simp [cwBlockFieldValue] at h
  · exact ((NeZero.ne (2 : R)) (by simpa [cwBlockFieldValue] using h.symm)).elim
  · simp [cwBlockFieldValue] at h
  · rfl
  · exfalso
    have h' : (1 : R) + 0 = 1 + 1 := by
      simpa [cwBlockFieldValue, one_add_one_eq_two] using h
    exact zero_ne_one (add_left_cancel h')
  · exact ((NeZero.ne (2 : R)) (by simpa [cwBlockFieldValue] using h)).elim
  · exfalso
    have h' : (1 : R) + 1 = 1 + 0 := by
      simpa [cwBlockFieldValue, one_add_one_eq_two] using h
    exact one_ne_zero (add_left_cancel h')
  · rfl

/-- The full six-address CW support is a legal constant-sum hashing support. -/
def cwPartitionHashEncoding {R : Type*} [Field R] [NeZero (2 : R)] :
    PartitionHashEncoding (R := R) cwBlockSupport where
  encode _ := cwBlockFieldValue
  target := 2
  support_nonempty := ⟨cw200, by decide⟩
  encode_injective _ := cwBlockFieldValue_injective
  legal s hs := by
    simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress,
        cwBlockFieldValue, one_add_one_eq_two]

end AlgebraicComplexity.Examples
