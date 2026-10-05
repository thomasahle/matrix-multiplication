/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquare

/-!
# Finite admission of native Coppersmith--Winograd base components

This is the base-component rule of [duan2023faster],
`papers/sources/2210.10173/prelim.tex:174-198` (the six physical block shapes) and
`second_power.tex:51-63` (level-one components are matrix multiplications).
The finite payload contains only the CW parameter and the ordered physical X/Y/Z degrees.
The decoder admits precisely the six native supported shapes, and its soundness theorem binds
the decoded native degrees to the input list. Matrix dimensions are derived from the existing
native component, not supplied as unchecked certificate fields.

This q-parameterized rule is shared by DWZ and other CW certificates. It belongs in `Examples`
because its semantic provider is the native CW partition; it is not a DWZ-specific theorem
family. The DWZ paired-011 instantiation is a separate consumer.
This module does not provide a producing DAG, profile filter, extraction, or exponent bound.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor

universe u

/-- Finite input for a CW base rule, with physical degrees ordered X, Y, Z. -/
structure CWBaseRuleData where
  q : Nat
  shape : List Nat

/-- The three native CW block degrees, in physical X/Y/Z order. -/
def cwBaseShapeDigits (s : CWBlockAddress) : List Nat :=
  [cwBlockDegree (s .X), cwBlockDegree (s .Y), cwBlockDegree (s .Z)]

/-- Decode only the six supported base shapes; malformed and unsupported lists are rejected. -/
def decodeCWBaseShape : List Nat → Option cwBlockSupport
  | [2, 0, 0] => some ⟨cw200, by decide⟩
  | [0, 2, 0] => some ⟨cw020, by decide⟩
  | [0, 0, 2] => some ⟨cw002, by decide⟩
  | [0, 1, 1] => some ⟨cw011, by decide⟩
  | [1, 0, 1] => some ⟨cw101, by decide⟩
  | [1, 1, 0] => some ⟨cw110, by decide⟩
  | _ => none

/-- A successful decode selects the native component with exactly the supplied physical shape. -/
theorem decodeCWBaseShape_sound (shape : List Nat) (s : cwBlockSupport)
    (h : decodeCWBaseShape shape = some s) : cwBaseShapeDigits s.val = shape := by
  unfold decodeCWBaseShape at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst s; rfl

/-- Admission requires a positive CW parameter and a successful native-shape decode. -/
def cwBaseRuleCheck (data : CWBaseRuleData) : Bool :=
  decide (0 < data.q) && (decodeCWBaseShape data.shape).isSome

/-- Checked finite data supplies an exact native restriction with derived positive dimensions. -/
theorem cwBaseRuleCheck_sound (K : Type u) [CommRing K] (data : CWBaseRuleData)
    (h : cwBaseRuleCheck data = true) :
    ∃ s : cwBlockSupport,
      decodeCWBaseShape data.shape = some s ∧
      cwBaseShapeDigits s.val = data.shape ∧
      (0 < (cwConstituentDimensions data.q s.val).1 ∧
        0 < (cwConstituentDimensions data.q s.val).2.1 ∧
        0 < (cwConstituentDimensions data.q s.val).2.2) ∧
      Restricts (cwSupportedConstituent K data.q s)
        (matrixMultiplication (K := K)
          (cwConstituentDimensions data.q s.val).1
          (cwConstituentDimensions data.q s.val).2.1
          (cwConstituentDimensions data.q s.val).2.2) := by
  have hq : 0 < data.q := by
    have hh : 0 < data.q ∧ (decodeCWBaseShape data.shape).isSome = true := by
      simpa [cwBaseRuleCheck] using h
    exact hh.1
  cases hd : decodeCWBaseShape data.shape with
  | none => simp [cwBaseRuleCheck, hd] at h
  | some s =>
      exact ⟨s, rfl, decodeCWBaseShape_sound data.shape s hd,
        cwConstituentDimensions_pos data.q hq s,
        cwSupportedConstituent_restricts K data.q s⟩

end AlgebraicComplexity.Examples
