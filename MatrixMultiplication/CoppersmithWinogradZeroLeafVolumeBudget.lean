/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroNativeStage
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationTypeClassGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

/-!
# Finite volume of a fused zero-coordinate CW leaf

A selected zero-coordinate Coppersmith--Winograd interface has two independent contributions to
its matrix-multiplication volume.

* Its complete-split type class contributes the entropy factor
  `2 ^ (multiplicity * profileEntropyBits)` up to the explicit polynomial
  `WordType.typeClassEntropyLoss`.
* Every member of that type class contributes the same exact power `q ^ e`, where `e` is
  `cwZeroInterfaceQExponentOn` at the first live leg.

The existing shared-one-slice fusion keeps both contributions in one native-frame matrix
dimension.  This file combines the already-proved counting and fusion statements.  Its principal
theorem deliberately retains the polynomial loss:

```text
2 ^ (entropy bits + q-power bits)
  <= typeClassEntropyLoss * (native x-size * native y-size * native z-size).
```

This is a finite semantic theorem.  It does not claim the lossless
`CertificateDerivedLeafVolumeBudget.MeetsBudget`; the eventual division forest must multiply these
finite losses and discharge them through its existing subexponential `volumeLoss` field.
-/

namespace MatrixMultiplication.CoppersmithWinogradZeroLeafVolumeBudget

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor

universe u

/-- The nominal three-coordinate volume, in bits, of a fused zero-coordinate CW interface leaf.

The first term is the logarithm of the complete-split type-class cardinality.  The second is the
logarithm of the exact `q`-power carried by every constituent in the shared one-slice fibre. -/
noncomputable def nominalVolumeBits
    (q : ℕ) (zero : Leg) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) : ℝ :=
  (((n + 1 : ℕ) : ℝ) * WordType.profileEntropyBits
      (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).counts) +
    Real.logb 2 (q : ℝ) *
      (cwZeroInterfaceQExponentOn (firstLiveLeg zero) term : ℝ)

/-- The product of the three dimensions displayed by the native zero-coordinate stage is exactly
the fused family dimension.

Proof sketch: the native stage has two unit dimensions and places the sole nontrivial dimension
on `secondLiveLeg zero`; the three cases differ only by that placement. -/
theorem nativeDimensionProduct_eq_familyDimension
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg)
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    (match zero with
      | .X => 1
      | .Y => cwSelectedZeroFamilyDimension K q .Y term hmultiplicity
      | .Z => 1) *
      (match zero with
        | .X => 1
        | .Y => 1
        | .Z => cwSelectedZeroFamilyDimension K q .Z term hmultiplicity) *
      (match zero with
        | .X => cwSelectedZeroFamilyDimension K q .X term hmultiplicity
        | .Y => 1
        | .Z => 1) =
      cwSelectedZeroFamilyDimension K q zero term hmultiplicity := by
  cases zero <;> simp

/-- A fused zero-coordinate CW interface realizes its entropy-plus-`q` nominal volume up to the
explicit type-class loss.

Proof sketch: multiply the existing type-class lower bound by `q ^ e`.  The identity
`2 ^ (logb 2 q * e) = q ^ e` converts this exact factor into bits, and the definition of
`cwSelectedZeroFamilyDimension` identifies the resulting product with the fused family size. -/
theorem two_rpow_nominalVolumeBits_le_typeClassEntropyLoss_mul_familyDimension
    (K : Type u) [CommRing K] (q : ℕ) (hq : 0 < q) (zero : Leg)
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hzero : term.index.count zero = 0)
    (hcomplement : ∀ word,
      (term.positivePowerProfile hmultiplicity (secondLiveLeg zero)).counts word =
        (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).counts
          (complementSplitWord word)) :
    (2 : ℝ) ^ nominalVolumeBits q zero term hmultiplicity ≤
      WordType.typeClassEntropyLoss (SplitWord depth) (n + 1) *
        (cwSelectedZeroFamilyDimension K q zero term hmultiplicity : ℝ) := by
  let exponent := cwZeroInterfaceQExponentOn (firstLiveLeg zero) term
  have htype :=
    two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_cwOrientedZeroInterface
      K q term hmultiplicity zero hzero hcomplement
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hqBits :
      (2 : ℝ) ^ (Real.logb 2 (q : ℝ) * (exponent : ℝ)) =
        ((q ^ exponent : ℕ) : ℝ) := by
    calc
      (2 : ℝ) ^ (Real.logb 2 (q : ℝ) * (exponent : ℝ)) =
          ((2 : ℝ) ^ Real.logb 2 (q : ℝ)) ^ (exponent : ℝ) :=
        Real.rpow_mul (by norm_num) _ _
      _ = (q : ℝ) ^ (exponent : ℝ) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) hqReal]
      _ = (q : ℝ) ^ exponent := Real.rpow_natCast _ _
      _ = ((q ^ exponent : ℕ) : ℝ) := by norm_cast
  have hmul := mul_le_mul_of_nonneg_right htype
    (show (0 : ℝ) ≤ ((q ^ exponent : ℕ) : ℝ) from Nat.cast_nonneg _)
  calc
    (2 : ℝ) ^ nominalVolumeBits q zero term hmultiplicity =
        (2 : ℝ) ^
            (((n + 1 : ℕ) : ℝ) * WordType.profileEntropyBits
              (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).counts) *
          ((q ^ exponent : ℕ) : ℝ) := by
      rw [nominalVolumeBits, Real.rpow_add (by norm_num), hqBits]
    _ ≤
        (WordType.typeClassEntropyLoss (SplitWord depth) (n + 1) *
            (((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card : ℕ) : ℝ)) *
          ((q ^ exponent : ℕ) : ℝ) := hmul
    _ = WordType.typeClassEntropyLoss (SplitWord depth) (n + 1) *
        (cwSelectedZeroFamilyDimension K q zero term hmultiplicity : ℝ) := by
      simp only [cwSelectedZeroFamilyDimension, exponent, Nat.cast_mul, Nat.cast_pow]
      ring

/-- The finite bound in the literal dimension order of
`cwSelectedExactInterfaceTerm_zero_nativeStage`.

This is the form consumed by a future loss-aware division-leaf fold: the right-hand natural
product is definitionally the native stage's `xSize * ySize * zSize`. -/
theorem two_rpow_nominalVolumeBits_le_typeClassEntropyLoss_mul_nativeDimensionProduct
    (K : Type u) [CommRing K] (q : ℕ) (hq : 0 < q) (zero : Leg)
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hzero : term.index.count zero = 0)
    (hcomplement : ∀ word,
      (term.positivePowerProfile hmultiplicity (secondLiveLeg zero)).counts word =
        (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).counts
          (complementSplitWord word)) :
    (2 : ℝ) ^ nominalVolumeBits q zero term hmultiplicity ≤
      WordType.typeClassEntropyLoss (SplitWord depth) (n + 1) *
        (((match zero with
            | .X => 1
            | .Y => cwSelectedZeroFamilyDimension K q .Y term hmultiplicity
            | .Z => 1) *
          (match zero with
            | .X => 1
            | .Y => 1
            | .Z => cwSelectedZeroFamilyDimension K q .Z term hmultiplicity) *
          (match zero with
            | .X => cwSelectedZeroFamilyDimension K q .X term hmultiplicity
            | .Y => 1
            | .Z => 1) : ℕ) : ℝ) := by
  cases zero with
  | X =>
      simpa using
        (two_rpow_nominalVolumeBits_le_typeClassEntropyLoss_mul_familyDimension
          K q hq .X term hmultiplicity hzero hcomplement)
  | Y =>
      simpa using
        (two_rpow_nominalVolumeBits_le_typeClassEntropyLoss_mul_familyDimension
          K q hq .Y term hmultiplicity hzero hcomplement)
  | Z =>
      simpa using
        (two_rpow_nominalVolumeBits_le_typeClassEntropyLoss_mul_familyDimension
          K q hq .Z term hmultiplicity hzero hcomplement)

end MatrixMultiplication.CoppersmithWinogradZeroLeafVolumeBudget
