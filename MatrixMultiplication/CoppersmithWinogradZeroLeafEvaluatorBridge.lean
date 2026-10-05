/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.CoppersmithWinogradZeroLeafVolumeBudget
import MatrixMultiplication.DyadicZeroLeafVolume

set_option autoImplicit false

/-!
# Exact evaluator bridge for one finite CW zero-coordinate leaf

The finite tensor construction stores a complete-split profile, while the certificate evaluator
stores a primitive profile as dyadic numerators.  This file isolates the only bridge needed between
them: if the stored profile is a positive `k`-fold repetition of a primitive profile of mass
`2^bits`, then the leaf's entropy-plus-dimension exponent is exactly the primitive dyadic value
times the repeated sample count.

The statement is about one literal `ExactInterfaceTermParameters` leaf and concludes with its
literal fused family dimension.  A recursive construction may later supply the two elementary
profile and sample-count equalities, but no recursive reference object is imported here.  The
second theorem transports the already-proved finite restriction bound across the equality, keeping
the method-of-types loss explicit.
-/

namespace MatrixMultiplication.CoppersmithWinogradZeroLeafEvaluatorBridge

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.CoppersmithWinogradZeroLeafVolumeBudget
open MatrixMultiplication.DyadicZeroLeafVolume

universe u

variable {depth n bits k : ℕ}
variable {zero : Leg}

private theorem positivePowerProfile_counts_aux
    (index : LevelConstituentIndex depth) (multiplicity n : ℕ)
    (split : ∀ c, CompleteSplitProfile depth (index.count c) multiplicity)
    (hmultiplicity : multiplicity = n + 1) (c : Leg) :
    ((ExactInterfaceTermParameters.mk multiplicity index split).positivePowerProfile
      hmultiplicity c).counts = (split c).counts := by
  subst hmultiplicity
  rfl

private theorem positivePowerProfile_counts
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (c : Leg) :
    (term.positivePowerProfile hmultiplicity c).counts = (term.split c).counts :=
  positivePowerProfile_counts_aux term.index term.multiplicity n term.split hmultiplicity c

/-- A finite CW zero leaf whose profile is a positive proportional repetition has exactly the
dyadic entropy-plus-middle-digit value used by the evaluator.

The hypotheses are finite equalities, not asymptotic assumptions: `hprofile` identifies the
stored complete-split counts with a `k`-fold repetition, while `hsamples` identifies the leaf's
sample count with the repeated dyadic mass.

Proof sketch: unfold the nominal volume, replace the stored profile and sample count using the two
hypotheses, and apply the generic dyadic scaling identity. -/
theorem nominalVolumeBits_eq_mass_mul_value_of_proportionalProfile
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (profile : SplitWord depth → ℕ)
    (hnormalized : WordType.profileMass profile = 2 ^ bits)
    (hprofile :
      (term.split (firstLiveLeg zero)).counts =
        WordType.proportionalCounts profile k)
    (hsamples : n + 1 = 2 ^ bits * k)
    (hk : 0 < k) :
    nominalVolumeBits 5 zero term hmultiplicity =
      ((((2 ^ bits) * k : ℕ) : ℝ) *
        value 5 bits profile splitWordMiddleCount) := by
  have hscaled := scaledProfileBits_eq_mass_mul_value
    5 bits profile splitWordMiddleCount hnormalized k hk
  calc
    nominalVolumeBits 5 zero term hmultiplicity =
        (((n + 1 : ℕ) : ℝ) *
            WordType.profileEntropyBits
              (WordType.proportionalCounts profile k)) +
          Real.logb 2 (5 : ℝ) *
            (((∑ word,
              WordType.proportionalCounts profile k word *
                splitWordMiddleCount word : ℕ)) : ℝ) := by
      unfold nominalVolumeBits cwZeroInterfaceQExponentOn
      rw [positivePowerProfile_counts, hprofile]
      norm_num
    _ = ((((2 ^ bits) * k : ℕ) : ℝ) *
        value 5 bits profile splitWordMiddleCount) := by
      rw [hsamples]
      exact hscaled

/-- The repeated evaluator value is realized by the literal fused zero-leaf restriction up to the
explicit method-of-types loss.

Proof sketch: rewrite the evaluator exponent by the preceding exact identity and apply the
existing finite zero-leaf volume theorem without changing its right-hand side. -/
theorem two_rpow_mass_mul_value_le_loss_mul_familyDimension_of_proportionalProfile
    (K : Type u) [CommRing K]
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (profile : SplitWord depth → ℕ)
    (hnormalized : WordType.profileMass profile = 2 ^ bits)
    (hprofile :
      (term.split (firstLiveLeg zero)).counts =
        WordType.proportionalCounts profile k)
    (hsamples : n + 1 = 2 ^ bits * k)
    (hk : 0 < k)
    (hzero : term.index.count zero = 0)
    (hcomplement : ∀ word,
      (term.positivePowerProfile hmultiplicity (secondLiveLeg zero)).counts word =
        (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).counts
            (complementSplitWord word)) :
    (2 : ℝ) ^
        ((((2 ^ bits) * k : ℕ) : ℝ) *
          value 5 bits profile splitWordMiddleCount) ≤
      WordType.typeClassEntropyLoss (SplitWord depth) (n + 1) *
        (cwSelectedZeroFamilyDimension K 5 zero term hmultiplicity : ℝ) := by
  rw [← nominalVolumeBits_eq_mass_mul_value_of_proportionalProfile term hmultiplicity
    profile hnormalized hprofile hsamples hk]
  exact two_rpow_nominalVolumeBits_le_typeClassEntropyLoss_mul_familyDimension
    K 5 (by norm_num) zero term hmultiplicity hzero hcomplement

end MatrixMultiplication.CoppersmithWinogradZeroLeafEvaluatorBridge
