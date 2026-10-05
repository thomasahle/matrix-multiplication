/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExactCompleteSplitRecursion

set_option autoImplicit false

/-!
# Scaling exact interface terms

Repeating every entry of an exact complete-split profile changes its sample count but not its
normalized distribution.  This module lifts that elementary operation to all three legs of an
exact interface term.  It is useful whenever one fixed rational recursive construction is
realized at every positive proportional repetition.
-/

namespace AlgebraicComplexity

namespace CompleteSplitProfile

/-- A positive common repetition leaves the normalized complete-split distribution unchanged. -/
theorem scale_toDistribution
    {depth total samples : ℕ}
    (profile : CompleteSplitProfile depth total samples)
    (hsamples : 0 < samples) (factor : ℕ) (hfactor : 0 < factor) :
    (profile.scale factor).toDistribution (Nat.mul_pos hsamples hfactor) =
      profile.toDistribution hsamples := by
  apply CompleteSplitDistribution.ext
  apply ProbabilityVector.ext
  funext word
  change ((profile.scale factor).toDistribution
      (Nat.mul_pos hsamples hfactor)).weight word =
    (profile.toDistribution hsamples).weight word
  rw [CompleteSplitProfile.toDistribution_weight,
    CompleteSplitProfile.toDistribution_weight]
  change (((profile.counts word * factor : ℕ) : ℝ) /
      ((samples * factor : ℕ) : ℝ)) =
    (profile.counts word : ℝ) / (samples : ℝ)
  rw [Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (by exact_mod_cast hfactor.ne')

end CompleteSplitProfile

namespace ExactInterfaceTermParameters

/-- Repeat every exact count of an interface term by a common factor. -/
def scale {depth : ℕ} (term : ExactInterfaceTermParameters depth) (factor : ℕ) :
    ExactInterfaceTermParameters depth where
  multiplicity := term.multiplicity * factor
  index := term.index
  split c := (term.split c).scale factor

@[simp] theorem scale_multiplicity
    {depth : ℕ} (term : ExactInterfaceTermParameters depth) (factor : ℕ) :
    (term.scale factor).multiplicity = term.multiplicity * factor :=
  rfl

@[simp] theorem scale_index
    {depth : ℕ} (term : ExactInterfaceTermParameters depth) (factor : ℕ) :
    (term.scale factor).index = term.index :=
  rfl

@[simp] theorem scale_split_counts
    {depth : ℕ} (term : ExactInterfaceTermParameters depth) (factor : ℕ)
    (c : Tensor.Leg) (word : SplitWord depth) :
    ((term.scale factor).split c).counts word =
      (term.split c).counts word * factor :=
  rfl

/-- Positivity of a term and its repetition factor gives positivity of the scaled term. -/
theorem scale_multiplicity_pos
    {depth : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : 0 < term.multiplicity)
    (factor : ℕ) (hfactor : 0 < factor) :
    0 < (term.scale factor).multiplicity := by
  rw [scale_multiplicity]
  exact Nat.mul_pos hmultiplicity hfactor

/-- Scaling an exact term leaves every normalized semantic split law unchanged.  The semantic
term's stored multiplicity does change, so the statement is deliberately legwise. -/
theorem scale_toSemantic_split
    {depth : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : 0 < term.multiplicity)
    (factor : ℕ) (hfactor : 0 < factor) (c : Tensor.Leg) :
    ((term.scale factor).toSemantic
        (term.scale_multiplicity_pos hmultiplicity factor hfactor)).split c =
      (term.toSemantic hmultiplicity).split c := by
  exact (term.split c).scale_toDistribution hmultiplicity factor hfactor

end ExactInterfaceTermParameters

end AlgebraicComplexity
