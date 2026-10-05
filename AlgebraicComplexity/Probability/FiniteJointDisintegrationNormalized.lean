/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.FiniteJointDisintegrationCore
import AlgebraicComplexity.Probability.IntegralProfileProbabilityCore

set_option autoImplicit false

/-!
# Normalized integral-profile disintegration

This module specializes the zero-safe finite disintegration core to normalized nonzero integral
joint profiles. It deliberately imports no entropy chain rule.

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

namespace AlgebraicComplexity

namespace WordType

universe u v

/-- First marginal of a normalized nonzero integral joint profile. -/
noncomputable def normalizedJointProfileParent
    {Z : Type u} {U : Type v} [Fintype Z] [DecidableEq Z] [Fintype U]
    (profile : Z × U → ℕ) (hmass : 0 < profileMass profile) : ProbabilityVector Z :=
  (normalizedProfileProbability profile hmass).pushforward Prod.fst

/-- Zero-safe conditional rows of a normalized nonzero integral joint profile. -/
noncomputable def normalizedJointProfileRows
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (profile : Z × U → ℕ) (hmass : 0 < profileMass profile) :
    Z → ProbabilityVector U :=
  (normalizedProfileProbability profile hmass).conditionalSnd

/-- A normalized integral joint profile reconstructs exactly from its normalized first marginal
and zero-safe conditional rows. -/
theorem normalizedJointProfileParent_joint_rows
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (profile : Z × U → ℕ) (hmass : 0 < profileMass profile) :
    (normalizedJointProfileParent profile hmass).joint
        (normalizedJointProfileRows profile hmass) =
      normalizedProfileProbability profile hmass := by
  exact ProbabilityVector.pushforward_fst_joint_conditionalSnd _

end WordType

end AlgebraicComplexity
