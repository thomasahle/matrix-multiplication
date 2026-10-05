/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.FiniteCoreDefs

set_option autoImplicit false

/-!
# Zero-safe finite joint disintegration core

Every finite joint probability vector is its first marginal joined with conditional
second-coordinate rows. A zero-mass row is assigned an arbitrary point mass; its parent
coefficient is zero, so exact reconstruction is independent of that choice.

This core intentionally contains no entropy theorem or integral-profile specialization.

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open scoped BigOperators

namespace AlgebraicComplexity

namespace ProbabilityVector

universe u v

/-- The mass of one first-coordinate row is its first-marginal weight. -/
theorem sum_snd_weight_eq_pushforward_fst_weight
    {Z : Type u} {U : Type v} [Fintype Z] [DecidableEq Z] [Fintype U]
    (joint : ProbabilityVector (Z × U)) (z : Z) :
    (∑ u, joint.weight (z, u)) = (joint.pushforward Prod.fst).weight z := by
  rw [pushforward_weight]
  symm
  rw [Fintype.sum_prod_type, Finset.sum_eq_single z]
  · simp
  · intro other _ hother
    simp [hother]
  · simp

/-- Conditional law of the second coordinate in one first-coordinate row.

At zero parent mass, use an arbitrary point mass. This choice disappears after multiplication by
the parent weight. -/
noncomputable def conditionalSnd
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (joint : ProbabilityVector (Z × U)) (z : Z) : ProbabilityVector U := by
  classical
  by_cases hz : (joint.pushforward Prod.fst).weight z = 0
  · exact pointMass (Classical.choice (inferInstance : Nonempty U))
  · exact
      { weight := fun u ↦
          joint.weight (z, u) / (joint.pushforward Prod.fst).weight z
        nonneg := fun u ↦ div_nonneg (joint.nonneg (z, u))
          ((joint.pushforward Prod.fst).nonneg z)
        total := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul, sum_snd_weight_eq_pushforward_fst_weight,
            mul_inv_cancel₀ hz] }

/-- Formula for a positive-mass conditional row. -/
@[simp] theorem conditionalSnd_weight_of_ne
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (joint : ProbabilityVector (Z × U)) (z : Z)
    (hz : (joint.pushforward Prod.fst).weight z ≠ 0) (u : U) :
    (joint.conditionalSnd z).weight u =
      joint.weight (z, u) / (joint.pushforward Prod.fst).weight z := by
  classical
  unfold conditionalSnd
  split
  · rename_i hzero
    exact (hz hzero).elim
  · rfl

/-- Every coordinate in a zero-mass parent row has zero joint mass. -/
theorem weight_eq_zero_of_pushforward_fst_weight_eq_zero
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U]
    (joint : ProbabilityVector (Z × U)) (z : Z)
    (hz : (joint.pushforward Prod.fst).weight z = 0) (u : U) :
    joint.weight (z, u) = 0 := by
  have hsum : ∑ other, joint.weight (z, other) = 0 := by
    rw [sum_snd_weight_eq_pushforward_fst_weight, hz]
  have hall : (fun other ↦ joint.weight (z, other)) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg fun other ↦ joint.nonneg (z, other)).mp hsum
  exact congrFun hall u

/-- Multiplying a conditional coordinate by its parent mass recovers the original joint
coordinate, including at zero-mass rows. -/
theorem pushforward_fst_weight_mul_conditionalSnd_weight
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (joint : ProbabilityVector (Z × U)) (z : Z) (u : U) :
    (joint.pushforward Prod.fst).weight z * (joint.conditionalSnd z).weight u =
      joint.weight (z, u) := by
  by_cases hz : (joint.pushforward Prod.fst).weight z = 0
  · rw [hz, zero_mul,
      weight_eq_zero_of_pushforward_fst_weight_eq_zero joint z hz u]
  · rw [conditionalSnd_weight_of_ne joint z hz u]
    exact mul_div_cancel₀ _ hz

/-- Exact zero-safe reconstruction of a finite joint law from its first marginal and conditional
second-coordinate rows. -/
theorem pushforward_fst_joint_conditionalSnd
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (joint : ProbabilityVector (Z × U)) :
    (joint.pushforward Prod.fst).joint joint.conditionalSnd = joint := by
  apply ProbabilityVector.ext
  funext entry
  obtain ⟨z, u⟩ := entry
  exact pushforward_fst_weight_mul_conditionalSnd_weight joint z u

end ProbabilityVector

end AlgebraicComplexity
