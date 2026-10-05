/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ProportionalMultinomialCore
import AlgebraicComplexity.Combinatorics.ConditionalWordType

/-!
# Conditional proportional multinomial estimate

This compatibility module adds the conditional-word client theorem to the lightweight
finite-alphabet estimates in `ProportionalMultinomialCore`.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u

/-- Exact conditional method-of-types lower estimate for proportional positive profiles.

The row-sum condition is stated through `mappedType`; by `mappedType_fst_eq_iff` it is exactly the
family of integer row-sum equations used by certificate formats.  No quotient of natural numbers
appears: the proof combines the division-free conditional type-class factorization with the two
polynomial multinomial estimates above. -/
theorem proportionalConditionalEntropyBase_pow_le
    {U : Type u} {Z : Type*} [Fintype U] [Fintype Z] [Nonempty U] [Nonempty Z]
    (sourceProfile : U → ℕ) (jointProfile : U × Z → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → U)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hjoint : proportionalCounts jointProfile k ∈
      types (U × Z) (profileMass sourceProfile * k))
    (hmap : mappedType Prod.fst (proportionalCounts jointProfile k) =
      multiplicity source)
    (hsourcePos : ∀ u, 0 < sourceProfile u)
    (hjointPos : ∀ z, 0 < jointProfile z)
    (hk : 0 < k) :
    proportionalEntropyBase jointProfile ^ k ≤
      (proportionalMultinomialLoss jointProfile k *
          proportionalMultinomialUpperLoss sourceProfile k) *
        ((conditionalTypeClass source (proportionalCounts jointProfile k)).card : ℝ) *
          proportionalEntropyBase sourceProfile ^ k := by
  classical
  have hjointLower :=
    proportionalEntropyBase_pow_le_loss_mul_multinomial jointProfile k hjointPos hk
  have hsourceUpper :=
    multinomial_le_upperLoss_mul_proportionalEntropyBase_pow sourceProfile k hsourcePos hk
  have hfactorNat :=
    multinomial_source_mul_card_conditionalTypeClass source
      (proportionalCounts jointProfile k) hjoint hmap
  rw [hsource] at hfactorNat
  have hfactor :
      (Nat.multinomial Finset.univ (proportionalCounts sourceProfile k) : ℝ) *
          ((conditionalTypeClass source (proportionalCounts jointProfile k)).card : ℝ) =
        (Nat.multinomial Finset.univ (proportionalCounts jointProfile k) : ℝ) := by
    exact_mod_cast hfactorNat
  calc
    proportionalEntropyBase jointProfile ^ k ≤
        proportionalMultinomialLoss jointProfile k *
          (Nat.multinomial Finset.univ (proportionalCounts jointProfile k) : ℝ) :=
      hjointLower
    _ = proportionalMultinomialLoss jointProfile k *
        ((Nat.multinomial Finset.univ (proportionalCounts sourceProfile k) : ℝ) *
          ((conditionalTypeClass source (proportionalCounts jointProfile k)).card : ℝ)) := by
      rw [hfactor]
    _ ≤ proportionalMultinomialLoss jointProfile k *
        ((proportionalMultinomialUpperLoss sourceProfile k *
            proportionalEntropyBase sourceProfile ^ k) *
          ((conditionalTypeClass source (proportionalCounts jointProfile k)).card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsourceUpper (by positivity)) (by
          unfold proportionalMultinomialLoss
          positivity)
    _ = (proportionalMultinomialLoss jointProfile k *
          proportionalMultinomialUpperLoss sourceProfile k) *
        ((conditionalTypeClass source (proportionalCounts jointProfile k)).card : ℝ) *
          proportionalEntropyBase sourceProfile ^ k := by
      ring

end AlgebraicComplexity.WordType
