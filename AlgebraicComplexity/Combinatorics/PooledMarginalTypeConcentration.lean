/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.StructuralZeroMultinomial
import AlgebraicComplexity.Combinatorics.PooledMarginalTypeEntropy
import AlgebraicComplexity.Combinatorics.PushedProfileTypeCounting

/-!
# Method of types with a pooled pair of occurrence marginals

This module turns `SparsePooledMarginalProjectionModel` into a finite conditional-type tail
bound.  A state profile is feasible when it

* has no mass outside the reference support;
* has the reference coarse marginal; and
* preserves, for each feature value, the sum of its left- and right-occurrence counts.

The two labelled feature marginals are deliberately not fixed separately.  If the empirical
parent profile differs from the reference parent law in one coordinate by at least `epsilon`,
the pooled information-projection theorem gives an entropy loss of `epsilon^2 / 4` nats.  After
partitioning a fixed-coarse word family by its complete empirical state type, the usual
conditional multinomial estimate yields an explicit finite tail bound.

The result is stated for an arbitrary finite state alphabet `U × T`.  Recursive CW clients use
`U` for a paired coarse cell and `T` for a pair of complete-split child words.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace WordType

universe u₁ u₂ u₃ u₄ u₅

variable {S : Type u₁} {U : Type u₂} {A : Type u₃} {P : Type u₄}
variable [Fintype S] [Fintype U] [Fintype A] [Fintype P]
variable [DecidableEq U] [DecidableEq A] [DecidableEq P]

/-! ## Finite conditional-word tail -/

variable {T : Type u₅} [Fintype T]

/-- Targets over one fixed coarse word whose complete state profile is pooled-feasible and whose
parent statistic deviates from the reference law. -/
noncomputable def pooledMarginalDeviatingWords
    (M : SparsePooledMarginalProjectionModel (U × T) U A)
    (parent : U × T → P)
    (sourceProfile : U → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → U)
    (epsilon : ℝ) :
    Finset (Fin (profileMass sourceProfile * k) → T) := by
  classical
  exact Finset.univ.filter fun target ↦
    let joint := multiplicity (jointWord source target)
    IsPooledMarginalProfile M joint ∧
      PooledParentProfileHasDeviation M parent joint epsilon

@[simp] theorem mem_pooledMarginalDeviatingWords
    (M : SparsePooledMarginalProjectionModel (U × T) U A)
    (parent : U × T → P)
    (sourceProfile : U → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → U)
    (epsilon : ℝ)
    (target : Fin (profileMass sourceProfile * k) → T) :
    target ∈ pooledMarginalDeviatingWords
        M parent sourceProfile k source epsilon ↔
      IsPooledMarginalProfile M
          (multiplicity (jointWord source target)) ∧
        PooledParentProfileHasDeviation M parent
          (multiplicity (jointWord source target)) epsilon := by
  classical
  simp [pooledMarginalDeviatingWords]

/-- **Pooled fixed-coarse method-of-types tail.**

The model's coarse statistic must be the first projection of the state alphabet.  For one exact
proportional coarse word, all pooled-feasible targets whose parent empirical law has a coordinate
deviation `epsilon` lose `epsilon^2 / 4` nats per sample, up to the literal number of state types
and the standard structural-zero multinomial loss. -/
theorem card_pooledMarginalDeviatingWords_le
    (M : SparsePooledMarginalProjectionModel (U × T) U A)
    (hMcoarse : M.coarse = Prod.fst)
    (parent : U × T → P)
    (sourceProfile : U → ℕ) (hmass : 0 < profileMass sourceProfile)
    (k : ℕ) (hk : 0 < k)
    (source : Fin (profileMass sourceProfile * k) → U)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    ((pooledMarginalDeviatingWords
      M parent sourceProfile k source epsilon).card : ℝ) ≤
      ((((profileMass sourceProfile * k + 1) ^ Fintype.card (U × T) : ℕ) : ℝ)) *
        structuralZeroMultinomialLoss sourceProfile k *
          Real.exp (((k : ℝ) * profileMass sourceProfile) *
            (M.reference.conditionalEntropy M.coarse - epsilon ^ 2 / 4)) := by
  classical
  let bad := pooledMarginalDeviatingWords
    M parent sourceProfile k source epsilon
  let n := profileMass sourceProfile * k
  let exponent := ((k : ℝ) * profileMass sourceProfile) *
    (M.reference.conditionalEntropy M.coarse - epsilon ^ 2 / 4)
  have hpartition : bad.card =
      ∑ joint ∈ types (U × T) n,
        (bad.filter fun target ↦
          multiplicity (jointWord source target) = joint).card := by
    exact Finset.card_eq_sum_card_fiberwise fun target _ ↦
      multiplicity_mem_types (jointWord source target)
  have hfiber : ∀ joint ∈ types (U × T) n,
      (((bad.filter fun target ↦
        multiplicity (jointWord source target) = joint).card : ℕ) : ℝ) ≤
        structuralZeroMultinomialLoss sourceProfile k * Real.exp exponent := by
    intro joint hjoint
    by_cases hempty : (bad.filter fun target ↦
        multiplicity (jointWord source target) = joint).Nonempty
    · obtain ⟨target, htarget⟩ := hempty
      have htargetData := Finset.mem_filter.mp htarget
      have hbad := (mem_pooledMarginalDeviatingWords
        M parent sourceProfile k source epsilon target).1 htargetData.1
      have hjointEq : multiplicity (jointWord source target) = joint := htargetData.2
      have hmap : mappedType Prod.fst joint = multiplicity source := by
        rw [← hjointEq, ← multiplicity_comp_eq_mappedType]
        rfl
      have hjointMass : profileMass joint = n := mem_types.mp hjoint
      have hjointMassPos : 0 < profileMass joint := by
        rw [hjointMass]
        exact Nat.mul_pos hmass hk
      have hentropy :=
        profileConditionalEntropy_le_reference_sub_quarter_sq_of_parentDeviation
          M parent joint hjointMassPos hepsilon (by simpa [hjointEq] using hbad.1)
            (by simpa [hjointEq] using hbad.2)
      rw [hMcoarse, hmap, hsource,
        profileEntropyNats_proportionalCounts sourceProfile hmass k hk] at hentropy
      have hscale : 0 ≤ (k : ℝ) * (profileMass sourceProfile : ℝ) := by
        positivity
      have hscaled := mul_le_mul_of_nonneg_left hentropy hscale
      have hexponent :
          (profileMass joint : ℝ) * profileEntropyNats joint -
              (k : ℝ) * (profileMass sourceProfile : ℝ) *
                profileEntropyNats sourceProfile ≤ exponent := by
        calc
          (profileMass joint : ℝ) * profileEntropyNats joint -
                (k : ℝ) * (profileMass sourceProfile : ℝ) *
                  profileEntropyNats sourceProfile =
              (k : ℝ) * (profileMass sourceProfile : ℝ) *
                (profileEntropyNats joint - profileEntropyNats sourceProfile) := by
            rw [hjointMass]
            dsimp only [n]
            push_cast
            ring
          _ ≤ (k : ℝ) * (profileMass sourceProfile : ℝ) *
                (M.reference.conditionalEntropy Prod.fst - epsilon ^ 2 / 4) := hscaled
          _ = exponent := by
            dsimp only [exponent]
            rw [hMcoarse]
      have hconditional :=
        card_conditionalTypeClass_le_structuralZeroLoss_mul_exp_entropyDifference
          sourceProfile k source joint hmass hk hsource hjoint hmap
      have hsubset :
          bad.filter (fun other ↦
            multiplicity (jointWord source other) = joint) ⊆
            conditionalTypeClass source joint := by
        intro other hother
        exact mem_conditionalTypeClass.mpr (Finset.mem_filter.mp hother).2
      calc
        (((bad.filter fun other ↦
            multiplicity (jointWord source other) = joint).card : ℕ) : ℝ) ≤
            ((conditionalTypeClass source joint).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset
        _ ≤ structuralZeroMultinomialLoss sourceProfile k *
              Real.exp
                ((profileMass joint : ℝ) * profileEntropyNats joint -
                  (k : ℝ) * (profileMass sourceProfile : ℝ) *
                    profileEntropyNats sourceProfile) := hconditional
        _ ≤ structuralZeroMultinomialLoss sourceProfile k * Real.exp exponent := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
            (structuralZeroMultinomialLoss_pos sourceProfile k).le
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hempty,
        Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (structuralZeroMultinomialLoss_pos sourceProfile k).le
        (Real.exp_pos _).le
  calc
    ((pooledMarginalDeviatingWords
        M parent sourceProfile k source epsilon).card : ℝ) =
        ∑ joint ∈ types (U × T) n,
          (((bad.filter fun target ↦
            multiplicity (jointWord source target) = joint).card : ℕ) : ℝ) := by
      change (bad.card : ℝ) = _
      exact_mod_cast hpartition
    _ ≤ ∑ _joint ∈ types (U × T) n,
          structuralZeroMultinomialLoss sourceProfile k * Real.exp exponent := by
      exact Finset.sum_le_sum fun joint hjoint ↦ hfiber joint hjoint
    _ = ((types (U × T) n).card : ℝ) *
          (structuralZeroMultinomialLoss sourceProfile k * Real.exp exponent) := by
      simp
    _ ≤ ((((n + 1) ^ Fintype.card (U × T) : ℕ) : ℝ)) *
          (structuralZeroMultinomialLoss sourceProfile k * Real.exp exponent) := by
      exact mul_le_mul_of_nonneg_right (by
        exact_mod_cast card_types_le (U × T) n)
        (mul_nonneg (structuralZeroMultinomialLoss_pos sourceProfile k).le
          (Real.exp_pos _).le)
    _ = ((((profileMass sourceProfile * k + 1) ^ Fintype.card (U × T) : ℕ) : ℝ)) *
        structuralZeroMultinomialLoss sourceProfile k *
          Real.exp (((k : ℝ) * profileMass sourceProfile) *
            (M.reference.conditionalEntropy M.coarse - epsilon ^ 2 / 4)) := by
      simp only [n, exponent]
      ring

end WordType
end AlgebraicComplexity
