/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.PooledMarginalTypeConcentration

/-!
# Pooled-marginal concentration at an arbitrary source-word length

The core tail theorem indexes a source word by the expression
`profileMass sourceProfile * k`.  Concrete finite constructions normally start with an arbitrary
`Fin n` word and prove its multiplicity is the proportional profile.  That equality already
forces the required length identity.  This module packages the dependent transport once, so
clients can state their finite encodings without carrying casts through every definition.
-/

namespace AlgebraicComplexity
namespace WordType

universe u₁ u₂ u₃ u₄

variable {U : Type u₁} {T : Type u₂} {A : Type u₃} {P : Type u₄}
variable [Fintype U] [Fintype T] [Fintype A] [Fintype P]
variable [DecidableEq U] [DecidableEq A] [DecidableEq P]

/-- Pooled-feasible target words whose empirical parent statistic deviates from the reference,
stated directly over the source word's native length. -/
noncomputable def pooledMarginalDeviatingWordsForSource
    (M : SparsePooledMarginalProjectionModel (U × T) U A)
    (parent : U × T → P) {n : ℕ} (source : Fin n → U)
    (epsilon : ℝ) : Finset (Fin n → T) := by
  classical
  exact Finset.univ.filter fun target ↦
    let joint := multiplicity (jointWord source target)
    IsPooledMarginalProfile M joint ∧
      PooledParentProfileHasDeviation M parent joint epsilon

@[simp] theorem mem_pooledMarginalDeviatingWordsForSource
    (M : SparsePooledMarginalProjectionModel (U × T) U A)
    (parent : U × T → P) {n : ℕ} (source : Fin n → U)
    (epsilon : ℝ) (target : Fin n → T) :
    target ∈ pooledMarginalDeviatingWordsForSource M parent source epsilon ↔
      IsPooledMarginalProfile M
          (multiplicity (jointWord source target)) ∧
        PooledParentProfileHasDeviation M parent
          (multiplicity (jointWord source target)) epsilon := by
  classical
  simp [pooledMarginalDeviatingWordsForSource]

/-- Native-length form of the pooled fixed-coarse method-of-types tail.  The displayed
multiplicity equality derives `n = profileMass sourceProfile * k`; no separate length premise is
required and the entropy-loss constant remains `epsilon^2 / 4`. -/
theorem card_pooledMarginalDeviatingWordsForSource_le
    (M : SparsePooledMarginalProjectionModel (U × T) U A)
    (hMcoarse : M.coarse = Prod.fst)
    (parent : U × T → P)
    (sourceProfile : U → ℕ) (hmass : 0 < profileMass sourceProfile)
    (k : ℕ) (hk : 0 < k) {n : ℕ} (source : Fin n → U)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    ((pooledMarginalDeviatingWordsForSource
      M parent source epsilon).card : ℝ) ≤
      ((((profileMass sourceProfile * k + 1) ^ Fintype.card (U × T) : ℕ) : ℝ)) *
        structuralZeroMultinomialLoss sourceProfile k *
          Real.exp (((k : ℝ) * profileMass sourceProfile) *
            (M.reference.conditionalEntropy M.coarse - epsilon ^ 2 / 4)) := by
  have hn : n = profileMass sourceProfile * k := by
    calc
      n = ∑ u, multiplicity source u := (sum_multiplicity source).symm
      _ = ∑ u, proportionalCounts sourceProfile k u := by rw [hsource]
      _ = profileMass sourceProfile * k := by
        simp only [proportionalCounts, profileMass, Finset.sum_mul]
  subst n
  have hbad :
      pooledMarginalDeviatingWordsForSource M parent source epsilon =
        pooledMarginalDeviatingWords
          M parent sourceProfile k source epsilon := by
    ext target
    rw [mem_pooledMarginalDeviatingWordsForSource,
      mem_pooledMarginalDeviatingWords]
  rw [hbad]
  exact card_pooledMarginalDeviatingWords_le
    M hMcoarse parent sourceProfile hmass k hk source hsource hepsilon

end WordType
end AlgebraicComplexity
