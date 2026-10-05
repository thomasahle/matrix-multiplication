import AlgebraicComplexity.Combinatorics.PushedProfileTypeCounting

/-!
# Entropy growth inside a pushed type fiber

Let `f : A → B` be a map of finite alphabets and let `profile : A → ℕ` be a nonzero
integral type.  Every word of the pushed proportional type has the same number of lifts of the
exact fine proportional type.  This file proves that the common fiber has exponential base

`proportionalEntropyBase profile /
  proportionalEntropyBase (mappedType f profile)`

up to the explicit polynomial loss already used for structural zeroes.

The result is the quantitative companion to a quotient-first tensor restriction: cleanup may be
performed on the coarser `B`-word while the entire prescribed fine typed fiber is retained inside
each surviving quotient block.  No injectivity or surjectivity assumption on `f` is needed.
-/

namespace AlgebraicComplexity.WordType

universe u v

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]

/-- An exact proportional type class is at most its entropy exponential.  This zero-safe form is
the upper-bound counterpart to
`proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass`. -/
theorem card_proportionalTypeClass_le_entropyBase_pow
    (profile : A → ℕ) (hmass : 0 < profileMass profile)
    (k : ℕ) (hk : 0 < k) :
    ((typeClass (profileMass profile * k)
        (proportionalCounts profile k)).card : ℝ) ≤
      proportionalEntropyBase profile ^ k := by
  have hscaledMassEq :
      profileMass (proportionalCounts profile k) = profileMass profile * k := by
    unfold profileMass proportionalCounts
    rw [Finset.sum_mul]
  have hscaledMass : 0 < profileMass (proportionalCounts profile k) := by
    rw [hscaledMassEq]
    exact Nat.mul_pos hmass hk
  rw [card_typeClass_eq_multinomial _ (proportionalCounts_mem_types profile k)]
  calc
    (Nat.multinomial Finset.univ (proportionalCounts profile k) : ℝ) ≤
        Real.exp
          ((profileMass (proportionalCounts profile k) : ℝ) *
            profileEntropyNats (proportionalCounts profile k)) :=
      multinomial_le_exp_profileEntropy _ hscaledMass
    _ = proportionalEntropyBase profile ^ k := by
      rw [profileEntropyNats_proportionalCounts profile hmass k hk,
        proportionalEntropyBase_eq_exp_profileEntropy profile hmass,
        ← Real.exp_nat_mul]
      congr 1
      rw [hscaledMassEq]
      push_cast
      ring

/-- Exponential base of the exact fine type fiber over one pushed type word. -/
noncomputable def pushedTypeFiberEntropyBase
    (f : A → B) (profile : A → ℕ) : ℝ :=
  proportionalEntropyBase profile /
    proportionalEntropyBase (mappedType f profile)

/-- The entropy base of a pushed exact-type fiber is strictly positive, including when either
profile contains structural zeroes. -/
theorem pushedTypeFiberEntropyBase_pos
    (f : A → B) (profile : A → ℕ) :
    0 < pushedTypeFiberEntropyBase f profile := by
  exact div_pos (proportionalEntropyBase_pos_zeroSafe profile)
    (proportionalEntropyBase_pos_zeroSafe (mappedType f profile))

/-- The quotient base is exactly the exponential of the entropy lost by observing only the
pushed symbol.  This is the bridge from the finite fiber count to certificate entropy formulas. -/
theorem pushedTypeFiberEntropyBase_eq_exp_entropyDifference
    (f : A → B) (profile : A → ℕ) (hmass : 0 < profileMass profile) :
    pushedTypeFiberEntropyBase f profile =
      Real.exp ((profileMass profile : ℝ) *
        (profileEntropyNats profile - profileEntropyNats (mappedType f profile))) := by
  have hcoarseMass : 0 < profileMass (mappedType f profile) := by
    rw [profileMass_mappedType]
    exact hmass
  unfold pushedTypeFiberEntropyBase
  rw [proportionalEntropyBase_eq_exp_profileEntropy profile hmass,
    proportionalEntropyBase_eq_exp_profileEntropy (mappedType f profile) hcoarseMass,
    ← Real.exp_sub, profileMass_mappedType]
  congr 1
  ring

/-- The only loss in the exact pushed-fiber lower bound.  It is named separately so clients can
pass it directly to sequence-level extraction APIs. -/
noncomputable def pushedTypeFiberLoss (profile : A → ℕ) (k : ℕ) : ℝ :=
  structuralZeroMultinomialLoss profile k

theorem pushedTypeFiberLoss_pos (profile : A → ℕ) (k : ℕ) :
    0 < pushedTypeFiberLoss profile k := by
  exact structuralZeroMultinomialLoss_pos profile k

/-- The exact fine-fiber loss is polynomial, hence subexponential. -/
theorem pushedTypeFiberLoss_subexponential (profile : A → ℕ) :
    Growth.Subexponential (pushedTypeFiberLoss profile) := by
  exact structuralZeroMultinomialLoss_subexponential profile

/-- Every target word of the exact pushed proportional type has exponentially many exact fine
lifts, with base equal to the quotient of the fine and pushed entropy bases.  The bound is
uniform in the target word and permits structural zeroes in both profiles. -/
theorem pushedTypeFiberEntropyBase_pow_le_loss_mul_card_typedFiber
    (f : A → B) (profile : A → ℕ) (hmass : 0 < profileMass profile)
    (k : ℕ) (hk : 0 < k)
    (target : Fin (profileMass profile * k) → B)
    (htarget : target ∈ typeClass (profileMass profile * k)
      (proportionalCounts (mappedType f profile) k)) :
    pushedTypeFiberEntropyBase f profile ^ k ≤
      pushedTypeFiberLoss profile k *
        ((typedWordMapFiber f (proportionalCounts profile k) target).card : ℝ) := by
  have hcoarseMass : 0 < profileMass (mappedType f profile) := by
    rw [profileMass_mappedType]
    exact hmass
  have hfine :=
    proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass profile k
  have hcoarse := card_proportionalTypeClass_le_entropyBase_pow
    (mappedType f profile) hcoarseMass k hk
  rw [profileMass_mappedType f profile] at hcoarse
  have hfactorNat := card_pushedTypeClass_mul_card_typedFiber
    f profile k target htarget
  have hfactor :
      ((typeClass (profileMass profile * k)
          (proportionalCounts (mappedType f profile) k)).card : ℝ) *
        ((typedWordMapFiber f (proportionalCounts profile k) target).card : ℝ) =
      ((typeClass (profileMass profile * k)
          (proportionalCounts profile k)).card : ℝ) := by
    exact_mod_cast hfactorNat
  have hcombined :
      proportionalEntropyBase profile ^ k ≤
        pushedTypeFiberLoss profile k *
          (proportionalEntropyBase (mappedType f profile) ^ k *
            ((typedWordMapFiber f (proportionalCounts profile k) target).card : ℝ)) := by
    calc
      proportionalEntropyBase profile ^ k ≤
          pushedTypeFiberLoss profile k *
            ((typeClass (profileMass profile * k)
              (proportionalCounts profile k)).card : ℝ) := hfine
      _ = pushedTypeFiberLoss profile k *
          (((typeClass (profileMass profile * k)
              (proportionalCounts (mappedType f profile) k)).card : ℝ) *
            ((typedWordMapFiber f (proportionalCounts profile k) target).card : ℝ)) := by
        rw [hfactor]
      _ ≤ pushedTypeFiberLoss profile k *
          (proportionalEntropyBase (mappedType f profile) ^ k *
            ((typedWordMapFiber f (proportionalCounts profile k) target).card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcoarse (by positivity))
          (pushedTypeFiberLoss_pos profile k).le
  rw [pushedTypeFiberEntropyBase, div_pow]
  apply (div_le_iff₀
    (pow_pos (proportionalEntropyBase_pos_zeroSafe (mappedType f profile)) k)).2
  calc
    proportionalEntropyBase profile ^ k ≤
        pushedTypeFiberLoss profile k *
          (proportionalEntropyBase (mappedType f profile) ^ k *
            ((typedWordMapFiber f (proportionalCounts profile k) target).card : ℝ)) :=
      hcombined
    _ = (pushedTypeFiberLoss profile k *
          ((typedWordMapFiber f (proportionalCounts profile k) target).card : ℝ)) *
        proportionalEntropyBase (mappedType f profile) ^ k := by
      ring

/-! ## Source-aware conditional fibers -/

variable {Cell : Type u} {Raw : Type v} {Feature : Type*}
variable [Fintype Cell] [Fintype Raw] [Fintype Feature]

/-- Source-aware form of the uniform pushed-fiber lower bound.  Once a compatibility-cell word
and a quotient-feature word are fixed, the whole conditional family of fine targets has the
same entropy-difference exponent as the corresponding joint-alphabet typed fiber. -/
theorem pushedTypeFiberEntropyBase_pow_le_loss_mul_card_conditionalTypedFeatureFiber
    (feature : Raw → Feature) (rawProfile : Cell × Raw → ℕ)
    (hmass : 0 < profileMass rawProfile)
    (k : ℕ) (hk : 0 < k)
    (source : Fin (profileMass rawProfile * k) → Cell)
    (featureTarget : Fin (profileMass rawProfile * k) → Feature)
    (hfeatureTarget : featureTarget ∈ conditionalTypeClass source
      (proportionalCounts
        (mappedType (conditionalFeatureMap feature) rawProfile) k)) :
    pushedTypeFiberEntropyBase (conditionalFeatureMap feature) rawProfile ^ k ≤
      pushedTypeFiberLoss rawProfile k *
        ((conditionalTypedFeatureFiber source feature
          (proportionalCounts rawProfile k) featureTarget).card : ℝ) := by
  have htarget : jointWord source featureTarget ∈
      typeClass (profileMass rawProfile * k)
        (proportionalCounts
          (mappedType (conditionalFeatureMap feature) rawProfile) k) := by
    rw [mem_typeClass]
    exact mem_conditionalTypeClass.mp hfeatureTarget
  have hbound := pushedTypeFiberEntropyBase_pow_le_loss_mul_card_typedFiber
    (conditionalFeatureMap feature) rawProfile hmass k hk
      (jointWord source featureTarget) htarget
  rw [card_conditionalTypedFeatureFiber_eq_card_typedWordMapFiber] at ⊢
  exact hbound

end AlgebraicComplexity.WordType
