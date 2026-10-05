import AlgebraicComplexity.Combinatorics.ProportionalConditionalTypeCounting
import AlgebraicComplexity.Combinatorics.PushedProfileTypeCountingCore

/-!
# Conditional type counting after an alphabet quotient

This smallest public leaf contains only the pushed-profile specialization.  Its entropy and exact
fine-lift dependencies are sealed in separate semantic modules to keep compilation bounded.
-/

namespace AlgebraicComplexity.WordType

universe u v w

variable {Cell : Type u} {Feature : Type v}
variable [Fintype Cell] [Fintype Feature]

variable {Raw : Type w} [Fintype Raw]

/-- Quotient-feature Claim 6.18 count for a pushed integral profile.  The source marginal is
checked on the raw table, while the displayed entropy base is computed solely from the exact
pushed cell/feature table consumed by the numerical evaluator. -/
theorem card_pushedConditionalTypeClass_le_entropyBase_pow
    (feature : Raw → Feature) (rawProfile : Cell × Raw → ℕ)
    (cellProfile : Cell → ℕ)
    (hmargin : mappedType Prod.fst rawProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k)
    (source : Fin (profileMass cellProfile * k) → Cell)
    (hsource : multiplicity source = proportionalCounts cellProfile k) :
    ((conditionalTypeClass source
        (proportionalCounts
          (mappedType (conditionalFeatureMap feature) rawProfile) k)).card : ℝ) ≤
      structuralZeroMultinomialLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile
          (mappedType (conditionalFeatureMap feature) rawProfile) ^ k := by
  apply card_proportionalConditionalTypeClass_le_entropyBase_pow
    cellProfile (mappedType (conditionalFeatureMap feature) rawProfile)
      ?_ hmass k hk source hsource
  rw [mappedType_fst_pushedConditionalProfile, hmargin]

/-- Sequence-facing pushed-profile theorem with the positive subexponential loss named
explicitly. -/
theorem card_pushedConditionalTypeClass_le_loss_mul_entropyBase_pow
    (feature : Raw → Feature) (rawProfile : Cell × Raw → ℕ)
    (cellProfile : Cell → ℕ)
    (hmargin : mappedType Prod.fst rawProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k)
    (source : Fin (profileMass cellProfile * k) → Cell)
    (hsource : multiplicity source = proportionalCounts cellProfile k) :
    ((conditionalTypeClass source
        (proportionalCounts
          (mappedType (conditionalFeatureMap feature) rawProfile) k)).card : ℝ) ≤
      pushedConditionalTypeLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile
          (mappedType (conditionalFeatureMap feature) rawProfile) ^ k := by
  exact card_pushedConditionalTypeClass_le_entropyBase_pow
    feature rawProfile cellProfile hmargin hmass k hk source hsource

end AlgebraicComplexity.WordType
