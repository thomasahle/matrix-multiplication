import AlgebraicComplexity.Analysis.StructuralZeroMultinomialLossCore
import AlgebraicComplexity.Analysis.StructuralZeroMultinomialEntropy
import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore

/-! # Conditional type bounds with structural zeroes -/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

open Real

universe u v

/-- Entropy-difference upper bound for one exact conditional type class.  The source profile is
fixed and scaled by `k`; the full joint type may be any legal empirical type with that source
marginal. -/
theorem card_conditionalTypeClass_le_structuralZeroLoss_mul_exp_entropyDifference
    {S : Type u} {T : Type v} [Fintype S] [Fintype T]
    (sourceProfile : S → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → S)
    (jointType : S × T → ℕ)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hjoint : jointType ∈ types (S × T) (profileMass sourceProfile * k))
    (hmap : mappedType Prod.fst jointType = multiplicity source) :
    ((conditionalTypeClass source jointType).card : ℝ) ≤
      structuralZeroMultinomialLoss sourceProfile k *
        Real.exp
          ((profileMass jointType : ℝ) * profileEntropyNats jointType -
            (k : ℝ) * (profileMass sourceProfile : ℝ) *
              profileEntropyNats sourceProfile) := by
  classical
  let sourceExponent : ℝ :=
    (k : ℝ) * (profileMass sourceProfile : ℝ) *
      profileEntropyNats sourceProfile
  let jointExponent : ℝ :=
    (profileMass jointType : ℝ) * profileEntropyNats jointType
  have hjointMass : profileMass jointType = profileMass sourceProfile * k := by
    exact mem_types.mp hjoint
  have hjointMassPos : 0 < profileMass jointType := by
    rw [hjointMass]
    positivity
  have hsourceBase :
      proportionalEntropyBase sourceProfile ^ k = Real.exp sourceExponent := by
    rw [proportionalEntropyBase_eq_exp_profileEntropy sourceProfile hmass,
      ← Real.exp_nat_mul]
    congr 1
    dsimp [sourceExponent]
    ring
  have hsourceLower :
      Real.exp sourceExponent ≤
        structuralZeroMultinomialLoss sourceProfile k *
          (Nat.multinomial Finset.univ (multiplicity source) : ℝ) := by
    rw [← hsourceBase, hsource]
    exact proportionalEntropyBase_pow_le_structuralZeroLoss_mul_multinomial
      sourceProfile k
  have hjointUpper :
      (Nat.multinomial Finset.univ jointType : ℝ) ≤ Real.exp jointExponent := by
    exact multinomial_le_exp_profileEntropy jointType hjointMassPos
  have hfactorNat :=
    multinomial_source_mul_card_conditionalTypeClass source jointType hjoint hmap
  have hfactor :
      (Nat.multinomial Finset.univ (multiplicity source) : ℝ) *
          ((conditionalTypeClass source jointType).card : ℝ) =
        (Nat.multinomial Finset.univ jointType : ℝ) := by
    exact_mod_cast hfactorNat
  have hcombined :
      Real.exp sourceExponent * ((conditionalTypeClass source jointType).card : ℝ) ≤
        structuralZeroMultinomialLoss sourceProfile k * Real.exp jointExponent := by
    calc
      _ ≤ (structuralZeroMultinomialLoss sourceProfile k *
          (Nat.multinomial Finset.univ (multiplicity source) : ℝ)) *
            ((conditionalTypeClass source jointType).card : ℝ) := by
        exact mul_le_mul_of_nonneg_right hsourceLower (by positivity)
      _ = structuralZeroMultinomialLoss sourceProfile k *
          (Nat.multinomial Finset.univ jointType : ℝ) := by rw [← hfactor]; ring
      _ ≤ structuralZeroMultinomialLoss sourceProfile k * Real.exp jointExponent := by
        exact mul_le_mul_of_nonneg_left hjointUpper
          (structuralZeroMultinomialLoss_pos sourceProfile k).le
  apply (mul_le_mul_iff_right₀ (Real.exp_pos sourceExponent)).mp
  calc
    Real.exp sourceExponent * ((conditionalTypeClass source jointType).card : ℝ) ≤
        structuralZeroMultinomialLoss sourceProfile k * Real.exp jointExponent := hcombined
    _ = Real.exp sourceExponent *
        (structuralZeroMultinomialLoss sourceProfile k *
          Real.exp (jointExponent - sourceExponent)) := by
      rw [show jointExponent = sourceExponent + (jointExponent - sourceExponent) by ring,
        Real.exp_add]
      ring_nf

end AlgebraicComplexity.WordType
