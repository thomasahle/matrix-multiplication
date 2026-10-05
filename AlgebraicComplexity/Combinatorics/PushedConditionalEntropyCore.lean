import AlgebraicComplexity.Analysis.StructuralZeroMultinomialLossCore
import AlgebraicComplexity.Combinatorics.ProportionalTypeClassCore
import AlgebraicComplexity.Probability.IntegralProfileCore

/-! # Core entropy data for proportional conditional types -/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v

variable {A : Type u} [Fintype A]

/-! ## Conditional cell/profile count -/

variable {Cell : Type u} {Feature : Type v}
variable [Fintype Cell] [Fintype Feature]

/-- Exponential base of a fixed joint cell/feature type relative to its cell marginal. -/
noncomputable def conditionalProfileEntropyBase
    (cellProfile : Cell → ℕ) (jointProfile : Cell × Feature → ℕ) : ℝ :=
  Real.exp
    ((profileMass jointProfile : ℝ) * profileEntropyNats jointProfile -
      (profileMass cellProfile : ℝ) * profileEntropyNats cellProfile)

theorem conditionalProfileEntropyBase_pos
    (cellProfile : Cell → ℕ) (jointProfile : Cell × Feature → ℕ) :
    0 < conditionalProfileEntropyBase cellProfile jointProfile := by
  exact Real.exp_pos _

/-- The only nonexponential loss in exact pushed conditional-type counting. -/
noncomputable def pushedConditionalTypeLoss
    (cellProfile : Cell → ℕ) (k : ℕ) : ℝ :=
  structuralZeroMultinomialLoss cellProfile k

theorem pushedConditionalTypeLoss_pos
    (cellProfile : Cell → ℕ) (k : ℕ) :
    0 < pushedConditionalTypeLoss cellProfile k := by
  exact structuralZeroMultinomialLoss_pos cellProfile k

/-- Scaling a positive-mass profile by a positive repetition does not change its normalized
Shannon entropy. -/
theorem profileEntropyNats_proportionalCounts
    (profile : A → ℕ) (hmass : 0 < profileMass profile)
    (k : ℕ) (hk : 0 < k) :
    profileEntropyNats (proportionalCounts profile k) =
      profileEntropyNats profile := by
  have hscaledMass : 0 < profileMass (proportionalCounts profile k) := by
    have hmassScale :
        profileMass (proportionalCounts profile k) = profileMass profile * k := by
      unfold profileMass proportionalCounts
      rw [Finset.sum_mul]
    rw [hmassScale]
    exact Nat.mul_pos hmass hk
  have hprob := normalizedProfileProbability_proportionalCounts profile hmass hk
  have hentropy := congrArg ProbabilityVector.entropy hprob
  simpa only [normalizedProfileProbability_entropy] using hentropy

end AlgebraicComplexity.WordType
