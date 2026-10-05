import AlgebraicComplexity.Analysis.StructuralZeroMultinomialLoss
import AlgebraicComplexity.Combinatorics.ProportionalTypeClassCore

/-!
# Proportional type-class growth

This file gives the direct sequence-facing form of the method-of-types lower bound.  A fixed
integral profile may contain structural zeroes.  Repeating it `k` times yields an exact type class
whose cardinality grows with base `proportionalEntropyBase profile`, up to the explicit
subexponential loss `structuralZeroMultinomialLoss profile k`.
-/

namespace AlgebraicComplexity.WordType

universe u

variable {I : Type u} [Fintype I]

/-- The entropy base is strictly positive even when the integral profile has structural zeroes. -/
theorem proportionalEntropyBase_pos_zeroSafe (profile : I → ℕ) :
    0 < proportionalEntropyBase profile := by
  unfold proportionalEntropyBase
  exact div_pos (factorialEntropyTerm_pos_zeroSafe _)
    (Finset.prod_pos fun i _ ↦ factorialEntropyTerm_pos_zeroSafe (profile i))

/-- Sequence-ready lower growth bound for one exact proportional type class. -/
theorem proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass
    (profile : I → ℕ) (k : ℕ) :
    proportionalEntropyBase profile ^ k ≤
      structuralZeroMultinomialLoss profile k *
        ((typeClass (profileMass profile * k)
          (proportionalCounts profile k)).card : ℝ) := by
  rw [card_typeClass_eq_multinomial _ (proportionalCounts_mem_types profile k)]
  exact proportionalEntropyBase_pow_le_structuralZeroLoss_mul_multinomial profile k

end AlgebraicComplexity.WordType
