import AlgebraicComplexity.Analysis.StructuralZeroMultinomialLoss
import AlgebraicComplexity.Combinatorics.PushedConditionalEntropyCore

/-! # Sequence-facing entropy data for proportional conditional types -/

namespace AlgebraicComplexity.WordType

universe u v

variable {Cell : Type u} {Feature : Type v}
variable [Fintype Cell] [Fintype Feature]

/-- For a fixed cell profile, exact pushed conditional types have only subexponential overhead. -/
theorem pushedConditionalTypeLoss_subexponential
    (cellProfile : Cell → ℕ) :
    Growth.Subexponential (pushedConditionalTypeLoss cellProfile) := by
  exact structuralZeroMultinomialLoss_subexponential cellProfile

end AlgebraicComplexity.WordType
