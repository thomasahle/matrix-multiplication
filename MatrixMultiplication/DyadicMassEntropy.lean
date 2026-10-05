import AlgebraicComplexity.Probability.DyadicMass
import MatrixMultiplication.DyadicEntropy

/-!
# Entropy semantics for exact dyadic-mass algebra

This module connects the exact product/mixture/scatter recurrence primitives to the certified
entropy evaluator.  In particular, rescaling a numerator table to a wider common denominator
does not change either its represented mass or its homogeneous entropy.  Concrete recursive
certificates may therefore combine branches at a common bit width without paying a numerical or
proof-size penalty for evaluating the padded integers.
-/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.DyadicMassEntropy

open AlgebraicComplexity
open MatrixMultiplication.DyadicEntropy

/-- Multiplying a numerator by the extra dyadic denominator represents the same real mass. -/
theorem mass_rescale (bits extra numerator : ℕ) :
    mass (bits + extra) (numerator * dyadicDenominator extra) =
      mass bits numerator := by
  unfold mass dyadicDenominator
  rw [pow_add]
  push_cast
  field_simp

/-- A Shannon summand is invariant under an exact denominator rescaling. -/
theorem entropyTerm_rescale (bits extra numerator : ℕ) :
    entropyTerm (bits + extra) (numerator * dyadicDenominator extra) =
      entropyTerm bits numerator := by
  unfold entropyTerm
  rw [mass_rescale]

/-- Homogeneous entropy is invariant under rescaling every numerator by the matching power of
two. -/
theorem weightedEntropy_rescale
    {I : Type*} [Fintype I]
    (bits extra : ℕ) (data : DyadicMassData I) :
    weightedEntropy (bits + extra) (data.rescale extra).numerator =
      weightedEntropy bits data.numerator := by
  have htotal :
      totalNumerator (data.rescale extra).numerator =
        totalNumerator data.numerator * dyadicDenominator extra := by
    unfold totalNumerator DyadicMassData.rescale
    rw [Finset.sum_mul]
  unfold weightedEntropy
  rw [htotal, entropyTerm_rescale]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact entropyTerm_rescale bits extra (data.numerator i)

end MatrixMultiplication.DyadicMassEntropy
