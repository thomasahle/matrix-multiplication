import MatrixMultiplication.IntegerEntropyDual
import MatrixMultiplication.VolumeRecurrence

/-!
# Directed local bounds for the scalar volume recurrence

After `VolumeRecurrence` removes the orientation labels, every local matrix-size contribution has
one of two forms:

* a positive level-two edge contributes `(2 - 2μ) log₂ q` to the sum of the three coordinates;
* a zero constituent contributes `H(p) + E_p[ones] log₂ q` to one coordinate.

This module gives fully rational lower endpoints for both expressions.  It uses exact dyadic
numerators and the atanh logarithm bounds from `DyadicEntropy`; no floating-point quantity enters
the definitions or the soundness proofs.
-/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.VolumeBounds

open AlgebraicComplexity
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.IntegerEntropyDual

/-- Exact base-two logarithm of a positive integer matrix parameter. -/
def logIntegerBits (q : ℕ) : ℝ :=
  Real.log (q : ℝ) / Real.log 2

/-- Sum-of-three-coordinates contribution of one positive level-two edge. -/
def positiveEdgeValue (bits muNumerator q : ℕ) : ℝ :=
  (2 - 2 * mass bits muNumerator) * logIntegerBits q

/-- Rational lower endpoint for a positive level-two edge. -/
def certifiedPositiveEdgeLower (steps bits muNumerator q : ℕ) : ℝ :=
  (2 - 2 * mass bits muNumerator) * certifiedLogIntegerLower steps q

/-- The exact integer condition corresponding to `μ ≤ 1/2`. -/
theorem positiveEdge_coefficient_nonneg
    {bits muNumerator : ℕ}
    (hmu : 2 * muNumerator ≤ dyadicDenominator bits) :
    0 ≤ (2 : ℝ) - 2 * mass bits muNumerator := by
  unfold mass
  have hden : 0 < (2 : ℝ) ^ bits := by positivity
  have hnat : muNumerator ≤ 2 ^ bits := by
    have : muNumerator ≤ 2 * muNumerator := by omega
    exact this.trans (by simpa [dyadicDenominator] using hmu)
  have hcast : (muNumerator : ℝ) ≤ (2 : ℝ) ^ bits := by
    exact_mod_cast hnat
  have hfraction : (muNumerator : ℝ) / (2 : ℝ) ^ bits ≤ 1 :=
    (div_le_one hden).2 hcast
  linarith

/-- Soundness of the positive-edge rational lower endpoint. -/
theorem certifiedPositiveEdgeLower_le
    {steps bits muNumerator q : ℕ}
    (hq : 0 < q)
    (hmu : 2 * muNumerator ≤ dyadicDenominator bits) :
    certifiedPositiveEdgeLower steps bits muNumerator q ≤
      positiveEdgeValue bits muNumerator q := by
  unfold certifiedPositiveEdgeLower positiveEdgeValue logIntegerBits
  exact mul_le_mul_of_nonneg_left (certifiedLogIntegerLower_le hq)
    (positiveEdge_coefficient_nonneg hmu)

/-- Expected number of `1` symbols under a dyadic complete-split law. -/
def expectedOnes
    {Symbol : Type*} [Fintype Symbol]
    (bits : ℕ) (numerator ones : Symbol → ℕ) : ℝ :=
  ∑ symbol, mass bits (numerator symbol) * ones symbol

/-- Exact scalar size of a zero constituent. -/
def zeroConstituentValue
    {Symbol : Type*} [Fintype Symbol]
    (bits : ℕ) (numerator ones : Symbol → ℕ) (q : ℕ) : ℝ :=
  (∑ symbol, entropyTerm bits (numerator symbol)) +
    expectedOnes bits numerator ones * logIntegerBits q

/-- Fully rational lower endpoint for a zero constituent. -/
def certifiedZeroConstituentLower
    {Symbol : Type*} [Fintype Symbol]
    (steps bits : ℕ) (numerator ones : Symbol → ℕ) (q : ℕ) : ℝ :=
  certifiedEntropyLower bits steps numerator +
    expectedOnes bits numerator ones * certifiedLogIntegerLower steps q

theorem expectedOnes_nonneg
    {Symbol : Type*} [Fintype Symbol]
    (bits : ℕ) (numerator ones : Symbol → ℕ) :
    0 ≤ expectedOnes bits numerator ones := by
  unfold expectedOnes
  exact Finset.sum_nonneg fun symbol _ ↦ mul_nonneg (by
    unfold mass
    positivity) (by positivity)

/-- Soundness of the zero-constituent rational lower endpoint. -/
theorem certifiedZeroConstituentLower_le
    {Symbol : Type*} [Fintype Symbol]
    {steps bits q : ℕ} (numerator ones : Symbol → ℕ)
    (hq : 0 < q) :
    certifiedZeroConstituentLower steps bits numerator ones q ≤
      zeroConstituentValue bits numerator ones q := by
  unfold certifiedZeroConstituentLower zeroConstituentValue logIntegerBits
  exact add_le_add
    (certifiedEntropyLower_le bits steps numerator)
    (mul_le_mul_of_nonneg_left (certifiedLogIntegerLower_le hq)
      (expectedOnes_nonneg bits numerator ones))

/-- Pointwise directed bounds remain sound after weighting by nonnegative exact recurrence
masses. -/
theorem weighted_local_lower_le
    {Node : Type*} [Fintype Node]
    (mass lower exact : Node → ℝ)
    (hmass : ∀ node, 0 ≤ mass node)
    (hlower : ∀ node, lower node ≤ exact node) :
    (∑ node, mass node * lower node) ≤
      ∑ node, mass node * exact node := by
  apply Finset.sum_le_sum
  intro node _
  exact mul_le_mul_of_nonneg_left (hlower node) (hmass node)

end MatrixMultiplication.VolumeBounds
