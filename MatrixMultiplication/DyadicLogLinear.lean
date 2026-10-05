import MatrixMultiplication.FastDyadicLog
import MatrixMultiplication.IntegerEntropyDual

/-!
# Certified dyadic log-linear forms

After exact symbolic aggregation, entropy-heavy certificate outputs often have the form

`constant / 2^b + Σ pᵢ / 2^b * log₂(aᵢ) - Σ nⱼ / 2^b * log₂(cⱼ)`.

This representation is substantially smaller than retaining every intermediate probability row.
The definitions below evaluate directed rational endpoints, and the soundness theorems reduce the
entire analytic proof to positivity of the integer logarithm arguments.  Exact recurrence theorems
remain responsible for proving the aggregated coefficients.
-/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.DyadicLogLinear

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.IntegerEntropyDual

variable {Positive Negative : Type*}

/-- A nonnegative-coefficient dyadic linear combination of integer logarithms. -/
def logSum [Fintype Positive]
    (bits : ℕ) (argument coefficient : Positive → ℕ) : ℝ :=
  ∑ term, mass bits (coefficient term) *
    (Real.log (argument term : ℝ) / Real.log 2)

/-- Fast rational lower endpoint for `logSum`. -/
def fastLogSumLower [Fintype Positive]
    (steps bits : ℕ) (argument coefficient : Positive → ℕ) : ℝ :=
  ∑ term, mass bits (coefficient term) *
    FastDyadicLog.certifiedLogIntegerLower steps (argument term)

/-- Fast rational upper endpoint for `logSum`. -/
def fastLogSumUpper [Fintype Positive]
    (steps bits : ℕ) (argument coefficient : Positive → ℕ) : ℝ :=
  ∑ term, mass bits (coefficient term) *
    FastDyadicLog.certifiedLogIntegerUpper steps (argument term)

/-- Generated-scale variant of `fastLogSumLower`.  Supplying `floor(log₂ argument)` avoids
reducing `Nat.log` separately in every large generated proof. -/
def fastLogSumLowerWithScale [Fintype Positive]
    (steps bits : ℕ) (argument coefficient scale : Positive → ℕ) : ℝ :=
  ∑ term, mass bits (coefficient term) *
    FastDyadicLog.numeratorLogLower (argument term) (scale term) steps

/-- Generated-scale variant of `fastLogSumUpper`. -/
def fastLogSumUpperWithScale [Fintype Positive]
    (steps bits : ℕ) (argument coefficient scale : Positive → ℕ) : ℝ :=
  ∑ term, mass bits (coefficient term) *
    FastDyadicLog.numeratorLogUpper (argument term) (scale term) steps

theorem fastLogSumLower_le_logSum
    [Fintype Positive]
    (steps bits : ℕ) (argument coefficient : Positive → ℕ)
    (hargument : ∀ term, 0 < argument term) :
    fastLogSumLower steps bits argument coefficient ≤
      logSum bits argument coefficient := by
  apply Finset.sum_le_sum
  intro term _
  exact mul_le_mul_of_nonneg_left
    (FastDyadicLog.certifiedLogIntegerLower_le (hargument term)) (by
      unfold mass
      positivity)

theorem logSum_le_fastLogSumUpper
    [Fintype Positive]
    (steps bits : ℕ) (argument coefficient : Positive → ℕ)
    (hargument : ∀ term, 0 < argument term) :
    logSum bits argument coefficient ≤
      fastLogSumUpper steps bits argument coefficient := by
  apply Finset.sum_le_sum
  intro term _
  exact mul_le_mul_of_nonneg_left
    (FastDyadicLog.le_certifiedLogIntegerUpper (hargument term)) (by
      unfold mass
      positivity)

theorem fastLogSumLowerWithScale_le_logSum
    [Fintype Positive]
    (steps bits : ℕ) (argument coefficient scale : Positive → ℕ)
    (hscale : ∀ term, 2 ^ scale term ≤ argument term) :
    fastLogSumLowerWithScale steps bits argument coefficient scale ≤
      logSum bits argument coefficient := by
  apply Finset.sum_le_sum
  intro term _
  exact mul_le_mul_of_nonneg_left
    (FastDyadicLog.numeratorLogLower_le (hscale term)) (by
      unfold mass
      positivity)

theorem logSum_le_fastLogSumUpperWithScale
    [Fintype Positive]
    (steps bits : ℕ) (argument coefficient scale : Positive → ℕ)
    (hscale : ∀ term, 2 ^ scale term ≤ argument term) :
    logSum bits argument coefficient ≤
      fastLogSumUpperWithScale steps bits argument coefficient scale := by
  apply Finset.sum_le_sum
  intro term _
  exact mul_le_mul_of_nonneg_left
    (FastDyadicLog.le_numeratorLogUpper (hscale term)) (by
      unfold mass
      positivity)

/-- Exact real value of a dyadic log-linear form. -/
def value [Fintype Positive] [Fintype Negative]
    (bits constantNumerator : ℕ)
    (positiveArgument positiveCoefficient : Positive → ℕ)
    (negativeArgument negativeCoefficient : Negative → ℕ) : ℝ :=
  mass bits constantNumerator +
      ∑ term, mass bits (positiveCoefficient term) *
        (Real.log (positiveArgument term : ℝ) / Real.log 2) -
    ∑ term, mass bits (negativeCoefficient term) *
      (Real.log (negativeArgument term : ℝ) / Real.log 2)

/-- Fully rational lower endpoint.  Positive coefficients use lower log endpoints; subtracted
coefficients use upper log endpoints. -/
def certifiedLower [Fintype Positive] [Fintype Negative]
    (steps bits constantNumerator : ℕ)
    (positiveArgument positiveCoefficient : Positive → ℕ)
    (negativeArgument negativeCoefficient : Negative → ℕ) : ℝ :=
  mass bits constantNumerator +
      ∑ term, mass bits (positiveCoefficient term) *
        certifiedLogIntegerLower steps (positiveArgument term) -
    ∑ term, mass bits (negativeCoefficient term) *
      certifiedLogIntegerUpper steps (negativeArgument term)

/-- Fully rational upper endpoint. -/
def certifiedUpper [Fintype Positive] [Fintype Negative]
    (steps bits constantNumerator : ℕ)
    (positiveArgument positiveCoefficient : Positive → ℕ)
    (negativeArgument negativeCoefficient : Negative → ℕ) : ℝ :=
  mass bits constantNumerator +
      ∑ term, mass bits (positiveCoefficient term) *
        certifiedLogIntegerUpper steps (positiveArgument term) -
    ∑ term, mass bits (negativeCoefficient term) *
      certifiedLogIntegerLower steps (negativeArgument term)

/-- Fast rational lower endpoint using the once-certified decimal enclosure for `log 2`. -/
def fastCertifiedLower [Fintype Positive] [Fintype Negative]
    (steps bits constantNumerator : ℕ)
    (positiveArgument positiveCoefficient : Positive → ℕ)
    (negativeArgument negativeCoefficient : Negative → ℕ) : ℝ :=
  mass bits constantNumerator +
      ∑ term, mass bits (positiveCoefficient term) *
        FastDyadicLog.certifiedLogIntegerLower steps (positiveArgument term) -
    ∑ term, mass bits (negativeCoefficient term) *
      FastDyadicLog.certifiedLogIntegerUpper steps (negativeArgument term)

/-- Fast rational upper endpoint. -/
def fastCertifiedUpper [Fintype Positive] [Fintype Negative]
    (steps bits constantNumerator : ℕ)
    (positiveArgument positiveCoefficient : Positive → ℕ)
    (negativeArgument negativeCoefficient : Negative → ℕ) : ℝ :=
  mass bits constantNumerator +
      ∑ term, mass bits (positiveCoefficient term) *
        FastDyadicLog.certifiedLogIntegerUpper steps (positiveArgument term) -
    ∑ term, mass bits (negativeCoefficient term) *
      FastDyadicLog.certifiedLogIntegerLower steps (negativeArgument term)

theorem certifiedLower_le_value
    [Fintype Positive] [Fintype Negative]
    (steps bits constantNumerator : ℕ)
    (positiveArgument positiveCoefficient : Positive → ℕ)
    (negativeArgument negativeCoefficient : Negative → ℕ)
    (hpositive : ∀ term, 0 < positiveArgument term)
    (hnegative : ∀ term, 0 < negativeArgument term) :
    certifiedLower steps bits constantNumerator
        positiveArgument positiveCoefficient negativeArgument negativeCoefficient ≤
      value bits constantNumerator
        positiveArgument positiveCoefficient negativeArgument negativeCoefficient := by
  unfold certifiedLower value
  apply sub_le_sub
  · apply add_le_add (le_refl _)
    apply Finset.sum_le_sum
    intro term _
    exact mul_le_mul_of_nonneg_left
      (certifiedLogIntegerLower_le (hpositive term)) (by
        unfold mass
        positivity)
  · apply Finset.sum_le_sum
    intro term _
    exact mul_le_mul_of_nonneg_left
      (le_certifiedLogIntegerUpper (hnegative term)) (by
        unfold mass
        positivity)

theorem value_le_certifiedUpper
    [Fintype Positive] [Fintype Negative]
    (steps bits constantNumerator : ℕ)
    (positiveArgument positiveCoefficient : Positive → ℕ)
    (negativeArgument negativeCoefficient : Negative → ℕ)
    (hpositive : ∀ term, 0 < positiveArgument term)
    (hnegative : ∀ term, 0 < negativeArgument term) :
    value bits constantNumerator
        positiveArgument positiveCoefficient negativeArgument negativeCoefficient ≤
      certifiedUpper steps bits constantNumerator
        positiveArgument positiveCoefficient negativeArgument negativeCoefficient := by
  unfold certifiedUpper value
  apply sub_le_sub
  · apply add_le_add (le_refl _)
    apply Finset.sum_le_sum
    intro term _
    exact mul_le_mul_of_nonneg_left
      (le_certifiedLogIntegerUpper (hpositive term)) (by
        unfold mass
        positivity)
  · apply Finset.sum_le_sum
    intro term _
    exact mul_le_mul_of_nonneg_left
      (certifiedLogIntegerLower_le (hnegative term)) (by
        unfold mass
        positivity)

theorem fastCertifiedLower_le_value
    [Fintype Positive] [Fintype Negative]
    (steps bits constantNumerator : ℕ)
    (positiveArgument positiveCoefficient : Positive → ℕ)
    (negativeArgument negativeCoefficient : Negative → ℕ)
    (hpositive : ∀ term, 0 < positiveArgument term)
    (hnegative : ∀ term, 0 < negativeArgument term) :
    fastCertifiedLower steps bits constantNumerator
        positiveArgument positiveCoefficient negativeArgument negativeCoefficient ≤
      value bits constantNumerator
        positiveArgument positiveCoefficient negativeArgument negativeCoefficient := by
  unfold fastCertifiedLower value
  apply sub_le_sub
  · apply add_le_add (le_refl _)
    apply Finset.sum_le_sum
    intro term _
    exact mul_le_mul_of_nonneg_left
      (FastDyadicLog.certifiedLogIntegerLower_le (hpositive term)) (by
        unfold mass
        positivity)
  · apply Finset.sum_le_sum
    intro term _
    exact mul_le_mul_of_nonneg_left
      (FastDyadicLog.le_certifiedLogIntegerUpper (hnegative term)) (by
        unfold mass
        positivity)

theorem value_le_fastCertifiedUpper
    [Fintype Positive] [Fintype Negative]
    (steps bits constantNumerator : ℕ)
    (positiveArgument positiveCoefficient : Positive → ℕ)
    (negativeArgument negativeCoefficient : Negative → ℕ)
    (hpositive : ∀ term, 0 < positiveArgument term)
    (hnegative : ∀ term, 0 < negativeArgument term) :
    value bits constantNumerator
        positiveArgument positiveCoefficient negativeArgument negativeCoefficient ≤
      fastCertifiedUpper steps bits constantNumerator
        positiveArgument positiveCoefficient negativeArgument negativeCoefficient := by
  unfold fastCertifiedUpper value
  apply sub_le_sub
  · apply add_le_add (le_refl _)
    apply Finset.sum_le_sum
    intro term _
    exact mul_le_mul_of_nonneg_left
      (FastDyadicLog.le_certifiedLogIntegerUpper (hpositive term)) (by
        unfold mass
        positivity)
  · apply Finset.sum_le_sum
    intro term _
    exact mul_le_mul_of_nonneg_left
      (FastDyadicLog.certifiedLogIntegerLower_le (hnegative term)) (by
        unfold mass
        positivity)

end MatrixMultiplication.DyadicLogLinear
