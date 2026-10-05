import AlgebraicComplexity.Analysis.Log
import AlgebraicComplexity.Probability.DyadicTable
import AlgebraicComplexity.Probability.Entropy
import MatrixMultiplication.DyadicEntropyDefs
import MatrixMultiplication.LogBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified entropy bounds for dyadic certificate tables

The level-four certificate stores every primary probability as an integer divided by a power of
two.  This module turns such integer tables into rigorous lower and upper Shannon-entropy bounds.
It uses the same rational atanh series as `MatrixMultiplication.LogBounds`; no floating-point
number or external interval result enters the statements.

For a positive numerator `a` with `2^k <= a < 2^(k+1)`, put

`x = (a - 2^k) / (a + 2^k)`.

Then `0 <= x < 1` and

`log₂ a = k + log ((1+x)/(1-x)) / log 2`.

The definitions `numeratorLogLower` and `numeratorLogUpper` enclose this value with a finite
rational series.  `entropyLower` and `entropyUpper` aggregate arbitrary pointwise logarithm
certificates over a dyadic mass table.  The latter interface is intentionally independent of a
particular generated array, so the same evaluator can be used at every recursive level.

The primitive `mass` and `entropyTerm` definitions are re-exported from the small
`DyadicEntropyDefs` leaf so semantic clients need not import this certificate-bound theorem layer.
-/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.DyadicEntropy

open AlgebraicComplexity
open AlgebraicComplexity.Analysis

universe u

/-- Reduction of a positive integer numerator to the atanh interval `[0,1)`. -/
def reducedArgument (numerator scale : ℕ) : ℝ :=
  ((numerator : ℝ) - (2 : ℝ) ^ scale) /
    ((numerator : ℝ) + (2 : ℝ) ^ scale)

/-- Rational lower endpoint for `log₂ numerator`, given its binary scale. -/
def numeratorLogLower (numerator scale steps : ℕ) : ℝ :=
  scale + logRatioLower (reducedArgument numerator scale) steps / LogBounds.logTwoUpper

/-- Rational upper endpoint for `log₂ numerator`, given its binary scale. -/
def numeratorLogUpper (numerator scale steps : ℕ) : ℝ :=
  scale + logRatioUpper (reducedArgument numerator scale) steps / LogBounds.logTwoLower

/-- Canonical binary scale used by the executable evaluator. -/
def numeratorBinaryScale (numerator : ℕ) : ℕ := Nat.log 2 numerator

theorem pow_numeratorBinaryScale_le {numerator : ℕ} (hn : 0 < numerator) :
    2 ^ numeratorBinaryScale numerator ≤ numerator := by
  exact Nat.pow_log_le_self 2 hn.ne'

private theorem logTwoUpper_pos : 0 < LogBounds.logTwoUpper :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le LogBounds.logTwo_le_logTwoUpper

theorem reducedArgument_nonneg {numerator scale : ℕ}
    (hlower : 2 ^ scale ≤ numerator) :
    0 ≤ reducedArgument numerator scale := by
  have hdiff : 0 ≤ (numerator : ℝ) - (2 : ℝ) ^ scale := by
    exact sub_nonneg.mpr (by exact_mod_cast hlower)
  have hsum : 0 ≤ (numerator : ℝ) + (2 : ℝ) ^ scale := by positivity
  exact div_nonneg hdiff hsum

theorem reducedArgument_lt_one {numerator scale : ℕ}
    (_hlower : 2 ^ scale ≤ numerator) :
    reducedArgument numerator scale < 1 := by
  have hpow : 0 < (2 : ℝ) ^ scale := by positivity
  have hnum : 0 ≤ (numerator : ℝ) := by positivity
  rw [reducedArgument, div_lt_one (by positivity : 0 < (numerator : ℝ) + 2 ^ scale)]
  linarith

theorem one_add_reduced_div_one_sub_reduced {numerator scale : ℕ}
    (_hlower : 2 ^ scale ≤ numerator) :
    (1 + reducedArgument numerator scale) /
        (1 - reducedArgument numerator scale) =
      (numerator : ℝ) / (2 : ℝ) ^ scale := by
  have hpow : (2 : ℝ) ^ scale ≠ 0 := by positivity
  have hsum : (numerator : ℝ) + (2 : ℝ) ^ scale ≠ 0 := by
    have : 0 < (numerator : ℝ) + (2 : ℝ) ^ scale := by positivity
    exact this.ne'
  rw [reducedArgument]
  field_simp
  ring

private theorem log_numerator_decompose {numerator scale : ℕ}
    (hlower : 2 ^ scale ≤ numerator) :
    Real.log (numerator : ℝ) =
      scale * Real.log 2 +
        Real.log ((1 + reducedArgument numerator scale) /
          (1 - reducedArgument numerator scale)) := by
  have hn : 0 < numerator := (Nat.pow_pos (by norm_num : 0 < (2 : ℕ))).trans_le hlower
  have hpow : (2 : ℝ) ^ scale ≠ 0 := by positivity
  have hratio :
      (numerator : ℝ) / (2 : ℝ) ^ scale ≠ 0 :=
    div_ne_zero (by exact_mod_cast hn.ne') hpow
  have hmul :
      (numerator : ℝ) = (2 : ℝ) ^ scale *
        ((numerator : ℝ) / (2 : ℝ) ^ scale) := by
    field_simp
  rw [hmul, Real.log_mul (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hratio,
    Real.log_pow]
  rw [← one_add_reduced_div_one_sub_reduced hlower]

/-- The finite rational lower endpoint really is below `log₂ numerator`. -/
theorem numeratorLogLower_le {numerator scale steps : ℕ}
    (hlower : 2 ^ scale ≤ numerator) :
    numeratorLogLower numerator scale steps ≤
      Real.log (numerator : ℝ) / Real.log 2 := by
  let x := reducedArgument numerator scale
  have hx0 : 0 ≤ x := reducedArgument_nonneg hlower
  have hx1 : x < 1 := reducedArgument_lt_one hlower
  have hratioNonneg :
      0 ≤ Real.log ((1 + x) / (1 - x)) := by
    have hratioOne : (1 : ℝ) ≤ (1 + x) / (1 - x) := by
      apply (le_div_iff₀ (sub_pos.mpr hx1)).2
      linarith
    exact Real.log_nonneg hratioOne
  have hpartialNonneg : 0 ≤ logRatioLower x steps := by
    unfold logRatioLower atanhPartial
    positivity
  have hseries :
      logRatioLower x steps ≤ Real.log ((1 + x) / (1 - x)) :=
    logRatioLower_le hx0 hx1 steps
  have hfirst :
      logRatioLower x steps / LogBounds.logTwoUpper ≤
        Real.log ((1 + x) / (1 - x)) / LogBounds.logTwoUpper :=
    div_le_div_of_nonneg_right hseries logTwoUpper_pos.le
  have hsecond :
      Real.log ((1 + x) / (1 - x)) / LogBounds.logTwoUpper ≤
        Real.log ((1 + x) / (1 - x)) / Real.log 2 :=
    div_le_div_of_nonneg_left hratioNonneg (Real.log_pos (by norm_num))
      LogBounds.logTwo_le_logTwoUpper
  rw [numeratorLogLower, log_numerator_decompose hlower]
  dsimp only [x] at hfirst hsecond ⊢
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [add_div, mul_div_cancel_right₀ (scale : ℝ) hlogTwo]
  linarith

/-- The finite rational upper endpoint really is above `log₂ numerator`. -/
theorem le_numeratorLogUpper {numerator scale steps : ℕ}
    (hlower : 2 ^ scale ≤ numerator) :
    Real.log (numerator : ℝ) / Real.log 2 ≤
      numeratorLogUpper numerator scale steps := by
  let x := reducedArgument numerator scale
  have hx0 : 0 ≤ x := reducedArgument_nonneg hlower
  have hx1 : x < 1 := reducedArgument_lt_one hlower
  have hratioNonneg :
      0 ≤ Real.log ((1 + x) / (1 - x)) := by
    have hratioOne : (1 : ℝ) ≤ (1 + x) / (1 - x) := by
      apply (le_div_iff₀ (sub_pos.mpr hx1)).2
      linarith
    exact Real.log_nonneg hratioOne
  have hseries := le_logRatioUpper hx0 hx1 steps
  have hupperNonneg : 0 ≤ logRatioUpper x steps := hratioNonneg.trans hseries
  have hfirst :
      Real.log ((1 + x) / (1 - x)) / Real.log 2 ≤
        logRatioUpper x steps / Real.log 2 :=
    div_le_div_of_nonneg_right hseries (Real.log_pos (by norm_num)).le
  have hsecond :
      logRatioUpper x steps / Real.log 2 ≤
        logRatioUpper x steps / LogBounds.logTwoLower :=
    div_le_div_of_nonneg_left hupperNonneg LogBounds.logTwoLower_pos
      LogBounds.logTwoLower_le_logTwo
  rw [numeratorLogUpper, log_numerator_decompose hlower]
  dsimp only [x] at hfirst hsecond ⊢
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [add_div, mul_div_cancel_right₀ (scale : ℝ) hlogTwo]
  linarith

theorem entropyTerm_zero (bits : ℕ) : entropyTerm bits 0 = 0 := by
  simp [entropyTerm, mass, Real.negMulLog]

theorem entropyTerm_eq {bits numerator : ℕ} (hn : 0 < numerator) :
    entropyTerm bits numerator =
      mass bits numerator *
        (bits - Real.log (numerator : ℝ) / Real.log 2) := by
  have hmass : 0 < mass bits numerator := by
    unfold mass
    positivity
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hnreal : (numerator : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : (2 : ℝ) ^ bits ≠ 0 := by positivity
  simp only [entropyTerm, Real.negMulLog_eq_neg, mass]
  rw [Real.log_div hnreal hpow, Real.log_pow]
  field_simp
  ring

/-- A pointwise upper bound on the numerator logarithm gives a lower entropy summand. -/
theorem entropyTerm_lower_of_logUpper {bits numerator : ℕ} {upper : ℝ}
    (hn : 0 < numerator)
    (hupper : Real.log (numerator : ℝ) / Real.log 2 ≤ upper) :
    mass bits numerator * (bits - upper) ≤ entropyTerm bits numerator := by
  rw [entropyTerm_eq hn]
  have hmass : 0 ≤ mass bits numerator := by
    unfold mass
    positivity
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hupper _) hmass

/-- A pointwise lower bound on the numerator logarithm gives an upper entropy summand. -/
theorem entropyTerm_upper_of_logLower {bits numerator : ℕ} {lower : ℝ}
    (hn : 0 < numerator)
    (hlower : lower ≤ Real.log (numerator : ℝ) / Real.log 2) :
    entropyTerm bits numerator ≤ mass bits numerator * (bits - lower) := by
  rw [entropyTerm_eq hn]
  have hmass : 0 ≤ mass bits numerator := by
    unfold mass
    positivity
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hlower _) hmass

/-- Zero-aware form of `entropyTerm_lower_of_logUpper`, convenient for generated arrays. -/
theorem entropyTerm_lower_of_logUpper_or_zero {bits numerator : ℕ} {upper : ℝ}
    (hupper : 0 < numerator →
      Real.log (numerator : ℝ) / Real.log 2 ≤ upper) :
    mass bits numerator * (bits - upper) ≤ entropyTerm bits numerator := by
  by_cases hn : numerator = 0
  · simp [hn, mass, entropyTerm_zero]
  · exact entropyTerm_lower_of_logUpper (Nat.pos_of_ne_zero hn)
      (hupper (Nat.pos_of_ne_zero hn))

/-- Zero-aware form of `entropyTerm_upper_of_logLower`, convenient for generated arrays. -/
theorem entropyTerm_upper_of_logLower_or_zero {bits numerator : ℕ} {lower : ℝ}
    (hlower : 0 < numerator →
      lower ≤ Real.log (numerator : ℝ) / Real.log 2) :
    entropyTerm bits numerator ≤ mass bits numerator * (bits - lower) := by
  by_cases hn : numerator = 0
  · simp [hn, mass, entropyTerm_zero]
  · exact entropyTerm_upper_of_logLower (Nat.pos_of_ne_zero hn)
      (hlower (Nat.pos_of_ne_zero hn))

/-- Rational expression accumulated by a generated lower entropy certificate. -/
def entropyLower [Fintype ι] (bits : ℕ) (numerator : ι → ℕ)
    (logUpper : ι → ℝ) : ℝ :=
  ∑ i, mass bits (numerator i) * (bits - logUpper i)

/-- Rational expression accumulated by a generated upper entropy certificate. -/
def entropyUpper [Fintype ι] (bits : ℕ) (numerator : ι → ℕ)
    (logLower : ι → ℝ) : ℝ :=
  ∑ i, mass bits (numerator i) * (bits - logLower i)

/-- Total integer numerator of a finite dyadic mass vector. -/
def totalNumerator [Fintype ι] (numerator : ι → ℕ) : ℕ :=
  ∑ i, numerator i

/-- Homogeneous entropy of an unnormalized dyadic mass vector.

If `w = ∑ᵢ mᵢ`, this is `-∑ᵢ mᵢ log₂ mᵢ + w log₂ w`.  It is the `wentropy`
operation used throughout the recursive evaluator. -/
def weightedEntropy [Fintype ι] (bits : ℕ) (numerator : ι → ℕ) : ℝ :=
  (∑ i, entropyTerm bits (numerator i)) - entropyTerm bits (totalNumerator numerator)

/-- Rational lower endpoint for homogeneous entropy from pointwise logarithm endpoints. -/
def weightedEntropyLower [Fintype ι] (bits : ℕ) (numerator : ι → ℕ)
    (logUpper : ι → ℝ) (totalLogLower : ℝ) : ℝ :=
  entropyLower bits numerator logUpper -
    mass bits (totalNumerator numerator) * (bits - totalLogLower)

/-- Rational upper endpoint for homogeneous entropy from pointwise logarithm endpoints. -/
def weightedEntropyUpper [Fintype ι] (bits : ℕ) (numerator : ι → ℕ)
    (logLower : ι → ℝ) (totalLogUpper : ℝ) : ℝ :=
  entropyUpper bits numerator logLower -
    mass bits (totalNumerator numerator) * (bits - totalLogUpper)

/-- Pointwise logarithm certificates aggregate to a lower bound on a dyadic table's entropy. -/
theorem entropyLower_le [Fintype ι] (bits : ℕ) (numerator : ι → ℕ)
    (logUpper : ι → ℝ)
    (hlog : ∀ i, 0 < numerator i →
      Real.log (numerator i : ℝ) / Real.log 2 ≤ logUpper i) :
    entropyLower bits numerator logUpper ≤ ∑ i, entropyTerm bits (numerator i) := by
  unfold entropyLower
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : numerator i = 0
  · simp [hi, mass, entropyTerm_zero]
  · exact entropyTerm_lower_of_logUpper (Nat.pos_of_ne_zero hi) (hlog i (Nat.pos_of_ne_zero hi))

/-- Pointwise logarithm certificates aggregate to an upper bound on a dyadic table's entropy. -/
theorem le_entropyUpper [Fintype ι] (bits : ℕ) (numerator : ι → ℕ)
    (logLower : ι → ℝ)
    (hlog : ∀ i, 0 < numerator i →
      logLower i ≤ Real.log (numerator i : ℝ) / Real.log 2) :
    (∑ i, entropyTerm bits (numerator i)) ≤ entropyUpper bits numerator logLower := by
  unfold entropyUpper
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : numerator i = 0
  · simp [hi, mass, entropyTerm_zero]
  · exact entropyTerm_upper_of_logLower (Nat.pos_of_ne_zero hi) (hlog i (Nat.pos_of_ne_zero hi))

/-- Pointwise logarithm enclosures give a lower bound for homogeneous entropy. -/
theorem weightedEntropyLower_le [Fintype ι] (bits : ℕ) (numerator : ι → ℕ)
    (logUpper : ι → ℝ) (totalLogLower : ℝ)
    (hlogUpper : ∀ i, 0 < numerator i →
      Real.log (numerator i : ℝ) / Real.log 2 ≤ logUpper i)
    (htotalLower : 0 < totalNumerator numerator →
      totalLogLower ≤ Real.log (totalNumerator numerator : ℝ) / Real.log 2) :
    weightedEntropyLower bits numerator logUpper totalLogLower ≤
      weightedEntropy bits numerator := by
  exact sub_le_sub (entropyLower_le bits numerator logUpper hlogUpper)
    (entropyTerm_upper_of_logLower_or_zero htotalLower)

/-- Pointwise logarithm enclosures give an upper bound for homogeneous entropy. -/
theorem le_weightedEntropyUpper [Fintype ι] (bits : ℕ) (numerator : ι → ℕ)
    (logLower : ι → ℝ) (totalLogUpper : ℝ)
    (hlogLower : ∀ i, 0 < numerator i →
      logLower i ≤ Real.log (numerator i : ℝ) / Real.log 2)
    (htotalUpper : 0 < totalNumerator numerator →
      Real.log (totalNumerator numerator : ℝ) / Real.log 2 ≤ totalLogUpper) :
    weightedEntropy bits numerator ≤
      weightedEntropyUpper bits numerator logLower totalLogUpper := by
  exact sub_le_sub (le_entropyUpper bits numerator logLower hlogLower)
    (entropyTerm_lower_of_logUpper_or_zero htotalUpper)

/-- A generated scale function turns the analytic numerator bounds into an executable entropy
lower endpoint. -/
theorem entropyLower_numeratorLogUpper_le [Fintype ι]
    (bits steps : ℕ) (numerator scale : ι → ℕ)
    (hscale : ∀ i, 0 < numerator i → 2 ^ scale i ≤ numerator i) :
    entropyLower bits numerator (fun i ↦ numeratorLogUpper (numerator i) (scale i) steps) ≤
      ∑ i, entropyTerm bits (numerator i) := by
  apply entropyLower_le
  intro i hi
  exact le_numeratorLogUpper (hscale i hi)

/-- A generated scale function turns the analytic numerator bounds into an executable entropy
upper endpoint. -/
theorem le_entropyUpper_numeratorLogLower [Fintype ι]
    (bits steps : ℕ) (numerator scale : ι → ℕ)
    (hscale : ∀ i, 0 < numerator i → 2 ^ scale i ≤ numerator i) :
    (∑ i, entropyTerm bits (numerator i)) ≤
      entropyUpper bits numerator (fun i ↦ numeratorLogLower (numerator i) (scale i) steps) := by
  apply le_entropyUpper
  intro i hi
  exact numeratorLogLower_le (hscale i hi)

/-- Canonical executable lower entropy endpoint; no generated scale table is needed. -/
def certifiedEntropyLower [Fintype ι] (bits steps : ℕ) (numerator : ι → ℕ) : ℝ :=
  entropyLower bits numerator fun i ↦
    numeratorLogUpper (numerator i) (numeratorBinaryScale (numerator i)) steps

/-- Canonical executable upper entropy endpoint; no generated scale table is needed. -/
def certifiedEntropyUpper [Fintype ι] (bits steps : ℕ) (numerator : ι → ℕ) : ℝ :=
  entropyUpper bits numerator fun i ↦
    numeratorLogLower (numerator i) (numeratorBinaryScale (numerator i)) steps

theorem certifiedEntropyLower_le [Fintype ι]
    (bits steps : ℕ) (numerator : ι → ℕ) :
    certifiedEntropyLower bits steps numerator ≤
      ∑ i, entropyTerm bits (numerator i) := by
  apply entropyLower_numeratorLogUpper_le
  intro i hi
  exact pow_numeratorBinaryScale_le hi

theorem le_certifiedEntropyUpper [Fintype ι]
    (bits steps : ℕ) (numerator : ι → ℕ) :
    (∑ i, entropyTerm bits (numerator i)) ≤
      certifiedEntropyUpper bits steps numerator := by
  apply le_entropyUpper_numeratorLogLower
  intro i hi
  exact pow_numeratorBinaryScale_le hi

/-- Fully generated lower endpoint for homogeneous entropy. -/
theorem weightedEntropyLower_numeratorLogs_le [Fintype ι]
    (bits steps : ℕ) (numerator scale : ι → ℕ) (totalScale : ℕ)
    (hscale : ∀ i, 0 < numerator i → 2 ^ scale i ≤ numerator i)
    (htotalScale : 0 < totalNumerator numerator →
      2 ^ totalScale ≤ totalNumerator numerator) :
    weightedEntropyLower bits numerator
        (fun i ↦ numeratorLogUpper (numerator i) (scale i) steps)
        (numeratorLogLower (totalNumerator numerator) totalScale steps) ≤
      weightedEntropy bits numerator := by
  apply weightedEntropyLower_le
  · intro i hi
    exact le_numeratorLogUpper (hscale i hi)
  · intro htotal
    exact numeratorLogLower_le (htotalScale htotal)

/-- Fully generated upper endpoint for homogeneous entropy. -/
theorem le_weightedEntropyUpper_numeratorLogs [Fintype ι]
    (bits steps : ℕ) (numerator scale : ι → ℕ) (totalScale : ℕ)
    (hscale : ∀ i, 0 < numerator i → 2 ^ scale i ≤ numerator i)
    (htotalScale : 0 < totalNumerator numerator →
      2 ^ totalScale ≤ totalNumerator numerator) :
    weightedEntropy bits numerator ≤
      weightedEntropyUpper bits numerator
        (fun i ↦ numeratorLogLower (numerator i) (scale i) steps)
        (numeratorLogUpper (totalNumerator numerator) totalScale steps) := by
  apply le_weightedEntropyUpper
  · intro i hi
    exact numeratorLogLower_le (hscale i hi)
  · intro htotal
    exact le_numeratorLogUpper (htotalScale htotal)

/-- Canonical executable lower endpoint for homogeneous entropy. -/
def certifiedWeightedEntropyLower [Fintype ι]
    (bits steps : ℕ) (numerator : ι → ℕ) : ℝ :=
  weightedEntropyLower bits numerator
    (fun i ↦ numeratorLogUpper (numerator i) (numeratorBinaryScale (numerator i)) steps)
    (numeratorLogLower (totalNumerator numerator)
      (numeratorBinaryScale (totalNumerator numerator)) steps)

/-- Canonical executable upper endpoint for homogeneous entropy. -/
def certifiedWeightedEntropyUpper [Fintype ι]
    (bits steps : ℕ) (numerator : ι → ℕ) : ℝ :=
  weightedEntropyUpper bits numerator
    (fun i ↦ numeratorLogLower (numerator i) (numeratorBinaryScale (numerator i)) steps)
    (numeratorLogUpper (totalNumerator numerator)
      (numeratorBinaryScale (totalNumerator numerator)) steps)

theorem certifiedWeightedEntropyLower_le [Fintype ι]
    (bits steps : ℕ) (numerator : ι → ℕ) :
    certifiedWeightedEntropyLower bits steps numerator ≤ weightedEntropy bits numerator := by
  apply weightedEntropyLower_numeratorLogs_le
  · intro i hi
    exact pow_numeratorBinaryScale_le hi
  · intro hi
    exact pow_numeratorBinaryScale_le hi

theorem le_certifiedWeightedEntropyUpper [Fintype ι]
    (bits steps : ℕ) (numerator : ι → ℕ) :
    weightedEntropy bits numerator ≤ certifiedWeightedEntropyUpper bits steps numerator := by
  apply le_weightedEntropyUpper_numeratorLogs
  · intro i hi
    exact pow_numeratorBinaryScale_le hi
  · intro hi
    exact pow_numeratorBinaryScale_le hi

/-- The analytic summands above are exactly the Shannon entropy of a valid generated dyadic row.

This is the semantic adapter from `DyadicTable`, used by all level-four generated tables, to the
rational interval evaluator in this module. -/
theorem rowToRational_entropyBits_eq_sum_entropyTerm
    {Row : Type*} {width : Row → ℕ} {bits : ℕ}
    (table : DyadicTable Row width) (htable : table.IsProbability bits) (row : Row) :
    ((table.rowToRational bits row).toReal
      (table.rowToRational_isProbability htable row)).entropyBits =
      ∑ symbol, entropyTerm bits (table.numerator row symbol) := by
  unfold ProbabilityVector.entropyBits ProbabilityVector.entropy entropyTerm mass
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro symbol _
  congr 2
  norm_cast
  simp [DyadicTable.rowToRational, dyadicDenominator]

/-- A representation-independent version of the dyadic entropy adapter.  This covers generated
certificate schemas which predate `DyadicTable` but expose the same exact real weights. -/
theorem rationalProbability_entropyBits_eq_sum_entropyTerm
    {ι : Type*} [Fintype ι] {bits : ℕ}
    (data : RationalProbabilityData ι) (hdata : data.IsProbability)
    (numerator : ι → ℕ)
    (hweight : ∀ i, ((data.toReal hdata).weight i) = mass bits (numerator i)) :
    (data.toReal hdata).entropyBits = ∑ i, entropyTerm bits (numerator i) := by
  unfold ProbabilityVector.entropyBits ProbabilityVector.entropy entropyTerm
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ congrArg Real.negMulLog (hweight i)

end MatrixMultiplication.DyadicEntropy
