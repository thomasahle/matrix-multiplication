import MatrixMultiplication.DyadicEntropy
import MatrixMultiplication.EntropyDual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integer product-family certificates for maximum entropy

The usual numerical dual certificate stores real coordinate potentials and evaluates an
exponential partition function.  For formal verification that representation is unnecessarily
expensive.  Positive integer coordinate factors give the same class of certificates: on a finite
structural support define

`q(a) = rX(x(a)) * rY(y(a)) * rZ(z(a)) / Z`.

Its logarithm is coordinate-additive, so it upper-bounds maximum entropy with the same Gibbs
argument.  The resulting dual expression contains only logarithms of positive integers.  It can
therefore be certified by the rational atanh evaluator in `MatrixMultiplication.DyadicEntropy`,
without formalizing IEEE-754 decoding or exponential-function interval arithmetic.
-/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.IntegerEntropyDual

open MatrixMultiplication.EntropyDual
open MatrixMultiplication.DyadicEntropy

variable {A X Y Z : Type*}

/-- Base-two potential represented by one positive integer factor. -/
def logIntegerPotential (weight : X → ℕ) (x : X) : ℝ :=
  Real.log (weight x : ℝ) / Real.log 2

/-- Exact real partition sum of a coordinatewise integer product family. -/
def integerPartition [Fintype A]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : ℝ :=
  ∑ a, (weightX (coordX a) : ℝ) *
    (weightY (coordY a) : ℝ) * (weightZ (coordZ a) : ℝ)

/-- Natural-number form of the same partition sum, used by the rational logarithm evaluator. -/
def integerPartitionNumerator [Fintype A]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : ℕ :=
  ∑ a, weightX (coordX a) * weightY (coordY a) * weightZ (coordZ a)

theorem integerPartition_eq_cast [Fintype A]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    integerPartition coordX coordY coordZ weightX weightY weightZ =
      (integerPartitionNumerator coordX coordY coordZ weightX weightY weightZ : ℝ) := by
  unfold integerPartition integerPartitionNumerator
  push_cast
  rfl

/-- Maximum-entropy dual expression associated to positive integer coordinate factors. -/
def integerCoordinateDualBits
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : ℝ :=
  Real.log (integerPartition coordX coordY coordZ weightX weightY weightZ) / Real.log 2 -
    ((∑ x, logIntegerPotential weightX x * marginal coordX reference x) +
     (∑ y, logIntegerPotential weightY y * marginal coordY reference y) +
     (∑ z, logIntegerPotential weightZ z * marginal coordZ reference z))

/-- Canonical rational lower endpoint for the base-two logarithm of a positive integer. -/
def certifiedLogIntegerLower (steps numerator : ℕ) : ℝ :=
  numeratorLogLower numerator (numeratorBinaryScale numerator) steps

/-- Canonical rational upper endpoint for the base-two logarithm of a positive integer. -/
def certifiedLogIntegerUpper (steps numerator : ℕ) : ℝ :=
  numeratorLogUpper numerator (numeratorBinaryScale numerator) steps

theorem certifiedLogIntegerLower_le {steps numerator : ℕ} (hnumerator : 0 < numerator) :
    certifiedLogIntegerLower steps numerator ≤
      Real.log (numerator : ℝ) / Real.log 2 := by
  exact numeratorLogLower_le (pow_numeratorBinaryScale_le hnumerator)

theorem le_certifiedLogIntegerUpper {steps numerator : ℕ} (hnumerator : 0 < numerator) :
    Real.log (numerator : ℝ) / Real.log 2 ≤
      certifiedLogIntegerUpper steps numerator := by
  exact le_numeratorLogUpper (pow_numeratorBinaryScale_le hnumerator)

/-- Fully rational upper endpoint for an integer product-family dual. -/
def certifiedIntegerCoordinateDualUpper
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (steps : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : ℝ :=
  certifiedLogIntegerUpper steps
      (integerPartitionNumerator coordX coordY coordZ weightX weightY weightZ) -
    ((∑ x, certifiedLogIntegerLower steps (weightX x) * marginal coordX reference x) +
     (∑ y, certifiedLogIntegerLower steps (weightY y) * marginal coordY reference y) +
     (∑ z, certifiedLogIntegerLower steps (weightZ z) * marginal coordZ reference z))

/-- Exponentiating the logarithmic integer potentials reconstructs the exact integer product
partition. -/
theorem partitionTwo_logIntegerPotential
    [Fintype A]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    partitionTwo (coordinateScore coordX coordY coordZ
      (logIntegerPotential weightX) (logIntegerPotential weightY)
      (logIntegerPotential weightZ)) =
      integerPartition coordX coordY coordZ weightX weightY weightZ := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold partitionTwo partition coordinateScore integerPartition logIntegerPotential
  apply Finset.sum_congr rfl
  intro a _
  have hx : 0 < (weightX (coordX a) : ℝ) := by exact_mod_cast hweightX (coordX a)
  have hy : 0 < (weightY (coordY a) : ℝ) := by exact_mod_cast hweightY (coordY a)
  have hz : 0 < (weightZ (coordZ a) : ℝ) := by exact_mod_cast hweightZ (coordZ a)
  have hscore :
      Real.log 2 *
          (Real.log (weightX (coordX a) : ℝ) / Real.log 2 +
            Real.log (weightY (coordY a) : ℝ) / Real.log 2 +
            Real.log (weightZ (coordZ a) : ℝ) / Real.log 2) =
        Real.log (weightX (coordX a) : ℝ) +
          Real.log (weightY (coordY a) : ℝ) +
          Real.log (weightZ (coordZ a) : ℝ) := by
    field_simp [hlogTwo]
  change Real.exp
      (Real.log 2 *
        (Real.log (weightX (coordX a) : ℝ) / Real.log 2 +
          Real.log (weightY (coordY a) : ℝ) / Real.log 2 +
          Real.log (weightZ (coordZ a) : ℝ) / Real.log 2)) = _
  rw [hscore, ← Real.log_mul hx.ne' hy.ne',
    ← Real.log_mul (mul_ne_zero hx.ne' hy.ne') hz.ne', Real.exp_log]
  positivity

theorem integerPartitionNumerator_pos
    [Fintype A] [Nonempty A]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    0 < integerPartitionNumerator coordX coordY coordZ weightX weightY weightZ := by
  unfold integerPartitionNumerator
  exact Finset.sum_pos
    (fun a _ ↦ Nat.mul_pos (Nat.mul_pos (hweightX _) (hweightY _)) (hweightZ _))
    Finset.univ_nonempty

private theorem marginal_nonneg
    [Fintype A] [Fintype X] [DecidableEq X]
    (coordX : A → X) (reference : A → ℝ)
    (href : ∀ a, 0 ≤ reference a) (x : X) :
    0 ≤ marginal coordX reference x := by
  unfold marginal
  exact Finset.sum_nonneg fun a _ ↦ by
    by_cases h : coordX a = x
    · simpa [h] using href a
    · simp [h]

/-- Soundness of the completely rational upper endpoint.  This is the numerical-checker boundary:
after choosing positive integer factors, only exact finite sums and the atanh log series remain. -/
theorem integerCoordinateDualBits_le_certifiedUpper
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (steps : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (href : IsProbability reference)
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    integerCoordinateDualBits coordX coordY coordZ reference weightX weightY weightZ ≤
      certifiedIntegerCoordinateDualUpper steps coordX coordY coordZ reference
        weightX weightY weightZ := by
  let partitionNumerator :=
    integerPartitionNumerator coordX coordY coordZ weightX weightY weightZ
  have hpartitionNumerator : 0 < partitionNumerator :=
    integerPartitionNumerator_pos coordX coordY coordZ weightX weightY weightZ
      hweightX hweightY hweightZ
  have hpartition :
      Real.log (integerPartition coordX coordY coordZ weightX weightY weightZ) /
          Real.log 2 ≤ certifiedLogIntegerUpper steps partitionNumerator := by
    rw [integerPartition_eq_cast]
    exact le_certifiedLogIntegerUpper hpartitionNumerator
  have hX :
      (∑ x, certifiedLogIntegerLower steps (weightX x) * marginal coordX reference x) ≤
        ∑ x, logIntegerPotential weightX x * marginal coordX reference x := by
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_right (certifiedLogIntegerLower_le (hweightX x))
      (marginal_nonneg coordX reference href.1 x)
  have hY :
      (∑ y, certifiedLogIntegerLower steps (weightY y) * marginal coordY reference y) ≤
        ∑ y, logIntegerPotential weightY y * marginal coordY reference y := by
    apply Finset.sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_right (certifiedLogIntegerLower_le (hweightY y))
      (marginal_nonneg coordY reference href.1 y)
  have hZ :
      (∑ z, certifiedLogIntegerLower steps (weightZ z) * marginal coordZ reference z) ≤
        ∑ z, logIntegerPotential weightZ z * marginal coordZ reference z := by
    apply Finset.sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_right (certifiedLogIntegerLower_le (hweightZ z))
      (marginal_nonneg coordZ reference href.1 z)
  unfold integerCoordinateDualBits certifiedIntegerCoordinateDualUpper
  dsimp only [partitionNumerator] at hpartition
  linarith

/-- The integer-product expression is definitionally the ordinary exponential-family dual after
the partition sum is simplified. -/
theorem coordinateDualBits_logIntegerPotential_eq
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    coordinateDualBits coordX coordY coordZ reference
        (logIntegerPotential weightX) (logIntegerPotential weightY)
        (logIntegerPotential weightZ) =
      integerCoordinateDualBits coordX coordY coordZ reference weightX weightY weightZ := by
  unfold coordinateDualBits integerCoordinateDualBits
  rw [partitionTwo_logIntegerPotential coordX coordY coordZ weightX weightY weightZ
    hweightX hweightY hweightZ]

/-- **Integer product-family maximum-entropy certificate.**  Any positive integer coordinate
factors give a rigorous upper bound, with no optimization or convergence hypothesis. -/
theorem maximumEntropyBits_le_integerCoordinateDual
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (href : IsProbability reference)
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    maximumEntropyBits coordX coordY coordZ reference ≤
      integerCoordinateDualBits coordX coordY coordZ reference weightX weightY weightZ := by
  exact (maximumEntropyBits_le_coordinateDual coordX coordY coordZ reference
    (logIntegerPotential weightX) (logIntegerPotential weightY)
    (logIntegerPotential weightZ) href).trans_eq
      (coordinateDualBits_logIntegerPotential_eq coordX coordY coordZ reference
        weightX weightY weightZ hweightX hweightY hweightZ)

/-- End-to-end rational maximum-entropy dual bound. -/
theorem maximumEntropyBits_le_certifiedIntegerDualUpper
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (steps : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (href : IsProbability reference)
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    maximumEntropyBits coordX coordY coordZ reference ≤
      certifiedIntegerCoordinateDualUpper steps coordX coordY coordZ reference
        weightX weightY weightZ :=
  (maximumEntropyBits_le_integerCoordinateDual coordX coordY coordZ reference
    weightX weightY weightZ href hweightX hweightY hweightZ).trans
      (integerCoordinateDualBits_le_certifiedUpper steps coordX coordY coordZ reference
        weightX weightY weightZ href hweightX hweightY hweightZ)

/-- Integer factors also directly certify the combination-loss gap used by the recursive
constituent theorem. -/
theorem combinationLossBits_le_integerDualGap
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (href : IsProbability reference)
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    combinationLossBits coordX coordY coordZ reference ≤
      integerCoordinateDualBits coordX coordY coordZ reference weightX weightY weightZ -
        entropyBits reference := by
  exact sub_le_sub_right
    (maximumEntropyBits_le_integerCoordinateDual coordX coordY coordZ reference
      weightX weightY weightZ href hweightX hweightY hweightZ) _

/-- End-to-end rational combination-loss certificate. -/
theorem combinationLossBits_le_certifiedIntegerDualGap
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (steps : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (href : IsProbability reference)
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    combinationLossBits coordX coordY coordZ reference ≤
      certifiedIntegerCoordinateDualUpper steps coordX coordY coordZ reference
          weightX weightY weightZ - entropyBits reference := by
  exact sub_le_sub_right
    (maximumEntropyBits_le_certifiedIntegerDualUpper steps coordX coordY coordZ reference
      weightX weightY weightZ href hweightX hweightY hweightZ) _

end MatrixMultiplication.IntegerEntropyDual
