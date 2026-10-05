import MatrixMultiplication.IntegerEntropyDual
import MatrixMultiplication.SignedDyadicLogForm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact signed-log forms for integer maximum-entropy duals

Positive integer coordinate factors turn a maximum-entropy dual into one partition logarithm
minus three finite logarithmic expectations.  This module records that expression directly as a
`SignedDyadicLogForm.Form` and proves exact agreement with `integerCoordinateDualBits`.

The result is the bridge needed by generated recursive-constituent checkers: choosing the integer
factors is untrusted optimization, while evaluating the resulting dual is exact kernel arithmetic.
-/

open scoped BigOperators

namespace MatrixMultiplication.IntegerEntropyDualForm

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.EntropyDual
open MatrixMultiplication.IntegerEntropyDual
open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

variable {A X Y Z : Type*}

def partitionForm [Fintype A]
    (bits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : Form :=
  { constantNumerator := 0
    terms := [⟨integerPartitionNumerator coordX coordY coordZ weightX weightY weightZ,
      (2 ^ bits : ℕ)⟩] }

def stateExpectationForm (numerator : ℕ) (weightX weightY weightZ : ℕ) : Form :=
  { constantNumerator := 0
    terms := [⟨weightX, -(numerator : ℤ)⟩,
      ⟨weightY, -(numerator : ℤ)⟩,
      ⟨weightZ, -(numerator : ℤ)⟩] }

def expectationForm [Fintype A]
    (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : Form :=
  Form.sum ((Finset.univ : Finset A).toList.map fun state =>
    stateExpectationForm (numerator state)
      (weightX (coordX state)) (weightY (coordY state)) (weightZ (coordZ state)))

/-- Exact form of an integer-coordinate maximum-entropy dual at dyadic denominator `2^bits`. -/
def integerDualForm [Fintype A]
    (bits : ℕ) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : Form :=
  Form.add (partitionForm bits coordX coordY coordZ weightX weightY weightZ)
    (expectationForm numerator coordX coordY coordZ weightX weightY weightZ)

theorem partitionForm_eval [Fintype A]
    (bits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    Form.eval bits (partitionForm bits coordX coordY coordZ weightX weightY weightZ) =
      Real.log (integerPartition coordX coordY coordZ weightX weightY weightZ) /
        Real.log 2 := by
  rw [integerPartition_eq_cast]
  unfold partitionForm Form.eval Form.termsValue Form.termValue
    SignedDyadicLogForm.log2Nat
  simp only [Int.cast_natCast, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  have hpow : (2 : ℝ) ^ bits ≠ 0 := by positivity
  field_simp
  norm_num

theorem stateExpectationForm_eval (bits numerator weightX weightY weightZ : ℕ) :
    Form.eval bits (stateExpectationForm numerator weightX weightY weightZ) =
      -(mass bits numerator *
        (logIntegerPotential (fun _ : Unit => weightX) () +
          logIntegerPotential (fun _ : Unit => weightY) () +
          logIntegerPotential (fun _ : Unit => weightZ) ())) := by
  unfold stateExpectationForm Form.eval Form.termsValue Form.termValue
    SignedDyadicLogForm.log2Nat logIntegerPotential mass
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Int.cast_neg, Int.cast_natCast, Int.cast_zero]
  ring

theorem expectationForm_eval [Fintype A]
    (bits : ℕ) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    Form.eval bits
        (expectationForm numerator coordX coordY coordZ weightX weightY weightZ) =
      -∑ state, mass bits (numerator state) *
        (logIntegerPotential weightX (coordX state) +
          logIntegerPotential weightY (coordY state) +
          logIntegerPotential weightZ (coordZ state)) := by
  rw [expectationForm, Form.eval_sum, List.map_map, Finset.sum_map_toList,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro state _
  change Form.eval bits
      (stateExpectationForm (numerator state) (weightX (coordX state))
        (weightY (coordY state)) (weightZ (coordZ state))) = _
  rw [stateExpectationForm_eval]
  rfl

/-- Evaluating the exact integer form gives precisely the analytic integer-coordinate dual. -/
theorem integerDualForm_eval
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    Form.eval bits
        (integerDualForm bits numerator coordX coordY coordZ weightX weightY weightZ) =
      integerCoordinateDualBits coordX coordY coordZ
        (fun state => mass bits (numerator state)) weightX weightY weightZ := by
  rw [integerDualForm, Form.eval_add, partitionForm_eval, expectationForm_eval]
  unfold integerCoordinateDualBits
  have hexpect := coordinateScore_expectation coordX coordY coordZ
    (fun state => mass bits (numerator state))
    (logIntegerPotential weightX) (logIntegerPotential weightY)
    (logIntegerPotential weightZ)
  unfold coordinateScore at hexpect
  rw [← hexpect]
  ring

end

end MatrixMultiplication.IntegerEntropyDualForm
