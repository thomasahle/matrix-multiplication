import MatrixMultiplication.IntegerEntropyDualForm
import MatrixMultiplication.HomogeneousEntropyDual

/-!
# Homogeneous integer maximum-entropy dual forms

Recursive laser formulas apply a maximum-entropy penalty to rows whose total mass need not be
one.  The usual coordinate dual is therefore multiplied by the row mass.  This module gives that
homogeneous expression an exact signed-log form.

The construction is generic over the finite support and its three coordinate maps.  Positive
integer coordinate factors remain an untrusted optimization witness; the resulting form and its
real interpretation are exact.
-/

open scoped BigOperators

namespace MatrixMultiplication.HomogeneousIntegerEntropyDualForm

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.EntropyDual
open MatrixMultiplication.IntegerEntropyDual
open MatrixMultiplication.IntegerEntropyDualForm
open MatrixMultiplication.HomogeneousEntropyDual
open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

variable {A X Y Z : Type*}

/-! ## Executable list-oriented forms

The generic `Fintype` presentation below is convenient for semantic theorems, but its canonical
enumeration can contain `Classical.choice`.  Certificate clients instead carry an explicit list of
states.  The following equivalent presentation is therefore the preferred executable boundary:
the kernel only folds over data serialized in the certificate.
-/

/-- Total numerator over an explicitly serialized finite state space. -/
def totalNumeratorOn (states : List A) (numerator : A → ℕ) : ℕ :=
  (states.map numerator).sum

/-- Integer product-family partition over an explicitly serialized finite state space. -/
def integerPartitionNumeratorOn (states : List A)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : ℕ :=
  (states.map fun state ↦
    weightX (coordX state) * weightY (coordY state) * weightZ (coordZ state)).sum

/-- Exact homogeneous partition form over an explicit state list. -/
def homogeneousPartitionFormOn (states : List A) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : Form :=
  { constantNumerator := 0
    terms := [⟨integerPartitionNumeratorOn states coordX coordY coordZ
        weightX weightY weightZ, totalNumeratorOn states numerator⟩] }

/-- Exact logarithmic expectation form over an explicit state list. -/
def expectationFormOn (states : List A) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : Form :=
  Form.sum (states.map fun state ↦
    stateExpectationForm (numerator state)
      (weightX (coordX state)) (weightY (coordY state)) (weightZ (coordZ state)))

/-- Executable homogeneous integer dual over an explicit state list. -/
def homogeneousIntegerDualFormOn (states : List A) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : Form :=
  Form.add
    (homogeneousPartitionFormOn states numerator coordX coordY coordZ
      weightX weightY weightZ)
    (expectationFormOn states numerator coordX coordY coordZ weightX weightY weightZ)

/-- Real value represented by the explicit-list homogeneous dual. -/
def homogeneousIntegerDualBitsOn (bits : ℕ) (states : List A) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : ℝ :=
  mass bits (totalNumeratorOn states numerator) *
      (Real.log (integerPartitionNumeratorOn states coordX coordY coordZ
        weightX weightY weightZ : ℝ) / Real.log 2) -
    (states.map fun state ↦
      mass bits (numerator state) *
        (logIntegerPotential weightX (coordX state) +
          logIntegerPotential weightY (coordY state) +
          logIntegerPotential weightZ (coordZ state))).sum

theorem homogeneousPartitionFormOn_eval (bits : ℕ) (states : List A)
    (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    Form.eval bits
        (homogeneousPartitionFormOn states numerator coordX coordY coordZ
          weightX weightY weightZ) =
      mass bits (totalNumeratorOn states numerator) *
        (Real.log (integerPartitionNumeratorOn states coordX coordY coordZ
          weightX weightY weightZ : ℝ) / Real.log 2) := by
  unfold homogeneousPartitionFormOn Form.eval Form.termsValue Form.termValue
    SignedDyadicLogForm.log2Nat mass
  simp only [Int.cast_natCast, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  ring

theorem expectationFormOn_eval (bits : ℕ) (states : List A) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    Form.eval bits
        (expectationFormOn states numerator coordX coordY coordZ weightX weightY weightZ) =
      -(states.map fun state ↦
        mass bits (numerator state) *
          (logIntegerPotential weightX (coordX state) +
            logIntegerPotential weightY (coordY state) +
            logIntegerPotential weightZ (coordZ state))).sum := by
  rw [expectationFormOn, Form.eval_sum]
  induction states with
  | nil => simp
  | cons state states ih =>
      have hhead :
          Form.eval bits
              (stateExpectationForm (numerator state)
                (weightX (coordX state)) (weightY (coordY state))
                (weightZ (coordZ state))) =
            -(mass bits (numerator state) *
              (logIntegerPotential weightX (coordX state) +
                logIntegerPotential weightY (coordY state) +
                logIntegerPotential weightZ (coordZ state))) := by
        simpa [logIntegerPotential] using
          (stateExpectationForm_eval bits (numerator state)
            (weightX (coordX state)) (weightY (coordY state))
            (weightZ (coordZ state)))
      simp only [List.map_cons, List.sum_cons, hhead, ih]
      ring

/-- The executable list form has exactly its intended real dual value. -/
theorem homogeneousIntegerDualFormOn_eval (bits : ℕ) (states : List A)
    (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    Form.eval bits
        (homogeneousIntegerDualFormOn states numerator coordX coordY coordZ
          weightX weightY weightZ) =
      homogeneousIntegerDualBitsOn bits states numerator coordX coordY coordZ
        weightX weightY weightZ := by
  rw [homogeneousIntegerDualFormOn, Form.eval_add,
    homogeneousPartitionFormOn_eval, expectationFormOn_eval]
  rfl

/-- Total dyadic numerator of a finite reference row. -/
def totalNumerator [Fintype A] (numerator : A → ℕ) : ℕ :=
  ∑ state, numerator state

/-- Exact form for the partition term multiplied by the total reference mass. -/
def homogeneousPartitionForm [Fintype A]
    (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : Form :=
  { constantNumerator := 0
    terms := [⟨integerPartitionNumerator coordX coordY coordZ weightX weightY weightZ,
      totalNumerator numerator⟩] }

/-- Exact signed-log form for the homogeneous integer-coordinate dual. -/
def homogeneousIntegerDualForm [Fintype A]
    (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : Form :=
  Form.add
    (homogeneousPartitionForm numerator coordX coordY coordZ weightX weightY weightZ)
    (expectationForm numerator coordX coordY coordZ weightX weightY weightZ)

/-- Real homogeneous coordinate-dual expression for a dyadic reference row. -/
def homogeneousIntegerDualBits
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) : ℝ :=
  mass bits (totalNumerator numerator) *
      (Real.log (integerPartition coordX coordY coordZ weightX weightY weightZ) /
        Real.log 2) -
    ((∑ x, logIntegerPotential weightX x *
        marginal coordX (fun state ↦ mass bits (numerator state)) x) +
     (∑ y, logIntegerPotential weightY y *
        marginal coordY (fun state ↦ mass bits (numerator state)) y) +
     (∑ z, logIntegerPotential weightZ z *
        marginal coordZ (fun state ↦ mass bits (numerator state)) z))

theorem homogeneousPartitionForm_eval [Fintype A]
    (bits : ℕ) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    Form.eval bits
        (homogeneousPartitionForm numerator coordX coordY coordZ weightX weightY weightZ) =
      mass bits (totalNumerator numerator) *
        (Real.log (integerPartition coordX coordY coordZ weightX weightY weightZ) /
          Real.log 2) := by
  rw [integerPartition_eq_cast]
  unfold homogeneousPartitionForm Form.eval Form.termsValue Form.termValue
    SignedDyadicLogForm.log2Nat mass
  simp only [Int.cast_natCast, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  ring

/-- The homogeneous signed-log form has exactly the intended real coordinate-dual value. -/
theorem homogeneousIntegerDualForm_eval
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    Form.eval bits
        (homogeneousIntegerDualForm numerator coordX coordY coordZ
          weightX weightY weightZ) =
      homogeneousIntegerDualBits bits numerator coordX coordY coordZ
        weightX weightY weightZ := by
  rw [homogeneousIntegerDualForm, Form.eval_add,
    homogeneousPartitionForm_eval, expectationForm_eval]
  unfold homogeneousIntegerDualBits
  have hexpect := coordinateScore_expectation coordX coordY coordZ
    (fun state ↦ mass bits (numerator state))
    (logIntegerPotential weightX) (logIntegerPotential weightY)
    (logIntegerPotential weightZ)
  unfold coordinateScore at hexpect
  rw [← hexpect]
  ring

/-! ## Agreement with the semantic `Fintype` presentation

For a `Fin n` state space, `List.ofFn id` is the canonical computable enumeration.  These lemmas
close the adapter boundary: using the list-oriented evaluator does not change the mathematical
maximum-entropy dual.
-/

theorem totalNumeratorOn_fin {n : ℕ} (numerator : Fin n → ℕ) :
    totalNumeratorOn (List.ofFn id) numerator = totalNumerator numerator := by
  simp [totalNumeratorOn, totalNumerator, List.sum_ofFn]

theorem integerPartitionNumeratorOn_fin {n : ℕ}
    (coordX : Fin n → X) (coordY : Fin n → Y) (coordZ : Fin n → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    integerPartitionNumeratorOn (List.ofFn id) coordX coordY coordZ
        weightX weightY weightZ =
      integerPartitionNumerator coordX coordY coordZ weightX weightY weightZ := by
  simp [integerPartitionNumeratorOn, integerPartitionNumerator, List.sum_ofFn]

theorem homogeneousIntegerDualBitsOn_fin_eq
    {n : ℕ} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (numerator : Fin n → ℕ)
    (coordX : Fin n → X) (coordY : Fin n → Y) (coordZ : Fin n → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ) :
    homogeneousIntegerDualBitsOn bits (List.ofFn id) numerator coordX coordY coordZ
        weightX weightY weightZ =
      homogeneousIntegerDualBits bits numerator coordX coordY coordZ
        weightX weightY weightZ := by
  unfold homogeneousIntegerDualBitsOn homogeneousIntegerDualBits
  rw [totalNumeratorOn_fin, integerPartitionNumeratorOn_fin,
    ← integerPartition_eq_cast]
  have hexpect := coordinateScore_expectation coordX coordY coordZ
    (fun state ↦ mass bits (numerator state))
    (logIntegerPotential weightX) (logIntegerPotential weightY)
    (logIntegerPotential weightZ)
  unfold coordinateScore at hexpect
  rw [← hexpect]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, id_eq]

/-! ## Analytic soundness

The exact forms above are useful only after connecting their homogeneous dual value to the
maximum-entropy inequality.  The following results discharge that semantic obligation for every
positive-mass dyadic row. -/

theorem totalMass_dyadic [Fintype A] (bits : ℕ) (numerator : A → ℕ) :
    totalMass (fun state ↦ mass bits (numerator state)) =
      mass bits (totalNumerator numerator) := by
  unfold totalMass totalNumerator mass
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  push_cast
  rfl

/-- Taking a coordinate marginal commutes with interpreting integer numerators as dyadic
masses. -/
theorem marginal_dyadic
    [Fintype A] [Fintype X] [DecidableEq X]
    (bits : ℕ) (numerator : A → ℕ) (coordinate : A → X) (x : X) :
    marginal coordinate (fun state ↦ mass bits (numerator state)) x =
      mass bits (∑ state, if coordinate state = x then numerator state else 0) := by
  unfold marginal mass
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  split <;> simp_all

/-- The executable dyadic homogeneous entropy is the mathematical homogeneous entropy of the
represented finite mass row. -/
theorem weightedEntropy_dyadic_eq_homogeneousEntropyBits
    [Fintype A] (bits : ℕ) (numerator : A → ℕ) :
    weightedEntropy bits numerator =
      homogeneousEntropyBits (fun state ↦ mass bits (numerator state)) := by
  unfold weightedEntropy homogeneousEntropyBits homogeneousEntropy entropy entropyTerm
  rw [totalMass_dyadic]
  rw [← Finset.sum_div]
  simp only [DyadicEntropy.totalNumerator, totalNumerator]
  ring

/-- The integer homogeneous dual is exactly the generic homogeneous exponential-family dual. -/
theorem homogeneousIntegerDualBits_eq_homogeneousCoordinateDualBits
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    homogeneousIntegerDualBits bits numerator coordX coordY coordZ
        weightX weightY weightZ =
      homogeneousCoordinateDualBits coordX coordY coordZ
        (fun state ↦ mass bits (numerator state))
        (logIntegerPotential weightX) (logIntegerPotential weightY)
        (logIntegerPotential weightZ) := by
  unfold homogeneousIntegerDualBits homogeneousCoordinateDualBits
  rw [totalMass_dyadic,
    partitionTwo_logIntegerPotential coordX coordY coordZ weightX weightY weightZ
      hweightX hweightY hweightZ]

/-- Positive integer factors give a rigorous homogeneous maximum-entropy upper bound for every
positive-mass dyadic row. -/
theorem homogeneousEntropyBits_dyadic_le_homogeneousIntegerDualBits
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (hmass : 0 < mass bits (totalNumerator numerator))
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    homogeneousEntropyBits (fun state ↦ mass bits (numerator state)) ≤
      homogeneousIntegerDualBits bits numerator coordX coordY coordZ
        weightX weightY weightZ := by
  rw [homogeneousIntegerDualBits_eq_homogeneousCoordinateDualBits bits numerator
    coordX coordY coordZ weightX weightY weightZ hweightX hweightY hweightZ]
  apply homogeneousEntropyBits_le_coordinateDual
  · intro state
    unfold mass
    positivity
  · rw [totalMass_dyadic]
    exact hmass

/-- End-to-end homogeneous maximum-entropy certificate for a positive-mass dyadic reference
row.  This is the analytic soundness theorem consumed by recursive constituent checkers. -/
theorem maximumHomogeneousEntropyBits_dyadic_le_homogeneousIntegerDualBits
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (hmass : 0 < mass bits (totalNumerator numerator))
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    maximumHomogeneousEntropyBits coordX coordY coordZ
        (fun state ↦ mass bits (numerator state)) ≤
      homogeneousIntegerDualBits bits numerator coordX coordY coordZ
        weightX weightY weightZ := by
  rw [homogeneousIntegerDualBits_eq_homogeneousCoordinateDualBits bits numerator
    coordX coordY coordZ weightX weightY weightZ hweightX hweightY hweightZ]
  apply maximumHomogeneousEntropyBits_le_coordinateDual
  · intro state
    unfold mass
    positivity
  · rw [totalMass_dyadic]
    exact hmass

/-- Zero-safe end-to-end homogeneous maximum-entropy certificate. -/
theorem maximumHomogeneousEntropyBits_dyadic_le_homogeneousIntegerDualBits_of_nonnegative
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (numerator : A → ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (weightX : X → ℕ) (weightY : Y → ℕ) (weightZ : Z → ℕ)
    (hweightX : ∀ x, 0 < weightX x)
    (hweightY : ∀ y, 0 < weightY y)
    (hweightZ : ∀ z, 0 < weightZ z) :
    maximumHomogeneousEntropyBits coordX coordY coordZ
        (fun state ↦ mass bits (numerator state)) ≤
      homogeneousIntegerDualBits bits numerator coordX coordY coordZ
        weightX weightY weightZ := by
  rw [homogeneousIntegerDualBits_eq_homogeneousCoordinateDualBits bits numerator
    coordX coordY coordZ weightX weightY weightZ hweightX hweightY hweightZ]
  apply maximumHomogeneousEntropyBits_le_coordinateDual_of_nonnegative
  intro state
  unfold mass
  positivity

end

end MatrixMultiplication.HomogeneousIntegerEntropyDualForm
