import AlgebraicComplexity.Probability.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Scalar form of the three-coordinate volume recurrence

The recursive evaluator records three matrix-size coordinates and takes their arithmetic mean in
the rectangular-volume assembly.  At level two, every positive constituent has one heavy
coordinate and two light coordinates; every zero constituent contributes its whole scalar size
to one coordinate.  Consequently the arithmetic mean is independent of all orientation labels.

The lemmas here collapse the coordinate-valued recurrence to one scalar sum before any generated
certificate arithmetic is performed.  This removes every repeated-orientation permutation from
the volume checker and reduces its exact workload by roughly a factor of three.
-/

open scoped BigOperators

namespace MatrixMultiplication.VolumeRecurrence

noncomputable section

/-- Arithmetic mean of the three rectangular matrix-size coordinates. -/
def threeCoordinateMean (value : Fin 3 → ℝ) : ℝ :=
  (∑ coordinate, value coordinate) / 3

/-- A scalar contribution placed in exactly one matrix coordinate. -/
def singleCoordinate (chosen : Fin 3) (value : ℝ) (coordinate : Fin 3) : ℝ :=
  if coordinate = chosen then value else 0

/-- Level-two positive constituent: one heavy coordinate receives `2μ log₂ q`, while each of
the other two receives `(1 - 2μ) log₂ q`. -/
def positiveEdgeCoordinates
    (heavy : Fin 3) (mu logQ : ℝ) (coordinate : Fin 3) : ℝ :=
  if coordinate = heavy then 2 * mu * logQ else (1 - 2 * mu) * logQ

theorem sum_fin_three (value : Fin 3 → ℝ) :
    (∑ coordinate, value coordinate) = value 0 + value 1 + value 2 := by
  simp [Fin.sum_univ_succ, add_assoc]

/-- The location of a one-coordinate contribution disappears after summing coordinates. -/
@[simp] theorem sum_singleCoordinate (chosen : Fin 3) (value : ℝ) :
    (∑ coordinate, singleCoordinate chosen value coordinate) = value := by
  fin_cases chosen <;> simp [singleCoordinate]

/-- The sum of one heavy and two light contributions is `(2 - 2μ) log₂ q`, independently of
which coordinate is heavy. -/
theorem sum_positiveEdgeCoordinates (heavy : Fin 3) (mu logQ : ℝ) :
    (∑ coordinate, positiveEdgeCoordinates heavy mu logQ coordinate) =
      (2 - 2 * mu) * logQ := by
  fin_cases heavy <;> simp [sum_fin_three, positiveEdgeCoordinates] <;> ring

@[simp] theorem mean_singleCoordinate (chosen : Fin 3) (value : ℝ) :
    threeCoordinateMean (singleCoordinate chosen value) = value / 3 := by
  simp [threeCoordinateMean]

theorem mean_positiveEdgeCoordinates (heavy : Fin 3) (mu logQ : ℝ) :
    threeCoordinateMean (positiveEdgeCoordinates heavy mu logQ) =
      ((2 - 2 * mu) * logQ) / 3 := by
  rw [threeCoordinateMean, sum_positiveEdgeCoordinates]

/-- Coordinate-valued level-two matrix-size total for an arbitrary finite family of edges. -/
def edgeCoordinateTotal
    {Edge : Type*} [Fintype Edge]
    (mass : Edge → ℝ) (isPositive : Edge → Prop) [DecidablePred isPositive]
    (heavy zeroCoordinate : Edge → Fin 3)
    (mu zeroValue : Edge → ℝ) (logQ : ℝ) (coordinate : Fin 3) : ℝ :=
  ∑ edge, mass edge *
    if isPositive edge then
      positiveEdgeCoordinates (heavy edge) (mu edge) logQ coordinate
    else
      singleCoordinate (zeroCoordinate edge) (zeroValue edge) coordinate

/-- Scalar numerator of the arithmetic-mean level-two volume. -/
def edgeVolumeNumerator
    {Edge : Type*} [Fintype Edge]
    (mass : Edge → ℝ) (isPositive : Edge → Prop) [DecidablePred isPositive]
    (mu zeroValue : Edge → ℝ) (logQ : ℝ) : ℝ :=
  ∑ edge, mass edge *
    if isPositive edge then (2 - 2 * mu edge) * logQ else zeroValue edge

/-- **Orientation-free level-two volume recurrence.**  The arithmetic mean of the three exact
coordinate totals is the scalar contribution formula; neither the heavy-coordinate assignment
nor the zero-coordinate assignment remains. -/
theorem threeCoordinateMean_edgeCoordinateTotal
    {Edge : Type*} [Fintype Edge]
    (mass : Edge → ℝ) (isPositive : Edge → Prop) [DecidablePred isPositive]
    (heavy zeroCoordinate : Edge → Fin 3)
    (mu zeroValue : Edge → ℝ) (logQ : ℝ) :
    threeCoordinateMean
        (edgeCoordinateTotal mass isPositive heavy zeroCoordinate mu zeroValue logQ) =
      edgeVolumeNumerator mass isPositive mu zeroValue logQ / 3 := by
  unfold threeCoordinateMean edgeCoordinateTotal edgeVolumeNumerator
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro edge _
  by_cases hedge : isPositive edge
  · simp only [hedge, if_true, ← Finset.mul_sum]
    rw [sum_positiveEdgeCoordinates]
  · simp only [hedge, if_false, ← Finset.mul_sum, sum_singleCoordinate]

/-- Coordinate-valued total for constituents whose scalar size is placed on one coordinate. -/
def zeroCoordinateTotal
    {Node : Type*} [Fintype Node]
    (mass value : Node → ℝ) (coordinateOf : Node → Fin 3)
    (coordinate : Fin 3) : ℝ :=
  ∑ node, mass node * singleCoordinate (coordinateOf node) (value node) coordinate

/-- The corresponding orientation-free scalar numerator. -/
def zeroVolumeNumerator
    {Node : Type*} [Fintype Node]
    (mass value : Node → ℝ) : ℝ :=
  ∑ node, mass node * value node

/-- **Orientation-free zero-family volume recurrence.** -/
theorem threeCoordinateMean_zeroCoordinateTotal
    {Node : Type*} [Fintype Node]
    (mass value : Node → ℝ) (coordinateOf : Node → Fin 3) :
    threeCoordinateMean (zeroCoordinateTotal mass value coordinateOf) =
      zeroVolumeNumerator mass value / 3 := by
  unfold threeCoordinateMean zeroCoordinateTotal zeroVolumeNumerator
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro node _
  rw [← Finset.mul_sum, sum_singleCoordinate]

end

end MatrixMultiplication.VolumeRecurrence
