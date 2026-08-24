import AlgebraicComplexity.Tensor.OriginalCWParameters
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The finite tight-support data in the original Coppersmith--Winograd certificate

The historical tensor-square analysis uses a symmetric probability distribution on the fifteen
triples `(i,j,k)` with `i+j+k=4`, grouped into the four permutation orbits represented by
`(4,0,0)`, `(3,1,0)`, `(2,2,0)`, and `(2,1,1)`. The exceptional `(2,1,1)` component has its own
four-point inner distribution. This file encodes those finite supports and kernel-checks their
normalizations and coordinate marginals.

We use explicit exhaustive sums rather than relying on generated `Fintype` enumeration order. This
keeps all rational reductions transparent to the kernel and gives later laser-score formulas a
stable normal form.
-/

namespace AlgebraicComplexity
namespace OriginalCW

/-- The fifteen labelled points of the tight support of `CW_q ⊠ CW_q`. -/
inductive OuterPoint
  | p400 | p040 | p004
  | p310 | p301 | p130 | p031 | p103 | p013
  | p220 | p202 | p022
  | p211 | p121 | p112
  deriving DecidableEq, Fintype, Repr

/-- Exhaustive sum over the fifteen outer support points. -/
def outerSum {M : Type*} [AddMonoid M] (f : OuterPoint → M) : M :=
  f .p400 + f .p040 + f .p004 +
  f .p310 + f .p301 + f .p130 + f .p031 + f .p103 + f .p013 +
  f .p220 + f .p202 + f .p022 +
  f .p211 + f .p121 + f .p112

/-- The three coordinate values attached to one outer support point. -/
def outerShape : OuterPoint → Fin 3 → ℕ
  | .p400 => ![4, 0, 0]
  | .p040 => ![0, 4, 0]
  | .p004 => ![0, 0, 4]
  | .p310 => ![3, 1, 0]
  | .p301 => ![3, 0, 1]
  | .p130 => ![1, 3, 0]
  | .p031 => ![0, 3, 1]
  | .p103 => ![1, 0, 3]
  | .p013 => ![0, 1, 3]
  | .p220 => ![2, 2, 0]
  | .p202 => ![2, 0, 2]
  | .p022 => ![0, 2, 2]
  | .p211 => ![2, 1, 1]
  | .p121 => ![1, 2, 1]
  | .p112 => ![1, 1, 2]

/-- Mass of an outer support point, constant on permutation orbits. -/
def outerMass : OuterPoint → ℚ
  | .p400 | .p040 | .p004 => a1
  | .p310 | .p301 | .p130 | .p031 | .p103 | .p013 => a2
  | .p220 | .p202 | .p022 => a3
  | .p211 | .p121 | .p112 => a4

/-- One coordinate marginal of the outer support distribution. -/
def outerMarginal (coordinate : Fin 3) (value : ℕ) : ℚ :=
  outerSum fun point =>
    if outerShape point coordinate = value then outerMass point else 0

/-- Every outer support point is tight of total degree four. -/
theorem outerShape_tight :
    ∀ point : OuterPoint, ∑ coordinate : Fin 3, outerShape point coordinate = 4 := by
  intro point
  cases point <;> decide

/-- The fifteen labelled masses form a probability distribution. -/
theorem outerMass_normalized : outerSum outerMass = 1 := by
  norm_num [outerSum, outerMass, a1, a2, a3, a4]

/-- All outer masses are strictly positive. -/
theorem outerMass_positive : ∀ point : OuterPoint, 0 < outerMass point := by
  intro point
  cases point <;> norm_num [outerMass, a1, a2, a3, a4]

/-- The probability of coordinate value zero is `16/125`, independently of the coordinate. -/
@[simp] theorem outerMarginal_zero (coordinate : Fin 3) :
    outerMarginal coordinate 0 = 16 / 125 := by
  fin_cases coordinate <;>
    norm_num [outerMarginal, outerSum, outerShape, outerMass, a1, a2, a3, a4]

/-- The probability of coordinate value one. -/
@[simp] theorem outerMarginal_one (coordinate : Fin 3) :
    outerMarginal coordinate 1 = 65419 / 150000 := by
  fin_cases coordinate <;>
    norm_num [outerMarginal, outerSum, outerShape, outerMass, a1, a2, a3, a4]

/-- The probability of coordinate value two. -/
@[simp] theorem outerMarginal_two (coordinate : Fin 3) :
    outerMarginal coordinate 2 = 123193 / 300000 := by
  fin_cases coordinate <;>
    norm_num [outerMarginal, outerSum, outerShape, outerMass, a1, a2, a3, a4]

/-- The probability of coordinate value three. -/
@[simp] theorem outerMarginal_three (coordinate : Fin 3) :
    outerMarginal coordinate 3 = 1 / 40 := by
  fin_cases coordinate <;>
    norm_num [outerMarginal, outerSum, outerShape, outerMass, a1, a2, a3, a4]

/-- The probability of coordinate value four. -/
@[simp] theorem outerMarginal_four (coordinate : Fin 3) :
    outerMarginal coordinate 4 = 23 / 100000 := by
  fin_cases coordinate <;>
    norm_num [outerMarginal, outerSum, outerShape, outerMass, a1, a2, a3, a4]

/-- No outer coordinate value above four occurs. -/
theorem outerMarginal_of_four_lt (coordinate : Fin 3) {value : ℕ} (h : 4 < value) :
    outerMarginal coordinate value = 0 := by
  have h0 : 0 ≠ value := by omega
  have h1 : 1 ≠ value := by omega
  have h2 : 2 ≠ value := by omega
  have h3 : 3 ≠ value := by omega
  have h4 : 4 ≠ value := by omega
  fin_cases coordinate <;>
    simp [outerMarginal, outerSum, outerShape, h0, h1, h2, h3, h4]

/-- The five displayed marginal probabilities sum to one. -/
theorem outerMarginal_normalized (coordinate : Fin 3) :
    outerMarginal coordinate 0 + outerMarginal coordinate 1 +
      outerMarginal coordinate 2 + outerMarginal coordinate 3 +
      outerMarginal coordinate 4 = 1 := by
  rw [outerMarginal_zero, outerMarginal_one, outerMarginal_two,
    outerMarginal_three, outerMarginal_four]
  norm_num

/-- The four labelled summands inside the exceptional `(2,1,1)` component. -/
inductive InnerPoint
  | edgeLeft
  | crossLeft
  | crossRight
  | edgeRight
  deriving DecidableEq, Fintype, Repr

/-- Exhaustive sum over the four inner support points. -/
def innerSum {M : Type*} [AddMonoid M] (f : InnerPoint → M) : M :=
  f .edgeLeft + f .crossLeft + f .crossRight + f .edgeRight

/-- The ordered constituent split represented by an inner support point. -/
def innerShape : InnerPoint → Fin 3 → ℕ
  | .edgeLeft => ![2, 0, 0]
  | .crossLeft => ![1, 1, 0]
  | .crossRight => ![1, 0, 1]
  | .edgeRight => ![0, 1, 1]

/-- Inner mass: the two edge terms have mass `b1`, the two crossing terms mass `b2`. -/
def innerMass : InnerPoint → ℚ
  | .edgeLeft | .edgeRight => b1
  | .crossLeft | .crossRight => b2

/-- One coordinate marginal of the inner distribution. -/
def innerMarginal (coordinate : Fin 3) (value : ℕ) : ℚ :=
  innerSum fun point =>
    if innerShape point coordinate = value then innerMass point else 0

/-- Every inner support point has total degree two. -/
theorem innerShape_tight :
    ∀ point : InnerPoint, ∑ coordinate : Fin 3, innerShape point coordinate = 2 := by
  intro point
  cases point <;> decide

/-- The four inner masses form a probability distribution. -/
theorem innerMass_normalized : innerSum innerMass = 1 := by
  norm_num [innerSum, innerMass, b1, b2]

/-- All inner masses are strictly positive. -/
theorem innerMass_positive : ∀ point : InnerPoint, 0 < innerMass point := by
  intro point
  cases point <;> norm_num [innerMass, b1, b2]

/-- The first-coordinate inner marginal is `(b1, 2*b2, b1)`. -/
@[simp] theorem innerMarginal_x_zero : innerMarginal 0 0 = b1 := by
  norm_num [innerMarginal, innerSum, innerShape, innerMass, b1, b2]

@[simp] theorem innerMarginal_x_one : innerMarginal 0 1 = 2 * b2 := by
  norm_num [innerMarginal, innerSum, innerShape, innerMass, b1, b2]

@[simp] theorem innerMarginal_x_two : innerMarginal 0 2 = b1 := by
  norm_num [innerMarginal, innerSum, innerShape, innerMass, b1, b2]

/-- The other two coordinate marginals are uniform binary distributions. -/
@[simp] theorem innerMarginal_y_zero : innerMarginal 1 0 = 1 / 2 := by
  norm_num [innerMarginal, innerSum, innerShape, innerMass, b1, b2]

@[simp] theorem innerMarginal_y_one : innerMarginal 1 1 = 1 / 2 := by
  norm_num [innerMarginal, innerSum, innerShape, innerMass, b1, b2]

@[simp] theorem innerMarginal_z_zero : innerMarginal 2 0 = 1 / 2 := by
  change (((b1 + b2) + 0) + 0 : ℚ) = 1 / 2
  norm_num [b1, b2]

@[simp] theorem innerMarginal_z_one : innerMarginal 2 1 = 1 / 2 := by
  change (((0 + 0) + b2) + b1 : ℚ) = 1 / 2
  norm_num [b1, b2]

/-- The inner first-coordinate marginal sums to one. -/
theorem innerMarginal_x_normalized :
    innerMarginal 0 0 + innerMarginal 0 1 + innerMarginal 0 2 = 1 := by
  rw [innerMarginal_x_zero, innerMarginal_x_one, innerMarginal_x_two]
  norm_num [b1, b2]

/-- The binary inner marginals sum to one. -/
theorem innerMarginal_y_normalized : innerMarginal 1 0 + innerMarginal 1 1 = 1 := by
  rw [innerMarginal_y_zero, innerMarginal_y_one]
  norm_num

theorem innerMarginal_z_normalized : innerMarginal 2 0 + innerMarginal 2 1 = 1 := by
  rw [innerMarginal_z_zero, innerMarginal_z_one]
  norm_num

#print axioms outerShape_tight
#print axioms outerMass_normalized
#print axioms outerMarginal_zero
#print axioms outerMarginal_normalized
#print axioms innerShape_tight
#print axioms innerMass_normalized
#print axioms innerMarginal_x_normalized

end OriginalCW
end AlgebraicComplexity
