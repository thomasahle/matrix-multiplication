import AlgebraicComplexity.Tensor.OriginalCWNumerics

set_option linter.style.header false

/-!
# Exact probability data for the original Coppersmith--Winograd certificate

The tensor-square support has four permutation orbits of sizes `3,6,3,3`; the exceptional
`(2,1,1)` component has an inner four-point distribution with two points of each weight.  This file
checks the exact simplex constraints and positivity of the published rationalized parameters.
-/

namespace AlgebraicComplexity.OriginalCW

/-- Outer mass on each `(4,0,0)` permutation. -/
def a1 : ℚ := 23 / 100000

/-- Outer mass on each `(3,1,0)` permutation. -/
def a2 : ℚ := 1 / 80

/-- Outer mass on each `(2,2,0)` permutation. -/
def a3 : ℚ := 5127 / 50000

/-- Outer mass on each `(2,1,1)` permutation. -/
def a4 : ℚ := 61669 / 300000

/-- Inner mass on each of the two edge terms of the exceptional component. -/
def b1 : ℚ := 689 / 50000

/-- Inner mass on each of the two cross terms of the exceptional component. -/
def b2 : ℚ := 24311 / 50000

/-- The four outer orbit masses form a probability distribution after orbit multiplicities. -/
theorem outer_normalization :
    3 * a1 + 6 * a2 + 3 * a3 + 3 * a4 = 1 := by
  norm_num [a1, a2, a3, a4]

/-- The inner four-term masses form a probability distribution. -/
theorem inner_normalization : 2 * b1 + 2 * b2 = 1 := by
  norm_num [b1, b2]

/-- Every outer parameter is strictly positive. -/
theorem outer_positive : 0 < a1 ∧ 0 < a2 ∧ 0 < a3 ∧ 0 < a4 := by
  norm_num [a1, a2, a3, a4]

/-- Every inner parameter is strictly positive. -/
theorem inner_positive : 0 < b1 ∧ 0 < b2 := by
  norm_num [b1, b2]

/-- The exact rational parameters are all strictly smaller than one. -/
theorem parameters_lt_one :
    a1 < 1 ∧ a2 < 1 ∧ a3 < 1 ∧ a4 < 1 ∧ b1 < 1 ∧ b2 < 1 := by
  norm_num [a1, a2, a3, a4, b1, b2]

/-- Each coordinate has expected partition index `4/3` under the symmetric outer distribution. -/
theorem outer_coordinate_expectation :
    4 * a1 + 8 * a2 + 4 * a3 + 4 * a4 = 4 / 3 := by
  norm_num [a1, a2, a3, a4]

#print axioms outer_normalization
#print axioms inner_normalization
#print axioms outer_positive
#print axioms inner_positive
#print axioms outer_coordinate_expectation

end AlgebraicComplexity.OriginalCW
