/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymptoticSumDefs
import AlgebraicComplexity.MatrixMultiplication.DirectSum
import AlgebraicComplexity.Tensor.Degeneration
import AlgebraicComplexity.Tensor.Power

/-!
# The semantic laser-extraction rate

This lightweight module defines the output relation shared by laser-method counting arguments.
It records that powers of a source tensor polynomially degenerate to finite direct sums whose
numerical asymptotic-sum expression has a prescribed logarithmic growth rate.

The analytic theorem bounding this rate by border rank remains in
`MatrixMultiplication/Laser.lean`.  Keeping the relation in a separate leaf allows combinatorial
and cyclic extraction clients to expose certificates without importing the full proof of
Schönhage's asymptotic sum inequality.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- A tensor achieves a logarithmic laser value when, up to an arbitrarily small loss per tensor
power, some finite nonuniform direct sum extracted from that power has at least that logarithmic
asymptotic-sum value.  This is the semantic output expected from a hashing/typical-sequence
argument; it deliberately contains no reference to a particular support or optimizer. -/
def HasLaserExtractionRate (T : Tensor3 K V) (value : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (k L : ℕ) (m n p : Fin L → ℕ),
      0 < k ∧
        (∀ i, 0 < m i) ∧ (∀ i, 0 < n i) ∧ (∀ i, 0 < p i) ∧
        PolynomialDegenerates (Tensor.power T k)
          (matrixMultiplicationDirectSum K m n p) ∧
        0 < asymptoticSum K m n p ∧
        (k : ℝ) * (value - ε) ≤ Real.log (asymptoticSum K m n p)

end AlgebraicComplexity
