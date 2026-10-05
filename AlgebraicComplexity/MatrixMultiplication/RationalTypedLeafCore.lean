/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IntegralProfileCounts
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafData

/-!
# Rational typed leaves: finite arithmetic core

This module records only exact integral profiles, coordinate labels, and multiplicative matrix
dimensions. Probability, entropy, optimization, and tensor extraction belong to higher adapter
modules. Semantic constituent assembly can therefore use the typed-leaf interface without loading
the real-analysis environment.
-/

open scoped BigOperators

namespace AlgebraicComplexity

open Tensor

universe u v

namespace RationalTypedLeaf

variable {I : Type u} [Fintype I] [Nonempty I]
variable {A : Leg → Type v}

/-- Exact finite product of one coordinate's matrix dimensions along the primitive profile. -/
def dimensionProduct (leaf : RationalTypedLeaf I A) (c : Leg) : ℕ :=
  ∏ i ∈ leaf.profile.alphabet,
    (leaf.dimension i c) ^ leaf.profile.count i

/-- A dimension product for the proportional profile `k ⋅ a` is the `k`th power of the
primitive profile's dimension product. -/
theorem prod_dimension_proportionalCounts
    (leaf : RationalTypedLeaf I A) (c : Leg) (k : ℕ) :
    (∏ i, leaf.dimension i c ^
      WordType.proportionalCounts leaf.profile.count k i) =
        leaf.dimensionProduct c ^ k := by
  rw [← leaf.profile.alphabet_eq_univ]
  simp only [WordType.proportionalCounts, dimensionProduct, pow_mul, Finset.prod_pow]

end RationalTypedLeaf

end AlgebraicComplexity
