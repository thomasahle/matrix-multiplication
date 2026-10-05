/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PositiveWordProductCore
import AlgebraicComplexity.Tensor.PositiveWord
import Mathlib.Algebra.BigOperators.Fin

/-!
# Numerical products along positive tensor words

The recursive definition, simplification laws, and positivity theorem live in the dependency-light
`PositiveWordProductCore`.  This module adds only the equivalence with a product over the function
representation, which requires Mathlib's finite big-operator API.  The stronger statement that
the product depends only on a multiplicity type remains in `MatrixMultiplication.TypeExtraction`,
where the type-class API is available.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe w

variable {I : Type w}

/-- The recursive product agrees with the product over the function representation of a word. -/
theorem positiveWordProduct_eq_fin_prod (x : I → ℕ) (r : ℕ)
    (q : Tensor.PositiveWord I r) :
    positiveWordProduct x r q =
      ∏ j, x (Tensor.positiveWordEquiv I r q j) := by
  induction r with
  | zero =>
      change I at q
      change x q = ∏ j, x (Tensor.positiveWordEquiv I 0 q j)
      rw [Fin.prod_univ_one]
      exact congrArg x
        (congrFun (Tensor.positiveWordEquiv_zero_apply I q) 0).symm
  | succ r ih =>
      rw [positiveWordProduct_succ, ih q.1,
        Tensor.positiveWordEquiv_succ_apply]
      let f : Fin (r + 1) → I := Tensor.positiveWordEquiv I r q.1
      let y : I := q.2
      have hcomp :
          (fun j : Fin (r + 2) ↦
            x ((Fin.snoc f y : Fin (r + 2) → I) j)) =
            (Fin.snoc
              (fun j : Fin (r + 1) ↦ x (f j)) (x y) : Fin (r + 2) → ℕ) := by
        funext j
        refine Fin.lastCases ?_ (fun k ↦ ?_) j <;> simp
      change
        (∏ j, x (f j)) * x y =
          ∏ j, x ((Fin.snoc f y : Fin (r + 2) → I) j)
      rw [hcomp, Fin.prod_snoc]

end AlgebraicComplexity
