/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Finite

/-!
# Marginal of a finite joint probability vector

This elementary identity is separated from the entropy chain rule so structural-support clients
can compute a joint law's first marginal without importing entropy.
-/

open scoped BigOperators

namespace AlgebraicComplexity.ProbabilityVector

universe u v

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

/-- The first marginal of a joint law is its outer law. -/
@[simp] theorem pushforward_joint_fst [DecidableEq I]
    (p : ProbabilityVector I) (family : I → ProbabilityVector J) :
    (p.joint family).pushforward Prod.fst = p := by
  ext i
  rw [pushforward_weight, Fintype.sum_prod_type]
  simp_rw [joint_weight]
  calc
    (∑ i', ∑ j, if i' = i then p.weight i' * (family i').weight j else 0) =
        ∑ i', if i' = i then p.weight i' else 0 := by
      apply Finset.sum_congr rfl
      intro i' _
      by_cases h : i' = i
      · simp only [h, if_pos]
        rw [← Finset.mul_sum, (family i).total, mul_one]
      · simp [h]
    _ = p.weight i := by simp

end AlgebraicComplexity.ProbabilityVector
