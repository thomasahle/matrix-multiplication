/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Coupling
import AlgebraicComplexity.Probability.KullbackLeiblerElementarySparse

/-!
# Entropy gaps from a coordinate deviation of a finite coupling

A coupling whose joint law differs from the independent product in either direction loses a fixed
quadratic amount of Shannon entropy.  The constant `1/4` comes from the derivative-free
coordinatewise KL bound, and any positive constant suffices for the subexponential repair
application.
-/

namespace AlgebraicComplexity
namespace ProbabilityVector

universe u v

variable {D : Type u} {E : Type v} [Fintype D] [Fintype E]
variable [DecidableEq D] [DecidableEq E]

/-- An absolute coordinate deviation `epsilon` from the independent product forces an entropy
deficit of at least `epsilon^2 / 4` nats.  Structural zeroes are allowed. -/
theorem IsCoupling.entropy_le_add_sub_quarter_sq_of_coordinateDeviation
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) (d : D) (e : E)
    {epsilon : ℝ} (hepsilon : 0 <= epsilon)
    (hdeviation : epsilon <=
      |joint.weight (d, e) - (left.product right).weight (d, e)|) :
    joint.entropy <= left.entropy + right.entropy - epsilon ^ 2 / 4 := by
  have hkl := quarter_sq_sub_weight_le_klDiv_of_absoluteContinuity_elementary
    joint (left.product right) h.isAbsolutelyContinuous_product (d, e)
  rw [h.klDiv_product_eq_entropy_gap] at hkl
  have hsquare : epsilon ^ 2 <=
      (joint.weight (d, e) - (left.product right).weight (d, e)) ^ 2 := by
    rw [← sq_abs (joint.weight (d, e) - (left.product right).weight (d, e))]
    exact (sq_le_sq₀ hepsilon (abs_nonneg _)).2 hdeviation
  nlinarith

end ProbabilityVector
end AlgebraicComplexity
