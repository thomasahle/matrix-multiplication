/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Power

/-!
# The three-orientation cyclic product

`cyclicPowerProduct T k` is the source tensor used by the modern value formalism: the `k`th power
of `T`, together with its two cyclic leg orientations.  The definition is kept in this small
tensor-only module so finite value certificates do not need to import the asymptotic-sum theorem.
Coherence and border-rank lemmas are proved in the corresponding higher-level modules.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Product of the `k`th power of a tensor with its two cyclic leg orientations. -/
noncomputable def cyclicPowerProduct (T : Tensor3 K V) (k : ℕ) :=
  let P := Tensor.power T k
  Tensor.external
    (Tensor.external P (Tensor.permute cycle P))
    (Tensor.permute cycle.symm P)

end AlgebraicComplexity
