/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PositiveWordConstantPower

set_option autoImplicit false

/-!
# Axiom audit for constant positive-word products

This companion enforces the trust boundary for the coherence isomorphism from a constant
positive-word tensor to the corresponding canonical tensor power.
-/

#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.positiveWordTensor_const_power

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]

/-- The audited coherence theorem is applicable to every actual word and tensor; it carries no
hidden extraction or nonemptiness premise. -/
example {I : Type w} [Fintype I]
    (A : LegModuleFamily.{u, v} K) (T : Tensor3 K A.Space)
    (n : ℕ) (word : PositiveWord I n) :
    Isomorphic
      (positiveWordTensor (fun _ : I ↦ A) (fun _ : I ↦ T) n word)
      (Tensor.power T (n + 1)) :=
  Isomorphic.positiveWordTensor_const_power A T n word

end AlgebraicComplexity.Tensor
