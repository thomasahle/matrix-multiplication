/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PositiveWordRelation

set_option autoImplicit false

/-!
# Axiom audit for positive-word relation lifting

This companion enforces the trust boundary for the factorwise exact-restriction theorem on
heterogeneous positive-word tensor products.  The audited theorem is the product-functoriality
step used by the exceptional `(1,1,2)` power construction of [CoppersmithWinograd1990,
pp. 270--272].
-/

#assert_axioms AlgebraicComplexity.Tensor.Restricts.positiveWordTensor

namespace AlgebraicComplexity.Tensor

universe u v z

variable {K : Type u} [CommSemiring K]

/-- The hypotheses of `Restricts.positiveWordTensor` are satisfiable: identity restrictions on
the factors give a restriction of every word tensor to itself. -/
example {I : Type z}
    (W : I → LegModuleFamily.{u, v} K)
    (T : ∀ i, Tensor3 K (W i).Space)
    (n : ℕ) (word : PositiveWord I n) :
    Restricts (positiveWordTensor W T n word)
      (positiveWordTensor W T n word) :=
  Restricts.positiveWordTensor W W T T (fun i ↦ Restricts.refl (T i)) n word

end AlgebraicComplexity.Tensor
