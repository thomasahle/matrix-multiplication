/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.CyclicHybridAssembly

set_option autoImplicit false

/-! # Audit and nonvacuous mixed cyclic assembly client -/

open AlgebraicComplexity Tensor

#assert_axioms Restricts.symThree_hybrid_indexedDirectSum

section

variable {K : Type*} [CommSemiring K]
variable {V W : Leg → Type*}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

-- Both local restrictions are constructed, not assumed. The diagonal cyclic restriction
-- keeps three copies from the 27 Cartesian copies of the second factor.
example (A : Tensor3 K V) (B : Tensor3 K W) :
    Restricts
      (symThree K (external
        (indexedDirectSum (fun _ : Fin 2 ↦ A))
        (indexedDirectSum (fun _ : Fin 3 ↦ B))))
      (indexedDirectSum (fun _ : ((Fin 2 × Fin 2) × Fin 2) × Fin 3 ↦
        symThree K (external A B))) := by
  apply Restricts.symThree_hybrid_indexedDirectSum (Restricts.refl _)
  exact Restricts.cyclic_indexedDirectSum_diagonal (fun _ : Fin 3 ↦ B)

example : Fintype.card (((Fin 2 × Fin 2) × Fin 2) × Fin 3) = 24 := by
  simp only [Fintype.card_prod, Fintype.card_fin]

end
