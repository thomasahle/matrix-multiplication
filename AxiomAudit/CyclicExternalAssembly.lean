/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.CyclicExternalAssembly

set_option autoImplicit false

/-!
# Audit and nonvacuous client for cyclic product assembly

The client constructs both local restrictions by diagonal zeroing of genuine direct sums.  Thus
the theorem is exercised with two and three nonempty cyclic child copies, producing six Cartesian
outputs rather than an empty or assumed extraction.
-/

open AlgebraicComplexity Tensor

#assert_axioms Restricts.symThree_external_indexedDirectSum

section

variable {K : Type*} [CommSemiring K]
variable {V W : Leg → Type*}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

example (A : Tensor3 K V) (B : Tensor3 K W) :
    Restricts
      (symThree K (external
        (indexedDirectSum (fun _ : Fin 2 ↦ A))
        (indexedDirectSum (fun _ : Fin 3 ↦ B))))
      (indexedDirectSum (fun _ : Fin 2 × Fin 3 ↦
        symThree K (external A B))) := by
  apply Restricts.symThree_external_indexedDirectSum
  · exact Restricts.cyclic_indexedDirectSum_diagonal (fun _ : Fin 2 ↦ A)
  · exact Restricts.cyclic_indexedDirectSum_diagonal (fun _ : Fin 3 ↦ B)

example : Fintype.card (Fin 2 × Fin 3) = 6 := by
  simp only [Fintype.card_prod, Fintype.card_fin]

end
