/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Census
import AlgebraicComplexity.Combinatorics.HeterogeneousProductHoleBound

set_option autoImplicit false

/-!
# Finite product-hole audit and nonempty three-factor client

The application uses three Boolean factors with one present symbol per factor. There are
seven missing product words out of eight, and the sum of the three hole cylinders is twelve.
Only these eight-word examples use finite reduction; the public bound is proved by a cover.
The final census also checks every project declaration in this small import closure.
-/

open scoped BigOperators

#assert_axioms AlgebraicComplexity.card_piFinset_sdiff_piFinset_le_sum

example :
    (Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset Bool)) \
      Fintype.piFinset (fun _ : Fin 3 => ({false} : Finset Bool))).card ≤
      ∑ i : Fin 3, ((Finset.univ : Finset Bool) \ {false}).card *
        ∏ _j : {j : Fin 3 // j ≠ i}, (Finset.univ : Finset Bool).card :=
  AlgebraicComplexity.card_piFinset_sdiff_piFinset_le_sum _ _

example :
    (Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset Bool)) \
      Fintype.piFinset (fun _ : Fin 3 => ({false} : Finset Bool))).card = 7 := by
  decide

example :
    (∑ i : Fin 3, ((Finset.univ : Finset Bool) \ {false}).card *
      ∏ _j : {j : Fin 3 // j ≠ i}, (Finset.univ : Finset Bool).card) = 12 := by
  decide

#axiom_census
