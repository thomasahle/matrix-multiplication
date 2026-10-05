/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSliceDefs

/-! # The `(0,2,0)` base CW constituent as a one-slice tensor -/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- The direct typed `(0,2,0)` maps produce `\langle 1,1,1\rangle`. -/
theorem map_cw020OneSliceMap :
    Tensor.map (cw020OneSliceMap K q)
        (cwConstituentOfBlocks K q .zero .last .zero) =
      matrixMultiplication (K := K) 1 1 1 := by
  rw [show cwConstituentOfBlocks K q .zero .last .zero =
      pure (K := K) (ofLegs
        (cwBlockBasis K q .zero ())
        (cwBlockBasis K q .last ())
        (cwBlockBasis K q .zero ())) from rfl]
  rw [Tensor.map_pure, OneSliceProduct.matrixMultiplication_eq_sum]
  simp only [Fintype.sum_unique]
  congr 1
  funext c
  cases c <;> ext a
  all_goals
    have ha : a = (0, 0) := Subsingleton.elim _ _
    subst a
    change (Pi.single () (1 : K) : Unit → K) () = 1
    simp only [Pi.single_eq_same]

/-- Explicit one-slice certificate for the typed `(0,2,0)` constituent. -/
noncomputable def cw020OneSliceRestriction :
    OneSliceRestriction
      (cwConstituentOfBlocks K q .zero .last .zero) 1 where
  legMap := cw020OneSliceMap K q
  map_eq := map_cw020OneSliceMap K q

end AlgebraicComplexity.Examples
