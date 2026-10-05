/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSliceDefs

/-! # The `(1,1,0)` base CW constituent as a one-slice tensor -/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- The direct typed `(1,1,0)` maps produce `\langle 1,q,1\rangle`. -/
theorem map_cw110OneSliceMap :
    Tensor.map (cw110OneSliceMap K q)
        (cwConstituentOfBlocks K q .middle .middle .zero) =
      matrixMultiplication (K := K) 1 q 1 := by
  rw [show cwConstituentOfBlocks K q .middle .middle .zero =
      ∑ i : Fin q, pure (K := K) (ofLegs
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .middle i)
        (cwBlockBasis K q .zero ())) from rfl]
  rw [map_sum, OneSliceProduct.matrixMultiplication_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Tensor.map_pure]
  congr 1
  funext c
  cases c <;> ext a
  · rcases a with ⟨h, j⟩
    have hh : h = 0 := Subsingleton.elim _ _
    subst h
    simp only [cw110, cwBlockAddress, cw110OneSliceMap, cw110OneSliceIndex, ofLegs,
      cwBlockBasis, CWBlockIndex, mmTerm]
    change (Pi.single i (1 : K) : Fin q → K) j =
      (Pi.single (0, i) (1 : K) : Fin 1 × Fin q → K) (0, j)
    by_cases hji : j = i
    · subst j
      exact (Pi.single_eq_same (M := fun _ : Fin q ↦ K) i (1 : K)).trans
        (Pi.single_eq_same (M := fun _ : Fin 1 × Fin q ↦ K) (0, i) (1 : K)).symm
    · have hpair : (0, j) ≠ ((0, i) : Fin 1 × Fin q) := by
        intro h
        exact hji (congrArg Prod.snd h)
      exact (Pi.single_eq_of_ne (M := fun _ : Fin q ↦ K) hji (1 : K)).trans
        (Pi.single_eq_of_ne (M := fun _ : Fin 1 × Fin q ↦ K) hpair (1 : K)).symm
  · rcases a with ⟨j, h⟩
    have hh : h = 0 := Subsingleton.elim _ _
    subst h
    simp only [cw110, cwBlockAddress, cw110OneSliceMap, cw110OneSliceIndex, ofLegs,
      cwBlockBasis, CWBlockIndex, mmTerm]
    change (Pi.single i (1 : K) : Fin q → K) j =
      (Pi.single (i, 0) (1 : K) : Fin q × Fin 1 → K) (j, 0)
    by_cases hji : j = i
    · subst j
      exact (Pi.single_eq_same (M := fun _ : Fin q ↦ K) i (1 : K)).trans
        (Pi.single_eq_same (M := fun _ : Fin q × Fin 1 ↦ K) (i, 0) (1 : K)).symm
    · have hpair : (j, 0) ≠ ((i, 0) : Fin q × Fin 1) := by
        intro h
        exact hji (congrArg Prod.fst h)
      exact (Pi.single_eq_of_ne (M := fun _ : Fin q ↦ K) hji (1 : K)).trans
        (Pi.single_eq_of_ne (M := fun _ : Fin q × Fin 1 ↦ K) hpair (1 : K)).symm
  · rcases a with ⟨h₁, h₂⟩
    have hh₁ : h₁ = 0 := Subsingleton.elim _ _
    have hh₂ : h₂ = 0 := Subsingleton.elim _ _
    subst h₁
    subst h₂
    change (Pi.single () (1 : K) : Unit → K) () = 1
    simp only [Pi.single_eq_same]

/-- Explicit one-slice certificate for the typed `(1,1,0)` constituent. -/
noncomputable def cw110OneSliceRestriction :
    OneSliceRestriction
      (cwConstituentOfBlocks K q .middle .middle .zero) q where
  legMap := cw110OneSliceMap K q
  map_eq := map_cw110OneSliceMap K q

end AlgebraicComplexity.Examples
