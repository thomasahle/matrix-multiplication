/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SparseRepairCounting
import AlgebraicComplexity.Combinatorics.ProportionalSparseCounting

/-!
# Proportional counting for sparse repair families

This module packages the arithmetic used after an aggregate competitor-incidence estimate.
Selecting one type class costs a factor `typeLoss`; if the three dense-fiber budgets occupy at
most half of the chosen class, the simultaneously sparse family costs only one further factor
`2`.

The statement is independent of Coppersmith--Winograd tensors.  Concrete constructions need only
instantiate the modeled fiber family and prove its three finite incidence inequalities.
-/

namespace AlgebraicComplexity.HoleRepair

open AlgebraicComplexity Tensor

universe u

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {I : Type u} [Fintype I] [DecidableEq I]
variable {U : Leg → Type u}
variable [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
variable {family : I → Tensor3 K U}

/-- A largest-type estimate and a half-density aggregate-incidence estimate bound the original
family by twice the type loss times the simultaneously sparse subfamily. -/
theorem ModeledFiberFamily.card_total_le_two_mul_typeLoss_mul_sparseIndices
    (model : ModeledFiberFamily P family)
    (total typeLoss base : ℕ)
    (htype : total ≤ typeLoss * Fintype.card I)
    (budget : Leg → ℕ)
    (haggregate : ∀ c,
      base * 4 * ∑ i : I, (model.holes i c).card ≤
        budget c * Fintype.card (A c))
    (hhalf : 2 * (budget .X + budget .Y + budget .Z) ≤ Fintype.card I) :
    total ≤ (2 * typeLoss) * (model.sparseIndices base).card := by
  let budgetSum := budget .X + budget .Y + budget .Z
  let sparseCard := (model.sparseIndices base).card
  have hcover : Fintype.card I ≤ sparseCard + budgetSum :=
    model.card_le_card_sparseIndices_add_budgets base budget haggregate
  exact card_le_two_mul_loss_mul_sparse_of_cover
    total typeLoss (Fintype.card I) sparseCard budgetSum htype hcover hhalf

/-- The exact fixed-type quotient has enough simultaneously sparse repair plans.  The doubled
candidate-independent supply is provided separately by
`two_mul_fixedTypeRepairOutputCount_mul_budget_le_fixed`. -/
theorem ModeledFiberFamily.fixedTypeRepairOutputCount_mul_repairBudget_le_sparseIndices
    (model : ModeledFiberFamily P family)
    (base repairBudget : ℕ) (budget : Leg → ℕ)
    (haggregate : ∀ c,
      base * 4 * ∑ i : I, (model.holes i c).card ≤
        budget c * Fintype.card (A c))
    (hhalf : 2 * (budget .X + budget .Y + budget .Z) ≤ Fintype.card I) :
    fixedTypeRepairOutputCount (Fintype.card I) repairBudget * repairBudget ≤
      (model.sparseIndices base).card := by
  apply fixedTypeRepairOutputCount_mul_budget_le_sparse_of_half
  have hcover := model.card_le_card_sparseIndices_add_budgets
    base budget haggregate
  simpa only [one_mul] using card_le_two_mul_loss_mul_sparse_of_cover
    (Fintype.card I) 1 (Fintype.card I) (model.sparseIndices base).card
      (budget .X + budget .Y + budget .Z) (by simp) hcover hhalf

end AlgebraicComplexity.HoleRepair
