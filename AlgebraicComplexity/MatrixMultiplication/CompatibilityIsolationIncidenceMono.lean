/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationCounting

/-!
# Competitor incidence shrinks with the ambient family

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).
`MatrixMultiplication/CompatibilityIsolationCounting.lean` already proves the *floor* for
compatibility zeroing --- `card_le_card_compatibilityIsolatedSupport_add_sum_competitors`, its
two-stage form `card_le_card_YZCompatibilityIsolatedSupport_add_incidences`, and the budget and
one-half forms --- together with the method-of-types adapter that turns a conditional type-class
encoding of a competitor fiber into a multinomial bound.  Nothing here duplicates that.

The one fact those statements do not record is that
`compatibilityCompetitorIncidence` is *monotone* in the ambient family.  It matters for a client
of the two-stage floor: that theorem deliberately measures the second stage's incidence on the
support the first stage leaves, which is the tight choice but forces a counting client to describe
the intermediate family.  With monotonicity the client may instead bound both incidences on its
original support --- a weaker hypothesis, but one stated entirely in terms of the family it
actually constructed.

Both directions of the trade-off are then available:
`card_le_card_YZCompatibilityIsolatedSupport_add_budgets` for the tight one, and
`card_le_card_YZCompatibilityIsolatedSupport_add_ambientBudgets` below for the convenient one.
-/

namespace AlgebraicComplexity.Tensor

open scoped BigOperators

universe u

variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Shrinking the ambient family shrinks every competitor fiber. -/
theorem compatibilityCompetitors_mono {ambient ambient' : Finset (BlockAddress A)}
    (hsub : ambient' ⊆ ambient) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) (address : BlockAddress A) :
    compatibilityCompetitors ambient' pivot compatible address ⊆
      compatibilityCompetitors ambient pivot compatible address := by
  classical
  intro other hother
  rw [mem_compatibilityCompetitors] at hother ⊢
  exact ⟨hsub hother.1, hother.2⟩

/-- **The exact competitor incidence is monotone in the ambient family.**  Both effects point the
same way: each fiber shrinks, and there are fewer addresses to sum over. -/
theorem compatibilityCompetitorIncidence_mono {ambient ambient' : Finset (BlockAddress A)}
    (hsub : ambient' ⊆ ambient) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) :
    compatibilityCompetitorIncidence ambient' pivot compatible ≤
      compatibilityCompetitorIncidence ambient pivot compatible := by
  classical
  unfold compatibilityCompetitorIncidence
  calc ∑ address ∈ ambient', (compatibilityCompetitors ambient' pivot compatible address).card
      ≤ ∑ address ∈ ambient', (compatibilityCompetitors ambient pivot compatible address).card :=
        Finset.sum_le_sum fun address _ ↦
          Finset.card_le_card (compatibilityCompetitors_mono hsub pivot compatible address)
    _ ≤ ∑ address ∈ ambient, (compatibilityCompetitors ambient pivot compatible address).card :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ Nat.zero_le _

/-- **The two-stage floor with both budgets stated on the original support.**

The tight form `card_le_card_YZCompatibilityIsolatedSupport_add_budgets` measures the `Z`
incidence after `Y` isolation.  Monotonicity lets a client bound it on the ambient family instead,
so neither hypothesis mentions the intermediate stage. -/
theorem card_le_card_YZCompatibilityIsolatedSupport_add_ambientBudgets
    (ambient : Finset (BlockAddress A))
    (compatibleY : A .Y → BlockAddress A → Prop)
    (compatibleZ : A .Z → BlockAddress A → Prop)
    (budgetY budgetZ : ℕ)
    (hbudgetY : compatibilityCompetitorIncidence ambient .Y compatibleY ≤ budgetY)
    (hbudgetZ : compatibilityCompetitorIncidence ambient .Z compatibleZ ≤ budgetZ) :
    let ySupport := compatibilityIsolatedSupport ambient .Y compatibleY
    let zSupport := compatibilityIsolatedSupport ySupport .Z compatibleZ
    ambient.card ≤ zSupport.card + budgetY + budgetZ := by
  refine card_le_card_YZCompatibilityIsolatedSupport_add_budgets ambient compatibleY compatibleZ
    budgetY budgetZ hbudgetY ?_
  exact (compatibilityCompetitorIncidence_mono
    (compatibilityIsolatedSupport_subset ambient .Y compatibleY) .Z compatibleZ).trans hbudgetZ

end AlgebraicComplexity.Tensor
