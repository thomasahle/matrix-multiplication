/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationCounting
import AlgebraicComplexity.Tensor.GroupedCompatibilityZeroing

/-!
# Exact counting for grouped compatibility isolation

Grouped compatibility cleanup deletes a fine address only when its pivot label is compatible
with an address in a different coarse group.  This module records the corresponding exact finite
incidence bound.  It is the grouped analogue of `CompatibilityIsolationCounting` and is the
counting interface used before target-specific hole repair.
-/

namespace AlgebraicComplexity.Tensor

open scoped BigOperators

universe u v w

variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {Γ : Type v}

/-- Distinct compatible addresses lying in a different coarse group from `address`. -/
noncomputable def groupCompatibilityCompetitors
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop)
    (address : BlockAddress A) : Finset (BlockAddress A) := by
  classical
  exact (ambient.erase address).filter fun other ↦
    compatible (address pivot) other ∧ group other ≠ group address

omit [∀ c, Fintype (A c)] in
@[simp] theorem mem_groupCompatibilityCompetitors
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop)
    (address other : BlockAddress A) :
    other ∈ groupCompatibilityCompetitors ambient group pivot compatible address ↔
      other ∈ ambient ∧ other ≠ address ∧
        compatible (address pivot) other ∧ group other ≠ group address := by
  classical
  simp [groupCompatibilityCompetitors, and_assoc, and_comm]

omit [∀ c, Fintype (A c)] in
/-- Every discarded ambient address has a concrete cross-group compatibility competitor. -/
theorem groupCompatibilityCompetitors_nonempty_of_not_isolated
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop)
    {address : BlockAddress A} (haddress : address ∈ ambient)
    (hnot : address ∉
      groupCompatibilityIsolatedSupport ambient group pivot compatible) :
    (groupCompatibilityCompetitors ambient group pivot compatible address).Nonempty := by
  classical
  have hnotUnique : ¬ IsGroupUniquelyCompatible ambient group pivot compatible address := by
    intro hunique
    exact hnot ((mem_groupCompatibilityIsolatedSupport
      ambient group pivot compatible address).2 hunique)
  have hnotAll : ¬ ∀ other ∈ ambient,
      compatible (address pivot) other → group other = group address := by
    intro hall
    exact hnotUnique ⟨haddress, hall⟩
  push Not at hnotAll
  obtain ⟨other, hother, hcompatible, hgroup⟩ := hnotAll
  have hne : other ≠ address := by
    intro heq
    subst other
    exact hgroup rfl
  exact ⟨other, (mem_groupCompatibilityCompetitors
    ambient group pivot compatible address other).2
      ⟨hother, hne, hcompatible, hgroup⟩⟩

/-- One grouped compatibility cleanup loses at most its exact cross-group incidence count. -/
theorem card_le_card_groupCompatibilityIsolatedSupport_add_sum_competitors
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop) :
    ambient.card ≤
      (groupCompatibilityIsolatedSupport ambient group pivot compatible).card +
        ∑ address ∈ ambient,
          (groupCompatibilityCompetitors ambient group pivot compatible address).card := by
  classical
  let isolated := groupCompatibilityIsolatedSupport ambient group pivot compatible
  let bad := ambient \ isolated
  have hbad : bad.card ≤
      ∑ address ∈ ambient,
        (groupCompatibilityCompetitors ambient group pivot compatible address).card := by
    calc
      bad.card = ∑ _address ∈ bad, 1 := by simp
      _ ≤ ∑ address ∈ bad,
          (groupCompatibilityCompetitors ambient group pivot compatible address).card := by
        apply Finset.sum_le_sum
        intro address haddress
        have hmem := Finset.mem_sdiff.mp haddress
        exact (groupCompatibilityCompetitors_nonempty_of_not_isolated
          ambient group pivot compatible hmem.1 hmem.2).card_pos
      _ ≤ ∑ address ∈ ambient,
          (groupCompatibilityCompetitors ambient group pivot compatible address).card := by
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun _ _ _ ↦ Nat.zero_le _)
  have hpartition : bad.card + isolated.card = ambient.card :=
    Finset.card_sdiff_add_card_eq_card
      (groupCompatibilityIsolatedSupport_subset ambient group pivot compatible)
  dsimp only [bad, isolated] at hbad hpartition ⊢
  omega

/-- Exact cross-group competitor incidence for one grouped cleanup. -/
noncomputable def groupCompatibilityCompetitorIncidence
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop) : ℕ :=
  ∑ address ∈ ambient,
    (groupCompatibilityCompetitors ambient group pivot compatible address).card

/-- Cross-group competitors are a subset of the ordinary compatibility competitors. -/
theorem groupCompatibilityCompetitors_subset_compatibilityCompetitors
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop)
    (address : BlockAddress A) :
    groupCompatibilityCompetitors ambient group pivot compatible address ⊆
      compatibilityCompetitors ambient pivot compatible address := by
  intro other hother
  have h := (mem_groupCompatibilityCompetitors
    ambient group pivot compatible address other).1 hother
  exact (mem_compatibilityCompetitors ambient pivot compatible address other).2
    ⟨h.1, h.2.1, h.2.2.1⟩

/-- Grouped competitor incidence is bounded by the already formalized ordinary incidence. -/
theorem groupCompatibilityCompetitorIncidence_le_compatibilityCompetitorIncidence
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop) :
    groupCompatibilityCompetitorIncidence ambient group pivot compatible ≤
      compatibilityCompetitorIncidence ambient pivot compatible := by
  classical
  unfold groupCompatibilityCompetitorIncidence compatibilityCompetitorIncidence
  apply Finset.sum_le_sum
  intro address _
  exact Finset.card_le_card
    (groupCompatibilityCompetitors_subset_compatibilityCompetitors
      ambient group pivot compatible address)

/-- Two grouped compatibility passes lose at most the sum of their exact cross-group incidences.
The second incidence is measured after the first pass, exactly as in the cleanup algorithm. -/
theorem card_le_card_groupYZCompatibilityIsolatedSupport_add_incidences
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivotY pivotZ : Leg)
    (compatibleY : A pivotY → BlockAddress A → Prop)
    (compatibleZ : A pivotZ → BlockAddress A → Prop) :
    let ySupport := groupCompatibilityIsolatedSupport ambient group pivotY compatibleY
    let zSupport := groupCompatibilityIsolatedSupport ySupport group pivotZ compatibleZ
    ambient.card ≤ zSupport.card +
      groupCompatibilityCompetitorIncidence ambient group pivotY compatibleY +
      groupCompatibilityCompetitorIncidence ySupport group pivotZ compatibleZ := by
  dsimp only
  have hy := card_le_card_groupCompatibilityIsolatedSupport_add_sum_competitors
    ambient group pivotY compatibleY
  have hz := card_le_card_groupCompatibilityIsolatedSupport_add_sum_competitors
    (groupCompatibilityIsolatedSupport ambient group pivotY compatibleY)
      group pivotZ compatibleZ
  change ambient.card ≤
      (groupCompatibilityIsolatedSupport ambient group pivotY compatibleY).card +
        groupCompatibilityCompetitorIncidence ambient group pivotY compatibleY at hy
  change (groupCompatibilityIsolatedSupport ambient group pivotY compatibleY).card ≤
      (groupCompatibilityIsolatedSupport
        (groupCompatibilityIsolatedSupport ambient group pivotY compatibleY)
          group pivotZ compatibleZ).card +
        groupCompatibilityCompetitorIncidence
          (groupCompatibilityIsolatedSupport ambient group pivotY compatibleY)
            group pivotZ compatibleZ at hz
  omega

/-- Budget form of the two-stage grouped incidence bound. -/
theorem card_le_card_groupYZCompatibilityIsolatedSupport_add_budgets
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivotY pivotZ : Leg)
    (compatibleY : A pivotY → BlockAddress A → Prop)
    (compatibleZ : A pivotZ → BlockAddress A → Prop)
    (budgetY budgetZ : ℕ)
    (hbudgetY : groupCompatibilityCompetitorIncidence
      ambient group pivotY compatibleY ≤ budgetY)
    (hbudgetZ : groupCompatibilityCompetitorIncidence
      (groupCompatibilityIsolatedSupport ambient group pivotY compatibleY)
        group pivotZ compatibleZ ≤ budgetZ) :
    let ySupport := groupCompatibilityIsolatedSupport ambient group pivotY compatibleY
    let zSupport := groupCompatibilityIsolatedSupport ySupport group pivotZ compatibleZ
    ambient.card ≤ zSupport.card + budgetY + budgetZ := by
  have hcount := card_le_card_groupYZCompatibilityIsolatedSupport_add_incidences
    ambient group pivotY pivotZ compatibleY compatibleZ
  dsimp only at hcount ⊢
  omega

/-- If the two grouped incidence budgets consume at most half the ambient family, at least half
of the coarse-group-compatible addresses survive. -/
theorem card_le_two_mul_card_groupYZCompatibilityIsolatedSupport
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivotY pivotZ : Leg)
    (compatibleY : A pivotY → BlockAddress A → Prop)
    (compatibleZ : A pivotZ → BlockAddress A → Prop)
    (budgetY budgetZ : ℕ)
    (hbudgetY : groupCompatibilityCompetitorIncidence
      ambient group pivotY compatibleY ≤ budgetY)
    (hbudgetZ : groupCompatibilityCompetitorIncidence
      (groupCompatibilityIsolatedSupport ambient group pivotY compatibleY)
        group pivotZ compatibleZ ≤ budgetZ)
    (hhalf : 2 * (budgetY + budgetZ) ≤ ambient.card) :
    let ySupport := groupCompatibilityIsolatedSupport ambient group pivotY compatibleY
    let zSupport := groupCompatibilityIsolatedSupport ySupport group pivotZ compatibleZ
    ambient.card ≤ 2 * zSupport.card := by
  have hcount := card_le_card_groupYZCompatibilityIsolatedSupport_add_budgets
    ambient group pivotY pivotZ compatibleY compatibleZ budgetY budgetZ hbudgetY hbudgetZ
  dsimp only at hcount ⊢
  omega

/-- Any ordinary conditional competitor encoding also bounds the cross-group competitor fiber.
This is the direct adapter from the loss-free method-of-types theorem to grouped cleanup. -/
theorem card_groupCompatibilityCompetitors_le_card_conditionalTypeClass
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop)
    (address : BlockAddress A)
    {U : Type w} {Z : Type w} [Fintype U] [Fintype Z] {samples : ℕ}
    (encoding : ConditionalCompetitorEncoding
      ambient pivot compatible address U Z samples) :
    (groupCompatibilityCompetitors ambient group pivot compatible address).card ≤
      (WordType.conditionalTypeClass encoding.source encoding.jointType).card := by
  exact (Finset.card_le_card
    (groupCompatibilityCompetitors_subset_compatibilityCompetitors
      ambient group pivot compatible address)).trans
      encoding.card_competitors_le_card_conditionalTypeClass

end AlgebraicComplexity.Tensor
