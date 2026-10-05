/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.GroupedVariableHoleRepair

/-!
# Counting sparse damaged fibers from aggregate hole incidence

The semantic repair theorem consumes fibers satisfying three pointwise hole-density bounds.
Concrete laser arguments more naturally bound the *sum* of missing labels over all retained
fibers.  This file supplies the exact finite Markov/union conversion between those interfaces.

All inequalities are division-free.  No asymptotic or tensor-specific hypothesis enters here.
-/

namespace AlgebraicComplexity.HoleRepair

open AlgebraicComplexity.Tensor
open scoped BigOperators

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

namespace ModeledFiberFamily

/-- Fibers violating the sparse-hole inequality on one specified leg. -/
noncomputable def denseIndices
    (model : ModeledFiberFamily P family) (base : ℕ) (c : Leg) : Finset I := by
  classical
  exact Finset.univ.filter fun i ↦
    Fintype.card (A c) < base * (4 * (model.holes i c).card)

omit [DecidableEq I] in
@[simp] theorem mem_denseIndices_iff
    (model : ModeledFiberFamily P family) (base : ℕ) (c : Leg) (i : I) :
    i ∈ model.denseIndices base c ↔
      Fintype.card (A c) < base * (4 * (model.holes i c).card) := by
  classical
  simp [denseIndices]

omit [DecidableEq I] in
/-- A division-free aggregate hole bound controls the number of fibers which are too damaged on
one leg.  This is the finite Markov step needed before varying-pattern repair. -/
theorem card_denseIndices_le_of_aggregate
    (model : ModeledFiberFamily P family) (base : ℕ) (c : Leg) (budget : ℕ)
    (haggregate :
      base * 4 * ∑ i : I, (model.holes i c).card ≤
        budget * Fintype.card (A c)) :
    (model.denseIndices base c).card ≤ budget := by
  classical
  by_cases hcard : Fintype.card (A c) = 0
  · have hholes (i : I) : (model.holes i c).card = 0 := by
      have hle := Finset.card_le_univ (model.holes i c)
      rw [hcard] at hle
      omega
    have hdense : model.denseIndices base c = ∅ := by
      ext i
      simp [mem_denseIndices_iff, hcard, hholes]
    simp [hdense]
  · have hcardPos : 0 < Fintype.card (A c) := Nat.pos_of_ne_zero hcard
    by_contra hnot
    have hbudgetLt : budget < (model.denseIndices base c).card :=
      Nat.lt_of_not_ge hnot
    have hdenseNonempty : (model.denseIndices base c).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hstrict :
        (model.denseIndices base c).card * Fintype.card (A c) <
          ∑ i ∈ model.denseIndices base c,
            base * (4 * (model.holes i c).card) := by
      rw [show (model.denseIndices base c).card * Fintype.card (A c) =
          ∑ _i ∈ model.denseIndices base c, Fintype.card (A c) by simp]
      exact Finset.sum_lt_sum_of_nonempty hdenseNonempty fun i hi ↦
        (model.mem_denseIndices_iff base c i).1 hi
    have hsubset : model.denseIndices base c ⊆ (Finset.univ : Finset I) :=
      Finset.subset_univ _
    have hsumLe :
        (∑ i ∈ model.denseIndices base c,
            base * (4 * (model.holes i c).card)) ≤
          base * 4 * ∑ i : I, (model.holes i c).card := by
      calc
        (∑ i ∈ model.denseIndices base c,
            base * (4 * (model.holes i c).card)) =
            base * 4 * ∑ i ∈ model.denseIndices base c,
              (model.holes i c).card := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          exact (Nat.mul_assoc base 4 (model.holes i c).card).symm
        _ ≤ base * 4 * ∑ i : I, (model.holes i c).card := by
          apply Nat.mul_le_mul_left
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun _ _ _ ↦ Nat.zero_le _)
    have hproduct :
        (model.denseIndices base c).card * Fintype.card (A c) <
      budget * Fintype.card (A c) :=
      hstrict.trans_le (hsumLe.trans haggregate)
    have hdenseLtBudget : (model.denseIndices base c).card < budget :=
      Nat.lt_of_mul_lt_mul_right hproduct
    omega

/-- Every index is either sparse on all three legs or dense on at least one named leg. -/
theorem univ_subset_sparseIndices_union_denseIndices
    (model : ModeledFiberFamily P family) (base : ℕ) :
    (Finset.univ : Finset I) ⊆
      model.sparseIndices base ∪
        ((model.denseIndices base .X ∪ model.denseIndices base .Y) ∪
          model.denseIndices base .Z) := by
  classical
  intro i _hi
  by_cases hsparse : i ∈ model.sparseIndices base
  · exact Finset.mem_union_left _ hsparse
  · have hnotAll : ¬ ∀ c,
        base * (4 * (model.holes i c).card) ≤ Fintype.card (A c) := by
      simpa [model.mem_sparseIndices_iff base i] using hsparse
    push Not at hnotAll
    obtain ⟨c, hc⟩ := hnotAll
    have hdense : i ∈ model.denseIndices base c := by
      exact (model.mem_denseIndices_iff base c i).2 hc
    simp only [Finset.mem_union]
    cases c with
    | X => exact Or.inr (Or.inl (Or.inl hdense))
    | Y => exact Or.inr (Or.inl (Or.inr hdense))
    | Z => exact Or.inr (Or.inr hdense)

/-- Three aggregate incidence budgets give an exact lower bound on the simultaneously sparse
fiber count. -/
theorem card_le_card_sparseIndices_add_budgets
    (model : ModeledFiberFamily P family) (base : ℕ) (budget : Leg → ℕ)
    (haggregate : ∀ c,
      base * 4 * ∑ i : I, (model.holes i c).card ≤
        budget c * Fintype.card (A c)) :
    Fintype.card I ≤ (model.sparseIndices base).card +
      (budget .X + budget .Y + budget .Z) := by
  classical
  have hcover := Finset.card_le_card
    (model.univ_subset_sparseIndices_union_denseIndices base)
  have hunion :
      (model.sparseIndices base ∪
          ((model.denseIndices base .X ∪ model.denseIndices base .Y) ∪
            model.denseIndices base .Z)).card ≤
        (model.sparseIndices base).card +
          ((model.denseIndices base .X).card +
            (model.denseIndices base .Y).card +
            (model.denseIndices base .Z).card) := by
    calc
      _ ≤ (model.sparseIndices base).card +
          ((model.denseIndices base .X ∪ model.denseIndices base .Y) ∪
            model.denseIndices base .Z).card := Finset.card_union_le _ _
      _ ≤ (model.sparseIndices base).card +
          ((model.denseIndices base .X ∪ model.denseIndices base .Y).card +
            (model.denseIndices base .Z).card) :=
        Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ ≤ (model.sparseIndices base).card +
          (((model.denseIndices base .X).card +
              (model.denseIndices base .Y).card) +
            (model.denseIndices base .Z).card) := by
        gcongr
        exact Finset.card_union_le _ _
      _ = _ := by omega
  have hX := model.card_denseIndices_le_of_aggregate
    base .X (budget .X) (haggregate .X)
  have hY := model.card_denseIndices_le_of_aggregate
    base .Y (budget .Y) (haggregate .Y)
  have hZ := model.card_denseIndices_le_of_aggregate
    base .Z (budget .Z) (haggregate .Z)
  simpa only [Finset.card_univ] using
    hcover.trans (hunion.trans (by omega))

/-- Subtraction form of the simultaneous sparse-fiber lower bound. -/
theorem card_sub_budgets_le_card_sparseIndices
    (model : ModeledFiberFamily P family) (base : ℕ) (budget : Leg → ℕ)
    (haggregate : ∀ c,
      base * 4 * ∑ i : I, (model.holes i c).card ≤
        budget c * Fintype.card (A c)) :
    Fintype.card I - (budget .X + budget .Y + budget .Z) ≤
      (model.sparseIndices base).card := by
  have h := model.card_le_card_sparseIndices_add_budgets base budget haggregate
  omega

/-- Maximal number of complete repair supplies obtainable from the sparse fibers by Euclidean
division. -/
noncomputable def maximalRepairOutputCount
    (model : ModeledFiberFamily P family) (base : ℕ)
    (target : ∀ c, Finset (A c)) : ℕ :=
  (model.sparseIndices base).card /
    sevenBranchBudget (logarithmicRepairDepth base target)

omit [DecidableEq I] in
/-- The maximal quotient count satisfies the repair constructor's exact multiplication budget. -/
theorem maximalRepairOutputCount_mul_budget_le_sparse
    (model : ModeledFiberFamily P family) (base : ℕ)
    (target : ∀ c, Finset (A c)) :
    model.maximalRepairOutputCount base target *
        sevenBranchBudget (logarithmicRepairDepth base target) ≤
      (model.sparseIndices base).card := by
  unfold maximalRepairOutputCount
  exact Nat.div_mul_le_self _ _

omit [DecidableEq I] in
/-- Any requested copy count whose complete repair supplies fit in the sparse family is bounded
by the canonical maximal quotient count. -/
theorem le_maximalRepairOutputCount_of_mul_budget_le
    (model : ModeledFiberFamily P family) (base : ℕ)
    (target : ∀ c, Finset (A c)) (copies : ℕ)
    (hcopies : copies * sevenBranchBudget (logarithmicRepairDepth base target) ≤
      (model.sparseIndices base).card) :
    copies ≤ model.maximalRepairOutputCount base target := by
  unfold maximalRepairOutputCount
  apply (Nat.le_div_iff_mul_le ?_).2 hcopies
  induction logarithmicRepairDepth base target with
  | zero => simp
  | succ d ih =>
      rw [sevenBranchBudget_succ]
      omega

/-- Canonical finite packaging of the repair parameters: take the exact logarithmic depth and
one output for each complete seven-branch supply contained in the sparse family. -/
theorem exists_maximalRepairPlans
    (model : ModeledFiberFamily P family)
    {Relabel : Type u} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : UniformStructureRelabelings (G := Relabel) P)
    {base : ℕ} (hbase : 1 < base)
    (target : ∀ c, Finset (A c)) :
    ∃ plans : ULift.{u} (Fin (model.maximalRepairOutputCount base target)) →
        RepairPlan P target,
      ∃ pick : (Σ output, (plans output).Copy) ↪ I,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 =
            model.holes (pick occurrence)) ∧
        Restricts (Tensor.indexedDirectSum family)
          (Tensor.indexedDirectSum
            (fun _output : ULift.{u} (Fin (model.maximalRepairOutputCount base target)) ↦
              (P.box target).realize)) := by
  exact model.exists_repairPlans_of_mul_budget_le_sparse
    (O := ULift.{u} (Fin (model.maximalRepairOutputCount base target))) relabelings hbase
      (logarithmicRepairDepth base target) target le_rfl (by
        simpa only [Fintype.card_ulift, Fintype.card_fin] using
          model.maximalRepairOutputCount_mul_budget_le_sparse base target)

end ModeledFiberFamily

end AlgebraicComplexity.HoleRepair
