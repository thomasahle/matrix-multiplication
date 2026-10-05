/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.VariableHoleRepair
import AlgebraicComplexity.MatrixMultiplication.GroupedHoleRepair
import AlgebraicComplexity.Tensor.PartitionedGroupingBoxes

/-!
# Repairing many sparse cleaned group fibers

This module composes three finite facts:

* a leg-readable cleaned fiber is exactly the box complementary to its explicit `fiberHoles`;
* a complete seven-branch supply of independently sparse hole patterns constructs a repair plan;
* disjoint repair-plan occurrences assemble into an indexed direct sum of intact target boxes.

The only remaining paper-specific repair obligation is therefore a cardinality lower bound on the
set of cleaned fibers satisfying the explicit hole-density inequality.
-/

namespace AlgebraicComplexity.HoleRepair

open AlgebraicComplexity.Tensor

universe u

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {Γ : Type u} [Fintype Γ] [DecidableEq Γ]

/-- A finite tensor family modeled as differently damaged boxes of one common intact partitioned
tensor.  This is the normalization datum required for CW cleanup fibers: the ambient direct sum
and the common interface tensor need not be the same partitioned tensor. -/
structure ModeledFiberFamily
    {U : Leg → Type u}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (family : Γ → Tensor3 K U) where
  holes : Γ → ∀ c, Finset (A c)
  fiber_restricts : ∀ γ,
    Restricts (family γ)
      (P.box (fun c ↦ Finset.univ \ holes γ c)).realize

namespace ModeledFiberFamily

variable {U : Leg → Type u}
variable [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
variable {family : Γ → Tensor3 K U}

/-- Projection-closed cleanup plus a leg-readable grouping canonically produces a family of
differently damaged boxes of the ideal ambient partitioned tensor.

For paper clients, `P` should be the normalized ideal interface tensor whose part types contain
exactly the available small blocks.  Taking `P` to be a larger ambient tensor is semantically
valid but usually gives a useless hole-density bound. -/
noncomputable def ofProjectionClosedGrouping
    (selected : Finset (BlockAddress A))
    (hclosed : IsProjectionClosed P.support selected Finset.univ)
    (G : (P.withSupport selected).LegGrouping Γ) :
    ModeledFiberFamily P (fun γ ↦ (G.fiber γ).realize) where
  holes := G.fiberHoles
  fiber_restricts γ :=
    G.fiber_restricts_ambientBox_compl_fiberHoles selected hclosed γ

@[simp] theorem ofProjectionClosedGrouping_holes
    (selected : Finset (BlockAddress A))
    (hclosed : IsProjectionClosed P.support selected Finset.univ)
    (G : (P.withSupport selected).LegGrouping Γ) (γ : Γ) (c : Leg) :
    (ofProjectionClosedGrouping selected hclosed G).holes γ c =
      G.fiberHoles γ c :=
  rfl

/-- Modeled fibers satisfying the explicit hole-density condition. -/
noncomputable def sparseIndices
    (model : ModeledFiberFamily P family) (base : ℕ) : Finset Γ := by
  classical
  exact Finset.univ.filter fun γ ↦ ∀ c,
    base * (4 * (model.holes γ c).card) ≤ Fintype.card (A c)

@[simp] theorem mem_sparseIndices_iff
    (model : ModeledFiberFamily P family) (base : ℕ) (γ : Γ) :
    γ ∈ model.sparseIndices base ↔ ∀ c,
      base * (4 * (model.holes γ c).card) ≤ Fintype.card (A c) := by
  classical
  simp [sparseIndices]

/-- Enough sparse modeled fibers supply disjoint varying repair plans for all requested outputs. -/
theorem exists_repairPlans_of_sparse_count
    (model : ModeledFiberFamily P family)
    {Relabel : Type u} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : UniformStructureRelabelings (G := Relabel) P)
    {O : Type u} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (A c))
    (hdepth : logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card (O × RepairSupplyIndex d) ≤
      (model.sparseIndices base).card) :
    ∃ plans : O → RepairPlan P target,
      ∃ pick : (Σ output, (plans output).Copy) ↪ Γ,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 = model.holes (pick occurrence)) ∧
        Restricts (Tensor.indexedDirectSum family)
          (Tensor.indexedDirectSum (fun _output : O ↦ (P.box target).realize)) := by
  classical
  let Sparse := { γ // γ ∈ model.sparseIndices base }
  have hSparseCard : Fintype.card Sparse = (model.sparseIndices base).card :=
    Fintype.card_coe _
  have hassignCard : Fintype.card (O × RepairSupplyIndex d) ≤ Fintype.card Sparse := by
    rw [hSparseCard]
    exact hcount
  let assign : O × RepairSupplyIndex d ↪ Sparse :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hassignCard)
  let fiberAt (output : O) (position : RepairSupplyIndex d) : Γ :=
    (assign (output, position)).1
  let suppliedHoles (output : O) (position : RepairSupplyIndex d) :
      ∀ c, Finset (A c) := model.holes (fiberAt output position)
  have hsparse (output : O) (position : RepairSupplyIndex d) (c : Leg) :
      base * (4 * (suppliedHoles output position c).card) ≤ Fintype.card (A c) := by
    have hmem := (assign (output, position)).2
    exact (model.mem_sparseIndices_iff base (fiberAt output position)).1 hmem c
  have hcertificate (output : O) :
      Nonempty (VariableRepairCertificate (P := P) (target := target)
        (suppliedHoles output)) :=
    exists_variableRepairCertificate relabelings hbase d
      (suppliedHoles output) (hsparse output) target hdepth
  let certificate (output : O) := Classical.choice (hcertificate output)
  let plans (output : O) := (certificate output).plan
  let pick : (Σ output, (plans output).Copy) ↪ Γ :=
    { toFun := fun occurrence ↦
        fiberAt occurrence.1 ((certificate occurrence.1).pick occurrence.2)
      inj' := by
        rintro ⟨leftOutput, leftOccurrence⟩ ⟨rightOutput, rightOccurrence⟩ heq
        have hassign :
            assign (leftOutput, (certificate leftOutput).pick leftOccurrence) =
              assign (rightOutput, (certificate rightOutput).pick rightOccurrence) := by
          apply Subtype.ext
          exact heq
        have hpair := assign.injective hassign
        have houtput : leftOutput = rightOutput := congrArg Prod.fst hpair
        subst rightOutput
        have hoccurrence : leftOccurrence = rightOccurrence :=
          (certificate leftOutput).pick.injective (congrArg Prod.snd hpair)
        subst rightOccurrence
        rfl }
  have hholes (occurrence : Σ output, (plans output).Copy) :
      (plans occurrence.1).holesAt occurrence.2 = model.holes (pick occurrence) := by
    calc
      (plans occurrence.1).holesAt occurrence.2 =
          suppliedHoles occurrence.1
            ((certificate occurrence.1).pick occurrence.2) := by
        simpa [plans] using (certificate occurrence.1).holesAt_eq occurrence.2
      _ = model.holes (pick occurrence) := rfl
  have hbroken (occurrence : Σ output, (plans output).Copy) :
      Restricts (family (pick occurrence))
        (P.box (fun c ↦ Finset.univ \
          (plans occurrence.1).holesAt occurrence.2 c)).realize := by
    rw [hholes occurrence]
    exact model.fiber_restricts (pick occurrence)
  refine ⟨plans, pick, hholes, ?_⟩
  exact RepairPlan.indexedDirectSum_repairPlans plans family pick hbroken

/-- Numerical complete-tree form of `exists_repairPlans_of_sparse_count`. -/
theorem exists_repairPlans_of_mul_budget_le_sparse
    (model : ModeledFiberFamily P family)
    {Relabel : Type u} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : UniformStructureRelabelings (G := Relabel) P)
    {O : Type u} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (A c))
    (hdepth : logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * sevenBranchBudget d ≤
      (model.sparseIndices base).card) :
    ∃ plans : O → RepairPlan P target,
      ∃ pick : (Σ output, (plans output).Copy) ↪ Γ,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 = model.holes (pick occurrence)) ∧
        Restricts (Tensor.indexedDirectSum family)
          (Tensor.indexedDirectSum (fun _output : O ↦ (P.box target).realize)) := by
  apply model.exists_repairPlans_of_sparse_count relabelings hbase d target hdepth
  simpa [Fintype.card_prod, card_repairSupplyIndex] using hcount

/-- Correct paper-facing finite MM endpoint for normalized cleaned fibers. -/
theorem degenerate_matrixMultiplicationDirectSum
    (model : ModeledFiberFamily P family)
    {Relabel : Type u} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : UniformStructureRelabelings (G := Relabel) P)
    {O : Type u} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (A c))
    (hdepth : logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * sevenBranchBudget d ≤
      (model.sparseIndices base).card)
    {Source : Leg → Type u}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source}
    (hfamily : Restricts T (Tensor.indexedDirectSum family))
    {m n p : ℕ}
    (hleaf : Restricts (P.box target).realize
      (matrixMultiplication (K := K) m n p)) :
    PolynomialDegenerates T
      (matrixMultiplicationDirectSum (ι := O) K
        (fun _ ↦ m) (fun _ ↦ n) (fun _ ↦ p)) := by
  obtain ⟨_plans, _pick, _hholes, hrepair⟩ :=
    model.exists_repairPlans_of_mul_budget_le_sparse
      relabelings hbase d target hdepth hcount
  exact PolynomialDegenerates.of_restricts_indexedDirectSum_matrixMultiplication K
    (hfamily.trans hrepair) (fun _output ↦ hleaf)

end ModeledFiberFamily

/-- Cleaned group fibers whose missing-label triple satisfies the finite hole-density condition. -/
noncomputable def sparseFiberGroups (grouping : P.LegGrouping Γ) (base : ℕ) : Finset Γ := by
  classical
  exact Finset.univ.filter fun γ ↦ ∀ c,
    base * (4 * (grouping.fiberHoles γ c).card) ≤ Fintype.card (A c)

@[simp] theorem mem_sparseFiberGroups_iff
    (grouping : P.LegGrouping Γ) (base : ℕ) (γ : Γ) :
    γ ∈ sparseFiberGroups grouping base ↔ ∀ c,
      base * (4 * (grouping.fiberHoles γ c).card) ≤ Fintype.card (A c) := by
  classical
  simp [sparseFiberGroups]

/-- A cardinality bound on sparse cleaned fibers supplies disjoint varying repair plans for every
requested output copy.

The domain `O × RepairSupplyIndex d` records one complete repair supply per output.  Its single
embedding into the subtype of sparse fibers enforces global no-reuse. -/
theorem exists_repairPlans_of_sparseFiberGroups
    {Relabel : Type u} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : UniformStructureRelabelings (G := Relabel) P)
    (grouping : P.LegGrouping Γ)
    {O : Type u} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (A c))
    (hdepth : logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card (O × RepairSupplyIndex d) ≤
      (sparseFiberGroups grouping base).card) :
    ∃ plans : O → RepairPlan P target,
      ∃ pick : (Σ output, (plans output).Copy) ↪ Γ,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 =
            grouping.fiberHoles (pick occurrence)) ∧
        Restricts
          (Tensor.indexedDirectSum (fun γ : Γ ↦ (grouping.fiber γ).realize))
          (Tensor.indexedDirectSum (fun _output : O ↦ (P.box target).realize)) := by
  classical
  let Sparse := { γ // γ ∈ sparseFiberGroups grouping base }
  have hSparseCard : Fintype.card Sparse = (sparseFiberGroups grouping base).card := by
    exact Fintype.card_coe _
  have hassignCard : Fintype.card (O × RepairSupplyIndex d) ≤ Fintype.card Sparse := by
    simpa [hSparseCard] using hcount
  let assign : O × RepairSupplyIndex d ↪ Sparse :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hassignCard)
  let groupAt (output : O) (position : RepairSupplyIndex d) : Γ :=
    (assign (output, position)).1
  let suppliedHoles (output : O) (position : RepairSupplyIndex d) :
      ∀ c, Finset (A c) :=
    grouping.fiberHoles (groupAt output position)
  have hsparse (output : O) (position : RepairSupplyIndex d) (c : Leg) :
      base * (4 * (suppliedHoles output position c).card) ≤ Fintype.card (A c) := by
    have hmem := (assign (output, position)).2
    exact (mem_sparseFiberGroups_iff grouping base (groupAt output position)).1 hmem c
  have hcertificate (output : O) :
      Nonempty (VariableRepairCertificate (P := P) (target := target)
        (suppliedHoles output)) :=
    exists_variableRepairCertificate relabelings hbase d
      (suppliedHoles output) (hsparse output) target hdepth
  let certificate (output : O) := Classical.choice (hcertificate output)
  let plans (output : O) := (certificate output).plan
  let pick : (Σ output, (plans output).Copy) ↪ Γ :=
    { toFun := fun occurrence ↦
        groupAt occurrence.1 ((certificate occurrence.1).pick occurrence.2)
      inj' := by
        rintro ⟨leftOutput, leftOccurrence⟩ ⟨rightOutput, rightOccurrence⟩ heq
        have hassign :
            assign (leftOutput, (certificate leftOutput).pick leftOccurrence) =
              assign (rightOutput, (certificate rightOutput).pick rightOccurrence) := by
          apply Subtype.ext
          exact heq
        have hpair := assign.injective hassign
        have houtput : leftOutput = rightOutput := congrArg Prod.fst hpair
        subst rightOutput
        have hoccurrence : leftOccurrence = rightOccurrence :=
          (certificate leftOutput).pick.injective (congrArg Prod.snd hpair)
        subst rightOccurrence
        rfl }
  have hholes (occurrence : Σ output, (plans output).Copy) :
      (plans occurrence.1).holesAt occurrence.2 =
        grouping.fiberHoles (pick occurrence) := by
    calc
      (plans occurrence.1).holesAt occurrence.2 =
          suppliedHoles occurrence.1
            ((certificate occurrence.1).pick occurrence.2) := by
        simpa [plans] using (certificate occurrence.1).holesAt_eq occurrence.2
      _ = grouping.fiberHoles (pick occurrence) := rfl
  have hbroken (occurrence : Σ output, (plans output).Copy) :
      Restricts ((grouping.fiber (pick occurrence)).realize)
        (P.box (fun c ↦ Finset.univ \
          (plans occurrence.1).holesAt occurrence.2 c)).realize := by
    rw [hholes occurrence]
    exact grouping.fiber_restricts_box_compl_fiberHoles (pick occurrence)
  refine ⟨plans, pick, hholes, ?_⟩
  exact RepairPlan.indexedDirectSum_repairPlans plans
    (fun γ : Γ ↦ (grouping.fiber γ).realize) pick hbroken

/-- Numerical form of the sparse-fiber supply condition. -/
theorem exists_repairPlans_of_mul_budget_le_sparseFiberGroups
    {Relabel : Type u} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : UniformStructureRelabelings (G := Relabel) P)
    (grouping : P.LegGrouping Γ)
    {O : Type u} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (A c))
    (hdepth : logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * sevenBranchBudget d ≤
      (sparseFiberGroups grouping base).card) :
    ∃ plans : O → RepairPlan P target,
      ∃ pick : (Σ output, (plans output).Copy) ↪ Γ,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 =
            grouping.fiberHoles (pick occurrence)) ∧
        Restricts
          (Tensor.indexedDirectSum (fun γ : Γ ↦ (grouping.fiber γ).realize))
          (Tensor.indexedDirectSum (fun _output : O ↦ (P.box target).realize)) := by
  apply exists_repairPlans_of_sparseFiberGroups relabelings grouping hbase d target hdepth
  simpa [Fintype.card_prod, card_repairSupplyIndex] using hcount

/-- One-shot finite extraction endpoint: a cleaned grouped tensor with enough sparse fibers
degenerates to the requested number of identical rectangular matrix-multiplication tensors.

After this theorem, the repair side of a concrete laser proof consists only of the explicit
sparse-fiber cardinality bound and the intact typed-leaf restriction. -/
theorem groupedSparseFibers_degenerate_matrixMultiplicationDirectSum
    {Relabel : Type u} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : UniformStructureRelabelings (G := Relabel) P)
    (grouping : P.LegGrouping Γ)
    {O : Type u} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset (A c))
    (hdepth : logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * sevenBranchBudget d ≤
      (sparseFiberGroups grouping base).card)
    {U : Leg → Type u}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    {T : Tensor3 K U}
    (hgroups : Restricts T
      (Tensor.indexedDirectSum (fun γ : Γ ↦ (grouping.fiber γ).realize)))
    {m n p : ℕ}
    (hleaf : Restricts (P.box target).realize
      (matrixMultiplication (K := K) m n p)) :
    PolynomialDegenerates T
      (matrixMultiplicationDirectSum (ι := O) K
        (fun _ ↦ m) (fun _ ↦ n) (fun _ ↦ p)) := by
  obtain ⟨_plans, _pick, _hholes, hrepair⟩ :=
    exists_repairPlans_of_mul_budget_le_sparseFiberGroups
      relabelings grouping hbase d target hdepth hcount
  exact PolynomialDegenerates.of_restricts_indexedDirectSum_matrixMultiplication K
    (hgroups.trans hrepair) (fun _output ↦ hleaf)

end AlgebraicComplexity.HoleRepair
