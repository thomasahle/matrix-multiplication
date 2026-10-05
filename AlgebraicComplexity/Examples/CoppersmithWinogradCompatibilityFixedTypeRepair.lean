/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityFiberNormalization

/-!
# Fixed-type CW compatibility fibers and sparse repair supply

Hash isolation produces a finite direct sum indexed by retained coarse constituent addresses.
The paper next keeps one joint multiplicity type.  This file makes that finite pigeonhole step
exact, normalizes the chosen type to one compact reference tensor, and identifies the explicit
sparse-address count with the generic varying-hole repair API.

No entropy or numerical certificate arithmetic is repeated here.  A generated evaluator only
has to bound the cardinality of the concrete `cwSparseFixedJointTypeAddresses` finset.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-! ## A reusable finite largest-fiber estimate -/

/-- Some member of a nonempty finite set has a fiber at least as large as the average fiber.
The division-free form is convenient for exact certificate checkers. -/
theorem exists_mem_card_le_card_image_mul_card_filter
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (hs : s.Nonempty) :
    ∃ reference ∈ s,
      s.card ≤ (s.image f).card *
        (s.filter fun x ↦ f x = f reference).card := by
  classical
  obtain ⟨reference, hreference, hmax⟩ :=
    Finset.exists_max_image s
      (fun x ↦ (s.filter fun y ↦ f y = f x).card) hs
  refine ⟨reference, hreference, ?_⟩
  have hpartition :
      s.card = ∑ value ∈ s.image f, (s.filter fun x ↦ f x = value).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro hx
      exact ⟨hx, x, hx, rfl⟩
    · rintro ⟨hx, _⟩
      exact hx
  rw [hpartition]
  calc
    (∑ value ∈ s.image f, (s.filter fun x ↦ f x = value).card) ≤
        ∑ _value ∈ s.image f,
          (s.filter fun x ↦ f x = f reference).card := by
      apply Finset.sum_le_sum
      intro value hvalue
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hvalue
      exact hmax x hx
    _ = (s.image f).card *
        (s.filter fun x ↦ f x = f reference).card := by simp

/-- Symmetric-orientation form of `exists_mem_card_le_card_image_mul_card_filter`.  Providing the
predicate in both orientations avoids unfolding dependent client alphabets merely to commute an
equality inside a `Finset.filter`. -/
theorem exists_mem_card_le_card_image_mul_card_filter_reference
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (hs : s.Nonempty) :
    ∃ reference ∈ s,
      s.card ≤ (s.image f).card *
        (s.filter fun x ↦ f reference = f x).card := by
  simpa only [eq_comm] using
    exists_mem_card_le_card_image_mul_card_filter s f hs

/-! ## Fixed joint multiplicity fibers -/

/-- Retained coarse addresses having the same joint constituent multiplicity as `reference`. -/
noncomputable def cwFixedJointTypeCoarseSupport (depth n : ℕ)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    Finset (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) := by
  classical
  exact coarseKept.filter fun coarse ↦
    WordType.multiplicity (cwCoarseAddressSequence depth n reference) =
      WordType.multiplicity (cwCoarseAddressSequence depth n coarse)

@[simp] theorem mem_cwFixedJointTypeCoarseSupport_iff
    (depth n : ℕ)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference coarse : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    coarse ∈ cwFixedJointTypeCoarseSupport depth n coarseKept reference ↔
      coarse ∈ coarseKept ∧
        WordType.multiplicity (cwCoarseAddressSequence depth n reference) =
          WordType.multiplicity (cwCoarseAddressSequence depth n coarse) := by
  classical
  simp [cwFixedJointTypeCoarseSupport]

/-- Exact largest-joint-type selection inside an arbitrary retained coarse support. -/
theorem exists_reference_card_le_jointTypes_mul_fixedJointType
    (depth n : ℕ)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hne : coarseKept.Nonempty) :
    ∃ reference ∈ coarseKept,
      coarseKept.card ≤
        (coarseKept.image fun coarse ↦
          WordType.multiplicity
            (cwCoarseAddressSequence depth n coarse)).card *
          (cwFixedJointTypeCoarseSupport depth n coarseKept reference).card := by
  simpa only [cwFixedJointTypeCoarseSupport, eq_comm] using
    exists_mem_card_le_card_image_mul_card_filter coarseKept
      (fun coarse ↦ WordType.multiplicity
        (cwCoarseAddressSequence depth n coarse)) hne

/-- The joint types occurring in a retained support are among all word types of the same length. -/
theorem card_cwJointTypesInCoarseSupport_le_types
    (depth n : ℕ)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))) :
    (coarseKept.image fun coarse ↦
      WordType.multiplicity (cwCoarseAddressSequence depth n coarse)).card ≤
      (WordType.types
        (BlockAddress (fun _c ↦ CWCoarseDigit depth)) (n + 1)).card := by
  classical
  apply Finset.card_le_card
  intro jointType hjointType
  obtain ⟨coarse, _hcoarse, rfl⟩ := Finset.mem_image.mp hjointType
  exact WordType.multiplicity_mem_types
    (cwCoarseAddressSequence depth n coarse)

/-- Selecting one joint type costs at most the standard polynomial number of empirical types. -/
theorem exists_reference_card_le_polynomial_mul_fixedJointType
    (depth n : ℕ)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hne : coarseKept.Nonempty) :
    ∃ reference ∈ coarseKept,
      coarseKept.card ≤
        (n + 2) ^ Fintype.card
          (BlockAddress (fun _c ↦ CWCoarseDigit depth)) *
          (cwFixedJointTypeCoarseSupport depth n coarseKept reference).card := by
  obtain ⟨reference, hreference, hcount⟩ :=
    exists_reference_card_le_jointTypes_mul_fixedJointType depth n coarseKept hne
  refine ⟨reference, hreference, hcount.trans ?_⟩
  apply Nat.mul_le_mul_right
  exact (card_cwJointTypesInCoarseSupport_le_types depth n coarseKept).trans
    (WordType.card_types_le
      (BlockAddress (fun _c ↦ CWCoarseDigit depth)) (n + 1))

/-! ## Exact bridge to the compact varying-hole repair model -/

/-- The compact damaged-fiber model indexed by all retained addresses of the reference joint
type. -/
noncomputable def cwFixedJointTypeCleanedModel
    (K : Type) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)) :
    HoleRepair.ModeledFiberFamily
      (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
        (cwIdealCoarseFiberParts depth n reference))
      (fun coarse : cwFixedJointTypeCoarseSupport depth n coarseKept reference ↦
        (G.fiber coarse.1).realize) := by
  apply cwFixedTypeCleanedModeledFiberFamily
    K q term hmultiplicity coarseKept finalSupport hclosed G hgroup reference
      (fun coarse : cwFixedJointTypeCoarseSupport depth n coarseKept reference ↦ coarse.1)
  · intro coarse
    exact (mem_cwFixedJointTypeCoarseSupport_iff
      depth n coarseKept reference coarse.1).mp coarse.2 |>.1
  · intro coarse
    exact (mem_cwFixedJointTypeCoarseSupport_iff
      depth n coarseKept reference coarse.1).mp coarse.2 |>.2

/-- The full grouped cleanup direct sum restricts to the subfamily of one fixed joint type.
This is why joint-type pigeonholing may safely be performed after hash isolation. -/
theorem cwGroupedFibers_restricts_fixedJointType
    (K : Type) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))}
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)) :
    Restricts
      (Tensor.indexedDirectSum (fun coarse : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦
          (G.fiber coarse).realize))
      (Tensor.indexedDirectSum
        (fun coarse : cwFixedJointTypeCoarseSupport depth n coarseKept reference ↦
          (G.fiber coarse.1).realize)) := by
  exact Tensor.Restricts.indexedDirectSum_subfamily
    (fun coarse : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦
        (G.fiber coarse).realize)
    (cwFixedJointTypeCoarseSupport depth n coarseKept reference)

/-- Fixed-type addresses whose explicit cleanup holes satisfy the repair density bound. -/
noncomputable def cwSparseFixedJointTypeAddresses
    (K : Type) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (base : ℕ) :
    Finset (cwFixedJointTypeCoarseSupport depth n coarseKept reference) :=
  (cwFixedJointTypeCleanedModel K q term hmultiplicity coarseKept finalSupport
    hclosed G hgroup reference).sparseIndices base

/-- Membership in the certificate-facing sparse-address set is exactly the three explicit CW
hole-cardinality inequalities.  The denominator is the actual compact ideal-fiber alphabet, not
the much larger ambient block alphabet. -/
@[simp] theorem mem_cwSparseFixedJointTypeAddresses_iff
    (K : Type) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (base : ℕ)
    (coarse : cwFixedJointTypeCoarseSupport depth n coarseKept reference) :
    coarse ∈ cwSparseFixedJointTypeAddresses K q term hmultiplicity coarseKept
        finalSupport hclosed G hgroup reference base ↔
      ∀ c,
        base * (4 * (cwFixedTypeCleanedFiberHoles K q term hmultiplicity G
          reference coarse.1
          ((mem_cwFixedJointTypeCoarseSupport_iff depth n coarseKept
            reference coarse.1).mp coarse.2).2 c).card) ≤
          (cwIdealCoarseFiberParts depth n reference c).card := by
  classical
  rw [cwSparseFixedJointTypeAddresses,
    HoleRepair.ModeledFiberFamily.mem_sparseIndices_iff]
  simp only [cwFixedJointTypeCleanedModel,
    cwFixedTypeCleanedModeledFiberFamily, Fintype_card_BoxPart]

/-- The sparse-address finset is literally the sparse-index supply consumed by generic varying
hole repair.  This named equality keeps numerical reconstruction clients independent of the
implementation of `ModeledFiberFamily`. -/
theorem card_cwSparseFixedJointTypeAddresses_eq_model_sparseIndices
    (K : Type) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (base : ℕ) :
    (cwSparseFixedJointTypeAddresses K q term hmultiplicity coarseKept
      finalSupport hclosed G hgroup reference base).card =
      ((cwFixedJointTypeCleanedModel K q term hmultiplicity coarseKept finalSupport
        hclosed G hgroup reference).sparseIndices base).card :=
  rfl

/-- One certificate-facing sparse-address count now constructs all varying repair plans and
assembles the cleaned fixed-type fibers into intact copies of the requested compact box. -/
theorem exists_cwFixedJointType_repairPlans_of_sparse_count
    (K : Type) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    {Relabel : Type} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : HoleRepair.UniformStructureRelabelings
      (G := Relabel)
      (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
        (cwIdealCoarseFiberParts depth n reference)))
    {O : Type} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset
      (BoxPart (cwIdealCoarseFiberParts depth n reference) c))
    (hdepth : HoleRepair.logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * HoleRepair.sevenBranchBudget d ≤
      (cwSparseFixedJointTypeAddresses K q term hmultiplicity coarseKept
        finalSupport hclosed G hgroup reference base).card) :
    ∃ plans : O → Tensor.RepairPlan
        (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
          (cwIdealCoarseFiberParts depth n reference)) target,
      ∃ pick : (Σ output, (plans output).Copy) ↪
          cwFixedJointTypeCoarseSupport depth n coarseKept reference,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 =
            (cwFixedJointTypeCleanedModel K q term hmultiplicity coarseKept
              finalSupport hclosed G hgroup reference).holes (pick occurrence)) ∧
        Restricts
          (Tensor.indexedDirectSum
            (fun coarse : cwFixedJointTypeCoarseSupport depth n coarseKept reference ↦
              (G.fiber coarse.1).realize))
          (Tensor.indexedDirectSum (fun _output : O ↦
            ((compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
              (cwIdealCoarseFiberParts depth n reference)).box target).realize)) := by
  exact (cwFixedJointTypeCleanedModel K q term hmultiplicity coarseKept finalSupport
    hclosed G hgroup reference).exists_repairPlans_of_mul_budget_le_sparse
      relabelings hbase d target hdepth hcount

/-- End-to-end finite semantic adapter for this layer.  Any tensor already restricted to the
whole grouped cleanup family restricts further to the repaired direct sum obtained from the
largest fixed joint type.  The only quantitative input is the explicit sparse-address count. -/
theorem exists_cwGroupedCleanup_repairedFixedJointType_of_sparse_count
    (K : Type) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    {S : Leg → Type} [∀ c, AddCommMonoid (S c)] [∀ c, Module K (S c)]
    (source : Tensor3 K S)
    (hsource : Restricts source
      (Tensor.indexedDirectSum (fun coarse : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦
          (G.fiber coarse).realize)))
    {Relabel : Type} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : HoleRepair.UniformStructureRelabelings
      (G := Relabel)
      (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
        (cwIdealCoarseFiberParts depth n reference)))
    {O : Type} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base) (d : ℕ)
    (target : ∀ c, Finset
      (BoxPart (cwIdealCoarseFiberParts depth n reference) c))
    (hdepth : HoleRepair.logarithmicRepairDepth base target ≤ d)
    (hcount : Fintype.card O * HoleRepair.sevenBranchBudget d ≤
      (cwSparseFixedJointTypeAddresses K q term hmultiplicity coarseKept
        finalSupport hclosed G hgroup reference base).card) :
    ∃ plans : O → Tensor.RepairPlan
        (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
          (cwIdealCoarseFiberParts depth n reference)) target,
      ∃ pick : (Σ output, (plans output).Copy) ↪
          cwFixedJointTypeCoarseSupport depth n coarseKept reference,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 =
            (cwFixedJointTypeCleanedModel K q term hmultiplicity coarseKept
              finalSupport hclosed G hgroup reference).holes (pick occurrence)) ∧
        Restricts source
          (Tensor.indexedDirectSum (fun _output : O ↦
            ((compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
              (cwIdealCoarseFiberParts depth n reference)).box target).realize)) := by
  obtain ⟨plans, pick, hholes, hrepair⟩ :=
    exists_cwFixedJointType_repairPlans_of_sparse_count
      K q term hmultiplicity coarseKept finalSupport hclosed G hgroup reference
        relabelings hbase d target hdepth hcount
  refine ⟨plans, pick, hholes, ?_⟩
  exact hsource.trans
    ((cwGroupedFibers_restricts_fixedJointType
      K q term hmultiplicity G coarseKept reference).trans hrepair)

end AlgebraicComplexity.Examples
