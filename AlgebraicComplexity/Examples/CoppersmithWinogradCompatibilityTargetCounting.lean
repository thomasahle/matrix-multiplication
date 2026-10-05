/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetRepair
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityFixedTypeRepair
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetLoss
import AlgebraicComplexity.MatrixMultiplication.SparseRepairCounting

/-!
# Counting exact target-specific CW repair supplies

This module is the quantitative boundary immediately above the finite compatibility/repair
semantics.  It proves:

* selection of one full tagged/oriented coarse-cell type at only polynomial loss;
* conversion of aggregate target-alphabet hole incidence into a simultaneous sparse count;
* absorption of a half-density sparse threshold at the constant factor `2`.

The actual competitor estimate enters only as the displayed aggregate-incidence inequality.  It
cannot be removed: an arbitrary projection-closed final support may be empty.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u v

/-! ## Largest full tagged/oriented cell type -/

/-- Exact largest-type selection for the full finite cell word, including the region tag and all
three oriented coarse digits. -/
theorem exists_reference_card_le_fullCellTypes_mul_fixedTargetCellType
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hne : coarseKept.Nonempty) :
    ∃ reference ∈ coarseKept,
      coarseKept.card ≤
        (coarseKept.image fun coarse ↦
          WordType.multiplicity
            (cwOrientedFiniteCellSequence depth n partAt sigma coarse)).card *
          (cwFixedTargetCellTypeCoarseSupport
            depth n partAt sigma coarseKept reference).card := by
  classical
  let f := fun coarse ↦ WordType.multiplicity
    (cwOrientedFiniteCellSequence depth n partAt sigma coarse)
  obtain ⟨reference, hreference, hcard⟩ :=
    exists_mem_card_le_card_image_mul_card_filter_reference coarseKept f hne
  refine ⟨reference, hreference, ?_⟩
  have hfixed :
      cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma coarseKept reference =
        coarseKept.filter (fun coarse ↦ f reference = f coarse) := by
    ext coarse
    simp only [mem_cwFixedTargetCellTypeCoarseSupport_iff,
      Finset.mem_filter, f]
  rw [hfixed]
  simpa only [f] using hcard

/-- The full cell types occurring in a retained coarse family lie in the standard finite set of
all empirical types of the same length. -/
theorem card_cwFullCellTypesInCoarseSupport_le_types
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))) :
    (coarseKept.image fun coarse ↦
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma coarse)).card ≤
      (WordType.types (CWOrientedCoarseCell Part depth) (n + 1)).card := by
  classical
  apply Finset.card_le_card
  intro cellType hcellType
  obtain ⟨coarse, _hcoarse, rfl⟩ := Finset.mem_image.mp hcellType
  exact WordType.multiplicity_mem_types
    (cwOrientedFiniteCellSequence depth n partAt sigma coarse)

/-- Selecting a full target-cell type costs at most the usual finite-alphabet polynomial. -/
theorem exists_reference_card_le_polynomial_mul_fixedTargetCellType
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hne : coarseKept.Nonempty) :
    ∃ reference ∈ coarseKept,
      coarseKept.card ≤
        (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
          (cwFixedTargetCellTypeCoarseSupport
            depth n partAt sigma coarseKept reference).card := by
  obtain ⟨reference, hreference, hcount⟩ :=
    exists_reference_card_le_fullCellTypes_mul_fixedTargetCellType
      depth n partAt sigma coarseKept hne
  refine ⟨reference, hreference, hcount.trans ?_⟩
  apply Nat.mul_le_mul_right
  exact (card_cwFullCellTypesInCoarseSupport_le_types
    depth n partAt sigma coarseKept).trans
      (WordType.card_types_le (CWOrientedCoarseCell Part depth) (n + 1))

/-- Proportional/rational form: if the sample count is `mass*r`, full-cell-type selection loses
the explicit polynomial `(mass*r+1)^|cell alphabet|`. -/
theorem exists_reference_card_le_proportional_mul_fixedTargetCellType
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n mass r : ℕ) (partAt : Fin (n + 1) → Part)
    (sigma : Orientation)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hne : coarseKept.Nonempty) (hsamples : n + 1 = mass * r) :
    ∃ reference ∈ coarseKept,
      coarseKept.card ≤
        (mass * r + 1) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
          (cwFixedTargetCellTypeCoarseSupport
            depth n partAt sigma coarseKept reference).card := by
  obtain ⟨reference, hreference, hcount⟩ :=
    exists_reference_card_le_polynomial_mul_fixedTargetCellType
      depth n partAt sigma coarseKept hne
  refine ⟨reference, hreference, ?_⟩
  have hn : n + 2 = mass * r + 1 := by omega
  simpa only [hn] using hcount

/-- Real-valued full-cell-type selection loss. -/
noncomputable def cwFullCellTypeSelectionLoss
    (Part : Type v) [Fintype Part] (depth n : ℕ) : ℝ :=
  (((n + 2 : ℕ) : ℝ)) ^ Fintype.card (CWOrientedCoarseCell Part depth)

/-- The full tagged/oriented type-selection loss is subexponential. -/
theorem cwFullCellTypeSelectionLoss_subexponential
    (Part : Type v) [Fintype Part] (depth : ℕ) :
    Growth.Subexponential (cwFullCellTypeSelectionLoss Part depth) := by
  let degree := Fintype.card (CWOrientedCoarseCell Part depth)
  have hmajor := (Growth.Subexponential.natCast_succ_pow degree).const_mul
    (show (0 : ℝ) ≤ 2 ^ degree by positivity)
  apply hmajor.mono
  · intro n
    unfold cwFullCellTypeSelectionLoss
    positivity
  · intro n
    unfold cwFullCellTypeSelectionLoss
    dsimp [degree] at hmajor ⊢
    have hbase : (((n + 2 : ℕ) : ℝ)) ≤
        2 * (((n + 1 : ℕ) : ℝ)) := by
      push_cast
      linarith
    calc
      (((n + 2 : ℕ) : ℝ)) ^ degree ≤
          (2 * (((n + 1 : ℕ) : ℝ))) ^ degree := by
        exact pow_le_pow_left₀ (by positivity) hbase _
      _ = 2 ^ degree * (((n + 1 : ℕ) : ℝ)) ^ degree := by
        rw [mul_pow]

/-! ## Aggregate holes imply many exact sparse fibers -/

/-- CW specialization of the division-free three-leg aggregate-hole bound.  Its hypotheses are
the exact competitor/counting quantities expected from a rational certificate evaluator. -/
theorem card_fixedTargetCellType_sub_budgets_le_sparse
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (base : ℕ) (budget : Leg → ℕ)
    (haggregate : ∀ c,
      base * 4 *
          ∑ coarse : cwFixedTargetCellTypeCoarseSupport
              depth n partAt sigma coarseKept reference,
            ((cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
              targets coarseKept finalSupport hclosed hExact G hgroup reference).holes
                coarse c).card ≤
        budget c *
          (cwExactTargetCoarseFiberParts
            partAt sigma targets reference c).card) :
    Fintype.card (cwFixedTargetCellTypeCoarseSupport
        depth n partAt sigma coarseKept reference) -
        (budget .X + budget .Y + budget .Z) ≤
      (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
        targets coarseKept finalSupport hclosed hExact G hgroup reference base).card := by
  let model := cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
    targets coarseKept finalSupport hclosed hExact G hgroup reference
  apply model.card_sub_budgets_le_card_sparseIndices base budget
  intro c
  simpa [model, Fintype_card_BoxPart] using haggregate c

/-- If the aggregate dense-fiber budgets consume at most half of one fixed full-cell type, then
at least half of that type is simultaneously sparse.  Thus sparse-threshold selection costs only
the fixed factor `2`. -/
theorem card_fixedTargetCellType_le_two_mul_card_sparse
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (base : ℕ) (budget : Leg → ℕ)
    (haggregate : ∀ c,
      base * 4 *
          ∑ coarse : cwFixedTargetCellTypeCoarseSupport
              depth n partAt sigma coarseKept reference,
            ((cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
              targets coarseKept finalSupport hclosed hExact G hgroup reference).holes
                coarse c).card ≤
        budget c *
          (cwExactTargetCoarseFiberParts
            partAt sigma targets reference c).card)
    (hhalf : 2 * (budget .X + budget .Y + budget .Z) ≤
      Fintype.card (cwFixedTargetCellTypeCoarseSupport
        depth n partAt sigma coarseKept reference)) :
    Fintype.card (cwFixedTargetCellTypeCoarseSupport
        depth n partAt sigma coarseKept reference) ≤
      2 * (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
        targets coarseKept finalSupport hclosed hExact G hgroup reference base).card := by
  have hsparse := card_fixedTargetCellType_sub_budgets_le_sparse
    K q partAt term hmultiplicity sigma targets coarseKept finalSupport hclosed
      hExact G hgroup reference base budget haggregate
  omega

/-- Combining largest-type selection and the half-density estimate exposes the complete finite
selection loss: the polynomial number of full cell types times the fixed factor `2`. -/
theorem card_coarseKept_le_typeLoss_mul_two_mul_sparse
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    (htype : coarseKept.card ≤
      (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
        Fintype.card (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma coarseKept reference))
    (base : ℕ) (budget : Leg → ℕ)
    (haggregate : ∀ c,
      base * 4 *
          ∑ coarse : cwFixedTargetCellTypeCoarseSupport
              depth n partAt sigma coarseKept reference,
            ((cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
              targets coarseKept finalSupport hclosed hExact G hgroup reference).holes
                coarse c).card ≤
        budget c *
          (cwExactTargetCoarseFiberParts
            partAt sigma targets reference c).card)
    (hhalf : 2 * (budget .X + budget .Y + budget .Z) ≤
      Fintype.card (cwFixedTargetCellTypeCoarseSupport
        depth n partAt sigma coarseKept reference)) :
    coarseKept.card ≤
      (2 * (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth)) *
        (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
          targets coarseKept finalSupport hclosed hExact G hgroup reference base).card := by
  have hfixed := card_fixedTargetCellType_le_two_mul_card_sparse
    K q partAt term hmultiplicity sigma targets coarseKept finalSupport hclosed
      hExact G hgroup reference base budget haggregate hhalf
  calc
    coarseKept.card ≤
        (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
          Fintype.card (cwFixedTargetCellTypeCoarseSupport
            depth n partAt sigma coarseKept reference) := htype
    _ ≤ (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
          (2 * (cwSparseTargetCellTypeAddresses K q partAt term hmultiplicity sigma
            targets coarseKept finalSupport hclosed hExact G hgroup reference base).card) :=
      Nat.mul_le_mul_left _ hfixed
    _ = _ := by ring

/-- The combined full-cell-type and half-density sparse-selection loss is subexponential. -/
theorem cwFullCellTypeAndSparseSelectionLoss_subexponential
    (Part : Type v) [Fintype Part] (depth : ℕ) :
    Growth.Subexponential
      (fun n ↦ 2 * cwFullCellTypeSelectionLoss Part depth n) :=
  (cwFullCellTypeSelectionLoss_subexponential Part depth).const_mul (by norm_num)

/-! ## Exact target-alphabet size and repair-budget growth -/

/-- Cardinality of a positive word over a finite alphabet. -/
theorem fintypeCard_positiveWord (I : Type v) [Fintype I] (n : ℕ) :
    Fintype.card (PositiveWord I n) = Fintype.card I ^ (n + 1) := by
  calc
    Fintype.card (PositiveWord I n) = Fintype.card (Fin (n + 1) → I) :=
      Fintype.card_congr (positiveWordEquiv I n)
    _ = Fintype.card I ^ (n + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin]

/-- The complete fine CW label alphabet has exactly three choices at each of its
`2^depth * (n+1)` leaf positions. -/
theorem fintypeCard_cwFineBlockWord (depth n : ℕ) :
    Fintype.card
        (PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) =
      3 ^ (2 ^ depth * (n + 1)) := by
  rw [fintypeCard_positiveWord, fintypeCard_positiveWord]
  have htwo : 2 ^ depth - 1 + 1 = 2 ^ depth :=
    Nat.sub_add_cancel Nat.one_le_two_pow
  rw [htwo, show Fintype.card CWBlock = 3 by rfl]
  rw [← pow_mul]

/-- Every exact target-specific leg alphabet is bounded by the full fine-label alphabet. -/
theorem card_cwExactTargetCoarseFiberParts_le_three_pow
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) (c : Leg) :
    (cwExactTargetCoarseFiberParts partAt sigma targets reference c).card ≤
      3 ^ (2 ^ depth * (n + 1)) := by
  calc
    (cwExactTargetCoarseFiberParts partAt sigma targets reference c).card ≤
        Fintype.card
          (PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :=
      Finset.card_le_univ _
    _ = 3 ^ (2 ^ depth * (n + 1)) :=
      fintypeCard_cwFineBlockWord depth n

/-- Rational/proportional specialization of the exact target-alphabet bound. -/
theorem card_cwExactTargetCoarseFiberParts_le_proportional_three_pow
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n mass r : ℕ} (partAt : Fin (n + 1) → Part)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hsamples : n + 1 = mass * r) (c : Leg) :
    (cwExactTargetCoarseFiberParts partAt sigma targets reference c).card ≤
      3 ^ ((2 ^ depth * mass) * r) := by
  simpa only [hsamples, mul_assoc] using
    card_cwExactTargetCoarseFiberParts_le_three_pow
      partAt sigma targets reference c

/-- Scaling the exponent of `3^r` by a fixed width scales its ceiling-log repair depth by at
most the same width. -/
theorem clog_add_two_three_pow_mul_le
    (width r : ℕ) :
    Nat.clog (r + 2) (3 ^ (width * r)) ≤
      width * HoleRepair.interfaceRepairDepth r := by
  let d := HoleRepair.interfaceRepairDepth r
  have hbase : 1 < r + 2 := by omega
  have hsingle : 3 ^ r ≤ (r + 2) ^ d := by
    exact Nat.le_pow_clog hbase (3 ^ r)
  apply Nat.clog_le_of_le_pow
  calc
    3 ^ (width * r) = (3 ^ r) ^ width := by
      rw [Nat.mul_comm width r, pow_mul]
    _ ≤ ((r + 2) ^ d) ^ width :=
      Nat.pow_le_pow_left hsingle width
    _ = (r + 2) ^ (width * d) := by
      rw [Nat.mul_comm width d, pow_mul]

/-- Any three-leg target whose leg sizes are bounded by `3^(width*r)` has repair depth at most
`3*width*interfaceRepairDepth r` when the shrink base is `r+2`. -/
theorem logarithmicRepairDepth_le_three_mul_width
    {A : Leg → Type v} [∀ c, Fintype (A c)]
    (target : ∀ c, Finset (A c)) (width r : ℕ)
    (hcard : ∀ c, (target c).card ≤ 3 ^ (width * r)) :
    HoleRepair.logarithmicRepairDepth (r + 2) target ≤
      3 * width * HoleRepair.interfaceRepairDepth r := by
  have hleg (c : Leg) :
      Nat.clog (r + 2) (target c).card ≤
        width * HoleRepair.interfaceRepairDepth r :=
    (Nat.clog_mono_right (r + 2) (hcard c)).trans
      (clog_add_two_three_pow_mul_le width r)
  unfold HoleRepair.logarithmicRepairDepth
  rw [Tensor.sum_leg]
  calc
    _ ≤ width * HoleRepair.interfaceRepairDepth r +
          width * HoleRepair.interfaceRepairDepth r +
          width * HoleRepair.interfaceRepairDepth r :=
      add_le_add (add_le_add (hleg .X) (hleg .Y)) (hleg .Z)
    _ = 3 * width * HoleRepair.interfaceRepairDepth r := by ring

/-- The actual complete repair supply is bounded by the explicit proportional majorant whenever
the target-cardinality estimate has supplied the displayed depth bound. -/
theorem sevenBranchBudget_logarithmicRepairDepth_le_targetRepairBudget
    {A : Leg → Type v} [∀ c, Fintype (A c)]
    (target : ∀ c, Finset (A c)) (width r : ℕ)
    (hdepth : HoleRepair.logarithmicRepairDepth (r + 2) target ≤
      3 * width * HoleRepair.interfaceRepairDepth r) :
    (HoleRepair.sevenBranchBudget
        (HoleRepair.logarithmicRepairDepth (r + 2) target) : ℕ) ≤
      cwTargetRepairBudgetLoss width r := by
  unfold cwTargetRepairBudgetLoss
  exact_mod_cast HoleRepair.sevenBranchBudget_monotone hdepth

/-! ## Canonical target/depth/output packaging -/

/-- The exact CW target model admits the canonical maximal repair construction: the depth is the
literal logarithmic depth of `target`, and the output type has one element per complete
seven-branch supply in the sparse address family. -/
theorem exists_cwTargetCellType_maximalRepairPlans
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (finalSupport : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hclosed : IsProjectionClosed
      (cwFineSupportOverCoarseSupport
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support coarseKept)
      finalSupport Finset.univ)
    (hExact : ∀ address ∈ finalSupport, ∀ logicalLeg,
      (cwExactInterfaceCompatibilityModel depth n partAt).MatchesExact
        (logicalAddress sigma address) logicalLeg
        (targets.exactProfile logicalLeg))
    (G : ((cwSelectedExactInterfaceTerm K q term hmultiplicity).withSupport
      finalSupport).LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hgroup : ∀ address,
      G.group address = cwExactInterfaceCoarseGroup depth n address)
    (reference : BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n))
    {base : ℕ} (hbase : 1 < base)
    (target : ∀ c, Finset (BoxPart
      (cwExactTargetCoarseFiberParts partAt sigma targets reference) c)) :
    let model := cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
      targets coarseKept finalSupport hclosed hExact G hgroup reference
    ∃ plans : ULift.{0} (Fin (model.maximalRepairOutputCount base target)) →
        Tensor.RepairPlan
          (compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
            (cwExactTargetCoarseFiberParts partAt sigma targets reference)) target,
      ∃ pick : (Σ output, (plans output).Copy) ↪
          cwFixedTargetCellTypeCoarseSupport
            depth n partAt sigma coarseKept reference,
        (∀ occurrence : Σ output, (plans output).Copy,
          (plans occurrence.1).holesAt occurrence.2 =
            model.holes (pick occurrence)) ∧
        Restricts
          (Tensor.indexedDirectSum
            (fun coarse : cwFixedTargetCellTypeCoarseSupport
                depth n partAt sigma coarseKept reference ↦
              (G.fiber coarse.1).realize))
          (Tensor.indexedDirectSum
            (fun _output : ULift.{0} (Fin (model.maximalRepairOutputCount base target)) ↦
              ((compactBox (cwSelectedExactInterfaceTerm K q term hmultiplicity)
                (cwExactTargetCoarseFiberParts partAt sigma targets reference)).box
                  target).realize)) := by
  classical
  let model := cwTargetCellTypeCleanedModel K q partAt term hmultiplicity sigma
    targets coarseKept finalSupport hclosed hExact G hgroup reference
  let CellPerm := cwReferenceCellPermSubgroup depth n partAt sigma reference
  letI : Fintype CellPerm := Fintype.ofFinite _
  letI : DecidableEq CellPerm := Classical.decEq _
  letI : Fintype CellPermᵐᵒᵖ :=
    Fintype.ofEquiv CellPerm MulOpposite.opEquiv
  letI : DecidableEq CellPermᵐᵒᵖ := Classical.decEq _
  exact model.exists_maximalRepairPlans
    (cwExactTargetUniformStructureRelabelings
      K q partAt sigma targets term hmultiplicity reference) hbase target

end AlgebraicComplexity.Examples
