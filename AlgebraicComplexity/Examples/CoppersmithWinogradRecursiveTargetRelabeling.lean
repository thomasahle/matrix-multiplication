/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TransitiveUniformity
import AlgebraicComplexity.Examples.CoppersmithWinogradChunkPartitionCore
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetCounting
import AlgebraicComplexity.MatrixMultiplication.InterfaceHoleRepair
import AlgebraicComplexity.Tensor.PartitionedBoxRetyping

set_option autoImplicit false

/-!
# Uniform relabelings of recursive Coppersmith--Winograd target alphabets

An exact recursive target alphabet is a conditional type class on all labelled child
occurrences, not on paired parent positions.  Its natural finite symmetry group is therefore the
stabilizer of the full tagged/oriented cell word on the doubled occurrence set.  This module
constructs that group, decodes its action back to native parent chunks, and proves that the action
is transitive on every exact target-leg alphabet.

There is one explicit geometric premise, and it is discharged downstream.  A permutation of
doubled child chunks must lift to a structure relabeling of the nested parent-chunk power;
`CWRecursiveChildOccurrenceRelabelingLift` states exactly that lift, and the constructor below
takes it as a hypothesis so this module stays independent of the route used to prove it.  That
proof is `cwRecursiveChildOccurrenceRelabelingLift_holds` in
`Examples.CoppersmithWinogradParentChildChunkPower`, which discharges the premise for every
permutation of labelled child occurrences -- not only for stabilizer elements -- by presenting
the parent power and the doubled child power as exact legwise reindexes of one common external
square.  Given the premise, the final constructor packages the proved finite uniform actions as
the `HoleRepair.UniformStructureRelabelings` consumed by sparse repair.

No hole estimate, survivor count, tensor degeneration, or certificate-specific datum occurs here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-! ## The doubled tagged-cell stabilizer -/

/-- Permutations of labelled child occurrences which preserve every tagged/oriented finite cell
of the recursive reference address. -/
def cwRecursiveReferenceCellPermSubgroup
    {Part : Type v} [Fintype Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (reference : CWRecursiveCoarseAddress depth n) :
    Subgroup (Equiv.Perm (Fin ((n + 1) + (n + 1)))) where
  carrier := {tau |
    cwRecursiveOrientedFiniteCellSequence depth n partAt sigma reference ∘ tau =
      cwRecursiveOrientedFiniteCellSequence depth n partAt sigma reference}
  one_mem' := by
    funext occurrence
    rfl
  mul_mem' := by
    intro left right hleft hright
    funext occurrence
    have hl := congrFun hleft (right occurrence)
    have hr := congrFun hright occurrence
    exact hl.trans hr
  inv_mem' := by
    intro tau htau
    funext occurrence
    have h := congrFun htau (tau.symm occurrence)
    simpa using h.symm

/-! ## Decode occurrence permutations back to native parent labels -/

/-- Permute the doubled labelled children of a native parent word and join them back into native
parent chunks. -/
noncomputable def cwRecursiveChildOccurrencePartEquiv (depth n : ℕ)
    (tau : Equiv.Perm (Fin ((n + 1) + (n + 1)))) :
    Equiv.Perm
      (PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :=
  (cwRecursiveLabelledChildrenEquiv depth n).trans
    ((Equiv.arrowCongr tau.symm (Equiv.refl _)).trans
      (cwRecursiveLabelledChildrenEquiv depth n).symm)

@[simp] theorem cwRecursiveLabelledChildrenEquiv_childOccurrencePartEquiv_apply
    (depth n : ℕ) (tau : Equiv.Perm (Fin ((n + 1) + (n + 1))))
    (fine : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    cwRecursiveLabelledChildrenEquiv depth n
        (cwRecursiveChildOccurrencePartEquiv depth n tau fine) =
      cwRecursiveLabelledChildrenEquiv depth n fine ∘ tau := by
  simp [cwRecursiveChildOccurrencePartEquiv, Function.comp_def, Equiv.arrowCongr]

@[simp] theorem cwRecursiveChildOccurrencePartEquiv_one (depth n : ℕ) :
    cwRecursiveChildOccurrencePartEquiv depth n 1 = Equiv.refl _ := by
  apply Equiv.ext
  intro fine
  apply (cwRecursiveLabelledChildrenEquiv depth n).injective
  rw [cwRecursiveLabelledChildrenEquiv_childOccurrencePartEquiv_apply]
  rfl

/-- Decoded child-occurrence permutations act from left to right, matching
`PartitionedTensor.StructureRelabeling.trans`. -/
theorem cwRecursiveChildOccurrencePartEquiv_mul
    (depth n : ℕ)
    (left right : Equiv.Perm (Fin ((n + 1) + (n + 1)))) :
    cwRecursiveChildOccurrencePartEquiv depth n (left * right) =
      (cwRecursiveChildOccurrencePartEquiv depth n left).trans
        (cwRecursiveChildOccurrencePartEquiv depth n right) := by
  apply Equiv.ext
  intro fine
  apply (cwRecursiveLabelledChildrenEquiv depth n).injective
  rw [cwRecursiveLabelledChildrenEquiv_childOccurrencePartEquiv_apply]
  change cwRecursiveLabelledChildrenEquiv depth n fine ∘ (left * right) =
    cwRecursiveLabelledChildrenEquiv depth n
      (cwRecursiveChildOccurrencePartEquiv depth n right
        (cwRecursiveChildOccurrencePartEquiv depth n left fine))
  rw [
    cwRecursiveLabelledChildrenEquiv_childOccurrencePartEquiv_apply,
    cwRecursiveLabelledChildrenEquiv_childOccurrencePartEquiv_apply]
  rfl

/-! ## Exact-target invariance and transitivity -/

/-- The decoded doubled-occurrence action preserves every exact recursive target alphabet.

The weight-support hypotheses are exactly those used by the committed equivalence between the
native target alphabet and its finite conditional type class. -/
theorem cwRecursiveExactTargetFiberParts_childOccurrenceRelabel_iff
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (tau : cwRecursiveReferenceCellPermSubgroup
      depth n partAt sigma reference)
    (logicalLeg : Leg)
    (fine : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    cwRecursiveChildOccurrencePartEquiv depth n tau.1 fine ∈
        cwRecursiveExactTargetFiberParts
          partAt sigma targets reference (sigma logicalLeg) ↔
      fine ∈ cwRecursiveExactTargetFiberParts
        partAt sigma targets reference (sigma logicalLeg) := by
  classical
  rw [mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
      partAt sigma targets hsupported hcoarseSupported reference logicalLeg,
    mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
      partAt sigma targets hsupported hcoarseSupported reference logicalLeg,
    cwRecursiveLabelledChildrenEquiv_childOccurrencePartEquiv_apply,
    WordType.mem_conditionalTypeClass, WordType.mem_conditionalTypeClass]
  let source := cwRecursiveOrientedFiniteCellSequence
    depth n partAt sigma reference
  let children := cwRecursiveLabelledChildrenEquiv depth n fine
  have hjoint :
      WordType.jointWord source (children ∘ tau.1) =
        WordType.jointWord source children ∘ tau.1 := by
    funext occurrence
    apply Prod.ext
    · exact (congrFun tau.2 occurrence).symm
    · rfl
  have hmultiplicity :
      WordType.multiplicity (WordType.jointWord source (children ∘ tau.1)) =
        WordType.multiplicity (WordType.jointWord source children) := by
    rw [hjoint]
    simpa using WordType.multiplicity_reindex tau.1.symm
      (WordType.jointWord source children)
  change WordType.multiplicity
      (WordType.jointWord source (children ∘ tau.1)) = _ ↔
    WordType.multiplicity (WordType.jointWord source children) = _
  rw [hmultiplicity]

/-- Permutation induced on one compact exact-target part alphabet. -/
noncomputable def cwRecursiveExactTargetPartChildOccurrenceEquiv
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (tau : cwRecursiveReferenceCellPermSubgroup
      depth n partAt sigma reference)
    (physicalLeg : Leg) :
    Equiv.Perm
      (BoxPart
        (cwRecursiveExactTargetFiberParts
          partAt sigma targets reference) physicalLeg) :=
  invariantFinsetSubtypePerm
    (cwRecursiveChildOccurrencePartEquiv depth n tau.1)
    (cwRecursiveExactTargetFiberParts
      partAt sigma targets reference physicalLeg)
    (fun fine ↦ by
      simpa using
        (cwRecursiveExactTargetFiberParts_childOccurrenceRelabel_iff
          partAt sigma targets hsupported hcoarseSupported reference tau
            (sigma.symm physicalLeg) fine).symm)

@[simp] theorem cwRecursiveExactTargetPartChildOccurrenceEquiv_apply_val
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (tau : cwRecursiveReferenceCellPermSubgroup
      depth n partAt sigma reference)
    (physicalLeg : Leg)
    (fine : BoxPart
      (cwRecursiveExactTargetFiberParts
        partAt sigma targets reference) physicalLeg) :
    (cwRecursiveExactTargetPartChildOccurrenceEquiv
      partAt sigma targets hsupported hcoarseSupported reference tau
        physicalLeg fine).1 =
      cwRecursiveChildOccurrencePartEquiv depth n tau.1 fine.1 :=
  rfl

/-- The opposite doubled-cell stabilizer acts on one exact recursive target alphabet. -/
@[instance_reducible] noncomputable def cwRecursiveExactTargetPartMulAction
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg) :
    MulAction
      (cwRecursiveReferenceCellPermSubgroup
        depth n partAt sigma reference)ᵐᵒᵖ
      (BoxPart
        (cwRecursiveExactTargetFiberParts
          partAt sigma targets reference) physicalLeg) where
  smul g fine := cwRecursiveExactTargetPartChildOccurrenceEquiv
    partAt sigma targets hsupported hcoarseSupported reference g.unop
      physicalLeg fine
  one_smul fine := by
    apply Subtype.ext
    change cwRecursiveChildOccurrencePartEquiv depth n
        ((1 : cwRecursiveReferenceCellPermSubgroup
          depth n partAt sigma reference) :
          Equiv.Perm (Fin ((n + 1) + (n + 1)))) fine.1 = fine.1
    have hone :
        ((1 : cwRecursiveReferenceCellPermSubgroup
          depth n partAt sigma reference) :
          Equiv.Perm (Fin ((n + 1) + (n + 1)))) = 1 := rfl
    rw [hone]
    rw [cwRecursiveChildOccurrencePartEquiv_one]
    rfl
  mul_smul left right fine := by
    apply Subtype.ext
    change cwRecursiveChildOccurrencePartEquiv depth n
        (right.unop.1 * left.unop.1) fine.1 =
      cwRecursiveChildOccurrencePartEquiv depth n left.unop.1
        (cwRecursiveChildOccurrencePartEquiv depth n right.unop.1 fine.1)
    exact congrArg
      (fun e : Equiv.Perm
        (PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦ e fine.1)
      (cwRecursiveChildOccurrencePartEquiv_mul
        depth n right.unop.1 left.unop.1)

/-- The doubled tagged-cell stabilizer is transitive on every exact recursive target alphabet. -/
theorem cwRecursiveExactTargetPart_isPretransitive
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg) :
    letI := cwRecursiveExactTargetPartMulAction
      partAt sigma targets hsupported hcoarseSupported reference physicalLeg
    MulAction.IsPretransitive
      (cwRecursiveReferenceCellPermSubgroup
        depth n partAt sigma reference)ᵐᵒᵖ
      (BoxPart
        (cwRecursiveExactTargetFiberParts
          partAt sigma targets reference) physicalLeg) := by
  letI := cwRecursiveExactTargetPartMulAction
    partAt sigma targets hsupported hcoarseSupported reference physicalLeg
  constructor
  intro left right
  let logicalLeg := sigma.symm physicalLeg
  let source := cwRecursiveOrientedFiniteCellSequence
    depth n partAt sigma reference
  let children := fun
      (fine : PositiveWord
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    cwRecursiveLabelledChildrenEquiv depth n fine
  let jointSequence := fun
      (fine : PositiveWord
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    WordType.jointWord source (children fine)
  have hleft : children left.1 ∈
      WordType.conditionalTypeClass source
        (fun pair ↦ targets.exactProfile logicalLeg
          (cwOrientedCoarseCellToIndex pair.1) pair.2) := by
    apply (mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
      partAt sigma targets hsupported hcoarseSupported reference
        logicalLeg left.1).1
    rw [show sigma logicalLeg = physicalLeg by
      exact sigma.apply_symm_apply physicalLeg]
    exact left.2
  have hright : children right.1 ∈
      WordType.conditionalTypeClass source
        (fun pair ↦ targets.exactProfile logicalLeg
          (cwOrientedCoarseCellToIndex pair.1) pair.2) := by
    apply (mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
      partAt sigma targets hsupported hcoarseSupported reference
        logicalLeg right.1).1
    rw [show sigma logicalLeg = physicalLeg by
      exact sigma.apply_symm_apply physicalLeg]
    exact right.2
  have hjoint : WordType.multiplicity (jointSequence left.1) =
      WordType.multiplicity (jointSequence right.1) := by
    exact (WordType.mem_conditionalTypeClass.mp hleft).trans
      (WordType.mem_conditionalTypeClass.mp hright).symm
  let tau := WordType.positionPermOfSameMultiplicity
    (jointSequence right.1) (jointSequence left.1) hjoint.symm
  have hmap : jointSequence left.1 ∘ tau = jointSequence right.1 :=
    WordType.positionPermOfSameMultiplicity_map _ _ hjoint.symm
  have hcells : source ∘ tau = source := by
    funext occurrence
    exact congrArg Prod.fst (congrFun hmap occurrence)
  let stabilizerElement : cwRecursiveReferenceCellPermSubgroup
      depth n partAt sigma reference := ⟨tau, hcells⟩
  refine ⟨MulOpposite.op stabilizerElement, ?_⟩
  change cwRecursiveExactTargetPartChildOccurrenceEquiv
      partAt sigma targets hsupported hcoarseSupported reference
        stabilizerElement physicalLeg left = right
  apply Subtype.ext
  apply (cwRecursiveLabelledChildrenEquiv depth n).injective
  rw [cwRecursiveExactTargetPartChildOccurrenceEquiv_apply_val,
    cwRecursiveLabelledChildrenEquiv_childOccurrencePartEquiv_apply]
  funext occurrence
  exact congrArg Prod.snd (congrFun hmap occurrence)

noncomputable local instance cwRecursiveReferenceCellPermSubgroupFintype
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (reference : CWRecursiveCoarseAddress depth n) :
    Fintype (cwRecursiveReferenceCellPermSubgroup
      depth n partAt sigma reference) :=
  Fintype.ofFinite _

noncomputable local instance cwRecursiveReferenceCellPermSubgroupDecidableEq
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (reference : CWRecursiveCoarseAddress depth n) :
    DecidableEq (cwRecursiveReferenceCellPermSubgroup
      depth n partAt sigma reference) :=
  Classical.decEq _

/-- Exact uniform action on one recursive target-specific physical-leg alphabet. -/
noncomputable def cwRecursiveExactTargetUniformOnParts
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg) :
    let CellPerm := cwRecursiveReferenceCellPermSubgroup
      depth n partAt sigma reference
    letI : Fintype CellPerm := Fintype.ofFinite _
    letI : DecidableEq CellPerm := Classical.decEq _
    letI : Fintype CellPermᵐᵒᵖ :=
      Fintype.ofEquiv CellPerm MulOpposite.opEquiv
    letI : DecidableEq CellPermᵐᵒᵖ := Classical.decEq _
    HoleRepair.UniformOnParts CellPermᵐᵒᵖ
      (BoxPart
        (cwRecursiveExactTargetFiberParts
          partAt sigma targets reference) physicalLeg) := by
  let CellPerm := cwRecursiveReferenceCellPermSubgroup
    depth n partAt sigma reference
  letI : Fintype CellPerm := Fintype.ofFinite _
  letI : DecidableEq CellPerm := Classical.decEq _
  letI : Fintype CellPermᵐᵒᵖ :=
    Fintype.ofEquiv CellPerm MulOpposite.opEquiv
  letI : DecidableEq CellPermᵐᵒᵖ := Classical.decEq _
  letI := cwRecursiveExactTargetPartMulAction
    partAt sigma targets hsupported hcoarseSupported reference physicalLeg
  letI := cwRecursiveExactTargetPart_isPretransitive
    partAt sigma targets hsupported hcoarseSupported reference physicalLeg
  exact HoleRepair.UniformOnParts.ofPretransitiveMulAction

/-! ## The exact nested-power geometry premise and final package -/

/-- **Honest geometric gap.**  Every doubled tagged-cell permutation must lift to a genuine
structure relabeling of the nested parent-chunk positive power, acting on each leg through the
decoded child-occurrence permutation.

This premise says only that the advertised variable relabeling preserves the source tensor.  It
does not assume target invariance, transitivity, uniformity, a restriction, or a degeneration;
all of those finite target facts are constructed below. -/
def CWRecursiveChildOccurrenceRelabelingLift
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (sigma : Orientation) (reference : CWRecursiveCoarseAddress depth n) : Prop :=
  ∀ tau : cwRecursiveReferenceCellPermSubgroup
      depth n partAt sigma reference,
    ∃ r : ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n).StructureRelabeling,
      ∀ physicalLeg,
        r.partEquiv physicalLeg =
          cwRecursiveChildOccurrencePartEquiv depth n tau.1

/-- A doubled-child lift supplies one simultaneous structure-preserving uniform relabeling family
on all three compact recursive target alphabets. -/
noncomputable def cwRecursiveExactTargetUniformStructureRelabelings
    (K : Type) [CommRing K] (q : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (hLift : CWRecursiveChildOccurrenceRelabelingLift
      K q depth n partAt sigma reference) :
    let CellPerm := cwRecursiveReferenceCellPermSubgroup
      depth n partAt sigma reference
    letI : Fintype CellPerm := Fintype.ofFinite _
    letI : DecidableEq CellPerm := Classical.decEq _
    letI : Fintype CellPermᵐᵒᵖ :=
      Fintype.ofEquiv CellPerm MulOpposite.opEquiv
    letI : DecidableEq CellPermᵐᵒᵖ := Classical.decEq _
    HoleRepair.UniformStructureRelabelings
      (G := CellPermᵐᵒᵖ)
      (compactBox
        ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
        (cwRecursiveExactTargetFiberParts
          partAt sigma targets reference)) := by
  classical
  let CellPerm := cwRecursiveReferenceCellPermSubgroup
    depth n partAt sigma reference
  letI : Fintype CellPerm := Fintype.ofFinite _
  letI : DecidableEq CellPerm := Classical.decEq _
  letI : Fintype CellPermᵐᵒᵖ :=
    Fintype.ofEquiv CellPerm MulOpposite.opEquiv
  letI : DecidableEq CellPermᵐᵒᵖ := Classical.decEq _
  let full := (cwChunkPartitionedTensor K q (depth + 1)).positivePower n
  let target := cwRecursiveExactTargetFiberParts
    partAt sigma targets reference
  let ambient (g : CellPermᵐᵒᵖ) : full.StructureRelabeling :=
    (hLift g.unop).choose
  have ambient_partEquiv (g : CellPermᵐᵒᵖ) (physicalLeg : Leg) :
      (ambient g).partEquiv physicalLeg =
        cwRecursiveChildOccurrencePartEquiv depth n g.unop.1 :=
    (hLift g.unop).choose_spec physicalLeg
  let invariant (g : CellPermᵐᵒᵖ) (physicalLeg : Leg)
      (fine : PositiveWord
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
      fine ∈ target physicalLeg ↔
        (ambient g).partEquiv physicalLeg fine ∈ target physicalLeg := by
    rw [ambient_partEquiv]
    simpa [target] using
      (cwRecursiveExactTargetFiberParts_childOccurrenceRelabel_iff
        partAt sigma targets hsupported hcoarseSupported reference g.unop
          (sigma.symm physicalLeg) fine).symm
  let relabeling (g : CellPermᵐᵒᵖ) :=
    (ambient g).compactBox target (invariant g)
  refine
    { relabeling := relabeling
      uniform := fun physicalLeg ↦ cwRecursiveExactTargetUniformOnParts
        partAt sigma targets hsupported hcoarseSupported reference physicalLeg
      uniform_eq := ?_ }
  intro g physicalLeg
  apply Equiv.ext
  intro fine
  apply Subtype.ext
  change cwRecursiveChildOccurrencePartEquiv depth n g.unop.1 fine.1 =
    ((relabeling g).partEquiv physicalLeg fine).1
  rw [PartitionedTensor.StructureRelabeling.compactBox_partEquiv_apply_val]
  change cwRecursiveChildOccurrencePartEquiv depth n g.unop.1 fine.1 =
    (ambient g).partEquiv physicalLeg fine.1
  rw [ambient_partEquiv]

end AlgebraicComplexity.Examples
