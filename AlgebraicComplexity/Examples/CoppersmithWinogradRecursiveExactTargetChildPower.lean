/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradParentChildChunkPower
import AlgebraicComplexity.Tensor.PartitionedPermutePower
import AlgebraicComplexity.Tensor.PartitionedBoxEmbedding

set_option autoImplicit false

/-!
# Splitting the exact parent box into labelled child positions

This is the first operation of the Total-Weight manuscript's `hyp:intact-box`,
`better_bound/paper.tex:1219–1229`: split every parent position into its two labelled children.
The child-product notation follows [alman2025more],
`papers/sources/2404.16349/constituent.tex:488–495`.

We define the child selection by its actual quotient weights and exact cell/split-word counts.
Decoding the parent-to-child word equivalence preserves those equations. The existing exact
reindexes from a common external square then transport the selected tensors, including all
constituents, giving an isomorphism of the ambient boxes. Compact-box inclusion supplies the
restriction from the honestly sized compact source returned by repair.

Both occurrences remain labelled, including at a self-complementary child shape. No parent
complete-split profile is imposed, and no weight-support, reference-existence or counting
hypothesis is needed for this representation identity. Regrouping child states, identifying the
evaluator's heterogeneous child factors, and bounding or repairing holes remain separate steps.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- Read a doubled child-power word as complete-split words on the original labelled-occurrence
domain. All left children precede all right children. -/
def cwChildPowerSplitSequence (depth n : ℕ)
    (children : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) (n + n + 1)) :
    Fin ((n + 1) + (n + 1)) → SplitWord depth :=
  fun occurrence ↦ cwChunkSplitWord depth
    (positiveWordEquiv _ (n + n + 1) children
      (Fin.cast (cwDoubledChildLength n).symm occurrence))

/-- Splitting the parent tensor power reads exactly the labelled children used by the original
exact-target profile, with no permutation of the occurrence-counting domain. -/
theorem cwChildPowerSplitSequence_parentChildEquiv (depth n : ℕ)
    (parent : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    cwChildPowerSplitSequence depth n (cwParentChildChunkWordEquiv depth n parent) =
      positiveWordLabelledChildren (cwChunkSplitWord (depth + 1)) parent := by
  funext occurrence
  unfold cwChildPowerSplitSequence
  rw [positiveWordEquiv_cwParentChildChunkWordEquiv]
  have hcast : Fin.cast (cwDoubledChildLength n)
      (Fin.cast (cwDoubledChildLength n).symm occurrence) = occurrence := by
    simp
  rw [hcast]
  exact (cwChunkSplitWordEquiv depth).apply_symm_apply _

/-- Child-power labels with the prescribed quotient weights and full tagged-cell exact profile
on one physical leg. The counts use logical leg `sigma.symm physicalLeg`. -/
noncomputable def cwRecursiveExactChildParts
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n) (physicalLeg : Leg) :
    Finset (PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) (n + n + 1)) := by
  classical
  exact Finset.univ.filter fun children ↦
    (∀ occurrence,
      splitWordWeight (cwChildPowerSplitSequence depth n children occurrence) =
        (reference physicalLeg occurrence : ℕ)) ∧
    ∀ cell word,
      cellMultiplicity
          (cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma reference)
          (cwChildPowerSplitSequence depth n children) cell word =
        targets.exactProfile (sigma.symm physicalLeg) cell word

/-- Membership in the selected child alphabet is exactly the stated weight and joint-profile
equations; no support condition on the tensor is hidden in this alphabet predicate. -/
theorem mem_cwRecursiveExactChildParts_iff
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n) (physicalLeg : Leg)
    (children : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) (n + n + 1)) :
    children ∈ cwRecursiveExactChildParts partAt sigma targets reference physicalLeg ↔
      (∀ occurrence,
        splitWordWeight (cwChildPowerSplitSequence depth n children occurrence) =
          (reference physicalLeg occurrence : ℕ)) ∧
      ∀ cell word,
        cellMultiplicity
            (cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma reference)
            (cwChildPowerSplitSequence depth n children) cell word =
          targets.exactProfile (sigma.symm physicalLeg) cell word := by
  classical
  simp only [cwRecursiveExactChildParts, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A doubled child word satisfies the child selection exactly when its joined parent belongs
to the original exact target alphabet.

Proof sketch: decode the child word as a parent, use the labelled-child identity above, and
compare bounded quotient digits through their natural values. The joint counts then coincide
literally on their original occurrence domain.
-/
theorem mem_cwRecursiveExactChildParts_iff_parent
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n) (physicalLeg : Leg)
    (children : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) (n + n + 1)) :
    children ∈ cwRecursiveExactChildParts partAt sigma targets reference physicalLeg ↔
      (cwParentChildChunkWordEquiv depth n).symm children ∈
        cwRecursiveExactTargetFiberParts partAt sigma targets reference physicalLeg := by
  obtain ⟨parent, rfl⟩ := (cwParentChildChunkWordEquiv depth n).surjective children
  rw [Equiv.symm_apply_apply, mem_cwRecursiveExactChildParts_iff,
    mem_cwRecursiveExactTargetFiberParts_iff,
    cwChildPowerSplitSequence_parentChildEquiv]
  apply and_congr _ Iff.rfl
  constructor
  · intro h
    funext occurrence
    apply Fin.ext
    rw [val_cwRecursiveLabelledChildWord_eq_splitWordWeight]
    exact h occurrence
  · intro h occurrence
    rw [← val_cwRecursiveLabelledChildWord_eq_splitWordWeight]
    exact congrArg Fin.val (congrFun h occurrence)

/-- The exact parent box is isomorphic to the selected doubled-child power with the same
quotient weights and full cell-by-cell split profiles.

Proof sketch: select the common external square of child powers by the joined parent predicate.
The two existing partition reindexes identify that same selected square with the parent box and
with the child box. Compose their tensor isomorphisms; the membership theorem above identifies
the child selection. This transports constituents as well as their labels.
-/
theorem cwRecursiveExactTargetBox_isomorphic_childPowerBox
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n) :
    Isomorphic
      (((cwChunkPartitionedTensor K q (depth + 1)).positivePower n).box
        (cwRecursiveExactTargetFiberParts partAt sigma targets reference)).realize
      (((cwChunkPartitionedTensor K q depth).positivePower (n + n + 1)).box
        (cwRecursiveExactChildParts partAt sigma targets reference)).realize := by
  classical
  let keepSquare := fun (c : Leg) pair ↦
    cwParentChildChunkWordJoin depth n pair ∈
      cwRecursiveExactTargetFiberParts partAt sigma targets reference c
  have hp := (cwParentChunkPower_reindexEquiv K q depth n).isomorphic_select keepSquare
  have hc := (cwChildChunkPower_reindexEquiv K q depth n).isomorphic_select keepSquare
  have hparent : Isomorphic
      ((((cwChunkPartitionedTensor K q depth).positivePower n).external
          ((cwChunkPartitionedTensor K q depth).positivePower n)).select keepSquare).realize
      (((cwChunkPartitionedTensor K q (depth + 1)).positivePower n).box
        (cwRecursiveExactTargetFiberParts partAt sigma targets reference)).realize := by
    simpa only [keepSquare, Equiv.apply_symm_apply, PartitionedTensor.box] using hp
  have hkeep :
      (fun c children ↦ keepSquare c
        ((positiveWordAppendEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n n).symm
          children)) =
        (fun c children ↦ children ∈
          cwRecursiveExactChildParts partAt sigma targets reference c) := by
    funext c children
    exact propext (mem_cwRecursiveExactChildParts_iff_parent
      partAt sigma targets reference c children).symm
  apply hparent.symm.trans
  simpa only [PartitionedTensor.box, hkeep] using hc

/-- The compact intact parent box restricts to the selected labelled-child power.

This is the compact-source form needed after repair: include the compact labels into the same
ambient box, then apply the exact parent-to-child isomorphism. It does not yet group the child
states into the evaluator's heterogeneous interface product.
-/
theorem cwRecursiveCompactExactTarget_restricts_childPowerBox
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n) :
    Restricts
      (compactBox ((cwChunkPartitionedTensor K q (depth + 1)).positivePower n)
        (cwRecursiveExactTargetFiberParts partAt sigma targets reference)).realize
      (((cwChunkPartitionedTensor K q depth).positivePower (n + n + 1)).box
        (cwRecursiveExactChildParts partAt sigma targets reference)).realize :=
  (Restricts.compactBox_to_box _ _).trans
    (cwRecursiveExactTargetBox_isomorphic_childPowerBox
      K q partAt sigma targets reference).restricts

end AlgebraicComplexity.Examples
