/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.CertifiedLevelFourOccurrenceTargets
import MatrixMultiplication.TotalWeightExtractionClients

/-!
# Count-facing level-four extraction at the compact certificate

`MatrixMultiplication.TotalWeightExtractionClients` states its level-four adapter with the local
validity, boundary and coordinate-order premises deliberately visible, "until a committed
certificate constructor packages them into `RecursiveOccurrenceTargetData`".  This module is that
constructor's client: at the committed rows of certificate `e7987d7f…` and its six diagonal
`(root, incomingRegion) = (region, region)` occurrences, child-row normalization and the
coordinate-order agreement are supplied by the certificate, so the extraction seam keeps only the
finite per-slot boundary law.

The support premise of the count-facing clients is discharged here as well, so a caller supplies
only tensor-side data: the kept coarse family, its restriction, legwise injectivity, and the
reference address realizing the `k`-fold full occurrence type.

The depth-two statement remains a per-stage semantic adapter, exactly as upstream: it is not a
global count seam, and nothing here proves a hash construction, a counting floor, or any
asymptotic estimate.
-/

namespace MatrixMultiplication.CertifiedLevelFourOccurrenceExtractionClients

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.CertifiedLevelFourOccurrenceTargets
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.TotalWeightExtractionClients

universe u

/-- The `hsupported` input of the count-facing clients, discharged at the committed data: every
nonzero labelled occurrence row of a committed diagonal tuple carries the split-word weight
advertised by its coarse occurrence cell. -/
theorem certifiedTargetData_supported (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (hboundary : FixedParentSlotBoundaryValid certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val)
    (c : Leg) (occurrence : ComplementaryOccurrence (LevelFourValidSlot parent))
    (word : SplitWord 2)
    (hcount : ((certifiedTargetData region parent hboundary).law c).count
      occurrence word ≠ 0) :
    splitWordWeight word = (levelFourOccurrenceCoarseIndex parent xzy occurrence).get c :=
  cwTotalWeightLevelFourOccurrenceLaw_supported certifiedTop certifiedBetaThree
    region region parent xzy (certifiedChildRowsValid region parent) c occurrence word hcount

/-- **Item 12, count-facing form.**  The committed level-four occurrence adapter: the local
validity and coordinate-order premises are gone, and the package consumed by the compatibility
cleanup is the certified one.  Only the finite per-slot boundary law and ordinary tensor-side
inputs remain. -/
theorem certifiedLevelFourOccurrenceFixedTargetCellType_to_indexedDirectSum
    (K : Type u) [CommRing K] (q : ℕ)
    (region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hboundary : FixedParentSlotBoundaryValid certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val)
    (k n : ℕ) (partAt : Fin (n + 1) → PUnit)
    (coarseKept : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 2) n)))
    (hcoarseKept : coarseKept ⊆
      (((cwChunkPartitionedTensor K q 2).coarsen
        (cwTotalWeightChunkCoarsening 2)).positivePower n).support)
    (hfull :
      let Q := (cwChunkPartitionedTensor K q 2).coarsen
        (cwTotalWeightChunkCoarsening 2)
      Restricts (Q.positivePower n).realize
        ((Q.positivePower n).withSupport coarseKept).realize)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 2) n) ↦ address .X) coarseKept)
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 2) n) ↦ address .Y) coarseKept)
    (hZ : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 2) n) ↦ address .Z) coarseKept)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 2) n))
    (hreferenceMem : reference ∈ coarseKept)
    (hreference : WordType.multiplicity
        (cwOrientedFiniteCellSequence 2 n partAt (Equiv.refl Leg) reference) =
      WordType.proportionalCounts
        (cwRecursiveOccurrenceFullCellType 2
          (certifiedSlotProfile region parent)
          (levelFourOccurrenceCoarseIndex parent xzy)
          (certifiedOccurrenceCoarseIndex_total parent)) k) :
    let scaledData := cwProportionalRecursiveOccurrenceTargetData
      (certifiedTargetData region parent hboundary) k
    let rawTargets := scaledData.toCompatibilityTargets
    let ambient := cwFixedTargetCellTypeCoarseSupport
      2 n partAt (Equiv.refl Leg) coarseKept reference
    let Q := (cwChunkPartitionedTensor K q 2).coarsen
      (cwTotalWeightChunkCoarsening 2)
    let P := (Q.positivePower n).withSupport ambient
    let model := cwTotalWeightFeatureCompatibilityModel 2 n partAt
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    reference ∈ zSupport ∧
      Restricts (Q.positivePower n).realize
        (Tensor.indexedDirectSum
          (fun address : zSupport ↦ P.constituent address.1)) :=
  levelFourOccurrenceFixedTargetCellType_to_indexedDirectSum K q certifiedTop certifiedBetaThree
    (certifiedOrder region.val) xzy (certifiedOrder_agreesWithOrientation region.val)
    region region parent (certifiedChildRowsValid region parent) hboundary
    k n partAt coarseKept hcoarseKept hfull hX hY hZ reference hreferenceMem hreference

/-- The same seam driven directly by the bounded boundary checker, which is what a generated
shard emits. -/
theorem certifiedLevelFourOccurrenceFixedTargetCellType_to_indexedDirectSum_ofChecked
    (K : Type u) [CommRing K] (q : ℕ)
    (region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hchecked : fixedParentSlotBoundaryValid certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val = true)
    (k n : ℕ) (partAt : Fin (n + 1) → PUnit)
    (coarseKept : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 2) n)))
    (hcoarseKept : coarseKept ⊆
      (((cwChunkPartitionedTensor K q 2).coarsen
        (cwTotalWeightChunkCoarsening 2)).positivePower n).support)
    (hfull :
      let Q := (cwChunkPartitionedTensor K q 2).coarsen
        (cwTotalWeightChunkCoarsening 2)
      Restricts (Q.positivePower n).realize
        ((Q.positivePower n).withSupport coarseKept).realize)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 2) n) ↦ address .X) coarseKept)
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 2) n) ↦ address .Y) coarseKept)
    (hZ : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 2) n) ↦ address .Z) coarseKept)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 2) n))
    (hreferenceMem : reference ∈ coarseKept)
    (hreference : WordType.multiplicity
        (cwOrientedFiniteCellSequence 2 n partAt (Equiv.refl Leg) reference) =
      WordType.proportionalCounts
        (cwRecursiveOccurrenceFullCellType 2
          (certifiedSlotProfile region parent)
          (levelFourOccurrenceCoarseIndex parent xzy)
          (certifiedOccurrenceCoarseIndex_total parent)) k) :
    let scaledData := cwProportionalRecursiveOccurrenceTargetData
      (certifiedTargetData_ofChecked region parent hchecked) k
    let rawTargets := scaledData.toCompatibilityTargets
    let ambient := cwFixedTargetCellTypeCoarseSupport
      2 n partAt (Equiv.refl Leg) coarseKept reference
    let Q := (cwChunkPartitionedTensor K q 2).coarsen
      (cwTotalWeightChunkCoarsening 2)
    let P := (Q.positivePower n).withSupport ambient
    let model := cwTotalWeightFeatureCompatibilityModel 2 n partAt
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    reference ∈ zSupport ∧
      Restricts (Q.positivePower n).realize
        (Tensor.indexedDirectSum
          (fun address : zSupport ↦ P.constituent address.1)) :=
  certifiedLevelFourOccurrenceFixedTargetCellType_to_indexedDirectSum K q region parent
    (fixedParentSlotBoundaryValid_sound certifiedTop certifiedBetaThree
      (certifiedOrder region.val) region.val region.val parent.val hchecked)
    k n partAt coarseKept hcoarseKept hfull hX hY hZ reference hreferenceMem hreference

end MatrixMultiplication.CertifiedLevelFourOccurrenceExtractionClients
