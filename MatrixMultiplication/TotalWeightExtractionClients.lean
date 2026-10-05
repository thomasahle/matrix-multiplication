/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightRecursiveOccurrenceClients

/-!
# Total-weight extraction clients at proportional scale

The count-facing endpoint in this module is depth one and `k`-parametric.  It consumes a fully
constructed recursive occurrence target package, an explicit restriction from the unrestricted
positive power to the hash-selected family, legwise injectivity, and a reference address realizing
the `k`-fold full occurrence type.  It proves that the reference survives both compatibility
passes and returns a restriction from the unrestricted power to a nonempty indexed direct sum.

The level-three and level-four specializations below are local occurrence adapters.  In particular,
the depth-two level-four theorem is capacity-safe only for its local 1.737289-bit stage; it is not a
global 8.241973-bit count seam.  Their validity/boundary/order premises are intentionally visible
until a committed certificate constructor packages them into `RecursiveOccurrenceTargetData`.

No cardinal lower bound, hash construction, generated numeric equality, fine typed leaf, or
sequence estimate is proved here.
-/

namespace MatrixMultiplication.TotalWeightExtractionClients

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveChildProfiles
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveLevelThreeOccurrences
open MatrixMultiplication.SimplifiedRecursiveSplitTypes
open MatrixMultiplication.SimplifiedVolumeReconstruction

universe u v w

/-- **C2 count-facing global client.**  At depth one, a proportional recursive occurrence package
and a nonempty leg-isolated reference class turn an explicit full-power `X` pass into the
post-`Y`/`Z` indexed direct sum.  The target package already contains its local laws and boundary
proofs, so no validity, boundary, or coordinate-order premise leaks through this interface. -/
theorem levelTwoGlobalRecursiveOccurrenceFixedTargetCellType_from_fullPower
    (K : Type u) [CommRing K] (q k n : ℕ)
    {State : Type v} [Fintype State]
    {Part : Type w} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (data : RecursiveOccurrenceTargetData (depth := 1) coarseOf profile)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal 1)
    (hsupported : ∀ c occurrence word,
      (data.law c).count occurrence word ≠ 0 →
        splitWordWeight word = (coarseOf occurrence).get c)
    (coarseKept : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 1) n)))
    (hcoarseKept : coarseKept ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).positivePower n).support)
    (hfull :
      let Q := (cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)
      Restricts (Q.positivePower n).realize
        ((Q.positivePower n).withSupport coarseKept).realize)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 1) n) ↦ address .X) coarseKept)
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 1) n) ↦ address .Y) coarseKept)
    (hZ : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 1) n) ↦ address .Z) coarseKept)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 1) n))
    (hreferenceMem : reference ∈ coarseKept)
    (hreference : WordType.multiplicity
        (cwOrientedFiniteCellSequence 1 n partAt (Equiv.refl Leg) reference) =
      WordType.proportionalCounts
        (cwRecursiveOccurrenceFullCellType 1 profile coarseOf htotal) k) :
    let scaledData := cwProportionalRecursiveOccurrenceTargetData data k
    let rawTargets := scaledData.toCompatibilityTargets
    let ambient := cwFixedTargetCellTypeCoarseSupport
      1 n partAt (Equiv.refl Leg) coarseKept reference
    let Q := (cwChunkPartitionedTensor K q 1).coarsen
      (cwTotalWeightChunkCoarsening 1)
    let P := (Q.positivePower n).withSupport ambient
    let model := cwTotalWeightFeatureCompatibilityModel 1 n partAt
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    reference ∈ zSupport ∧
      Restricts (Q.positivePower n).realize
        (Tensor.indexedDirectSum
          (fun address : zSupport ↦ P.constituent address.1)) := by
  let scaledData := cwProportionalRecursiveOccurrenceTargetData data k
  have hscaledSupported : ∀ c occurrence word,
      (scaledData.law c).count occurrence word ≠ 0 →
        splitWordWeight word = (coarseOf occurrence).get c := by
    intro c occurrence word hcount
    apply hsupported c occurrence word
    intro hzero
    exact hcount (by simp [scaledData, hzero])
  have htargetsSupported : scaledData.toCompatibilityTargets.IsWeightSupported :=
    cwRecursiveOccurrenceTargetData_isWeightSupported coarseOf scaledData hscaledSupported
  exact cwTotalWeightFixedTargetCellTypeYZCompatibilityCleanup_from_fullPower
    K q 1 n partAt scaledData.toCompatibilityTargets coarseKept hcoarseKept hfull
      hX hY hZ reference hreferenceMem htargetsSupported
      (cwTotalWeightReferenceProfiles_of_recursiveOccurrenceTargetData_proportionalCounts
        1 n partAt profile coarseOf data htotal hsupported k reference hreference)

/-- **Local level-three occurrence adapter.**  This depth-one specialization exposes the local
validity and boundary proofs used to construct its occurrence target package; the global client
above is the count-facing seam. -/
theorem levelThreeOccurrenceFixedTargetCellType_to_indexedDirectSum
    (K : Type u) [CommRing K] (q : ℕ)
    (data : PrimaryTables) (node : Fin PositiveLevelThreeData.nodeCount)
    (region : Fin PositiveLevelThreeData.regionCount) (sigma : Orientation)
    (hvalid : LevelThreeChildRowsValid data node region sigma)
    (hboundary : LevelThreeOccurrenceBoundaryValid data node region sigma hvalid)
    (k n : ℕ) (partAt : Fin (n + 1) → PUnit)
    (coarseKept : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 1) n)))
    (hcoarseKept : coarseKept ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).positivePower n).support)
    (hfull :
      let Q := (cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)
      Restricts (Q.positivePower n).realize
        ((Q.positivePower n).withSupport coarseKept).realize)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 1) n) ↦ address .X) coarseKept)
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 1) n) ↦ address .Y) coarseKept)
    (hZ : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 1) n) ↦ address .Z) coarseKept)
    (reference : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 1) n))
    (hreferenceMem : reference ∈ coarseKept)
    (hreference : WordType.multiplicity
        (cwOrientedFiniteCellSequence 1 n partAt (Equiv.refl Leg) reference) =
      WordType.proportionalCounts
        (cwRecursiveOccurrenceFullCellType 1
          (fun slot ↦ levelThreeSlotNumerator data node region slot *
            (levelTwoChildDenominator * levelTwoChildDenominator))
          (levelThreeOccurrenceCoarseIndex node sigma)
          (levelThreeOccurrenceCoarseIndex_total node sigma)) k) :
    let rawTargets := (cwProportionalRecursiveOccurrenceTargetData
      (levelThreeOccurrenceTargetData data node region sigma hvalid hboundary)
      k).toCompatibilityTargets
    let ambient := cwFixedTargetCellTypeCoarseSupport
      1 n partAt (Equiv.refl Leg) coarseKept reference
    let Q := (cwChunkPartitionedTensor K q 1).coarsen
      (cwTotalWeightChunkCoarsening 1)
    let P := (Q.positivePower n).withSupport ambient
    let model := cwTotalWeightFeatureCompatibilityModel 1 n partAt
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    reference ∈ zSupport ∧
      Restricts (Q.positivePower n).realize
        (Tensor.indexedDirectSum
          (fun address : zSupport ↦ P.constituent address.1)) := by
  exact levelTwoGlobalRecursiveOccurrenceFixedTargetCellType_from_fullPower
    K q k n partAt
    (fun slot ↦ levelThreeSlotNumerator data node region slot *
      (levelTwoChildDenominator * levelTwoChildDenominator))
    (levelThreeOccurrenceCoarseIndex node sigma)
    (levelThreeOccurrenceTargetData data node region sigma hvalid hboundary)
    (levelThreeOccurrenceCoarseIndex_total node sigma)
    (fun c occurrence word hcount ↦
      cwTotalWeightLevelThreeOccurrenceLaw_supported
        data node region sigma hvalid c occurrence word hcount)
    coarseKept hcoarseKept hfull hX hY hZ reference hreferenceMem hreference

/-- **Local level-four occurrence adapter.**  This depth-two theorem is only a per-stage semantic
adapter.  The `8.241973` global family cannot be `Y`-injective at this depth; use the depth-one
global client above for any count-facing statement. -/
theorem levelFourOccurrenceFixedTargetCellType_to_indexedDirectSum
    (K : Type u) [CommRing K] (q : ℕ)
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hboundary : FixedParentSlotBoundaryValid
      top betaThree order root.val region.val parent.val)
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
          (fun slot ↦ levelFourSlotNumerator top root region parent slot *
            (levelFourChildSamples * levelFourChildSamples))
          (levelFourOccurrenceCoarseIndex parent sigma)
          (levelFourOccurrenceCoarseIndex_total parent sigma)) k) :
    let scaledData := cwProportionalRecursiveOccurrenceTargetData
      (levelFourOccurrenceTargetData top betaThree order sigma horder root region parent
        hvalid hboundary) k
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
          (fun address : zSupport ↦ P.constituent address.1)) := by
  let scaledData := cwProportionalRecursiveOccurrenceTargetData
    (levelFourOccurrenceTargetData top betaThree order sigma horder root region parent
      hvalid hboundary) k
  have hscaledSupported : ∀ c occurrence word,
      (scaledData.law c).count occurrence word ≠ 0 →
        splitWordWeight word = (levelFourOccurrenceCoarseIndex parent sigma occurrence).get c := by
    intro c occurrence word hcount
    apply cwTotalWeightLevelFourOccurrenceLaw_supported
      top betaThree root region parent sigma hvalid c occurrence word
    intro hzero
    exact hcount (by simp [scaledData, levelFourOccurrenceTargetData, hzero])
  have htargetsSupported : scaledData.toCompatibilityTargets.IsWeightSupported :=
    cwRecursiveOccurrenceTargetData_isWeightSupported
      (levelFourOccurrenceCoarseIndex parent sigma) scaledData hscaledSupported
  exact cwTotalWeightFixedTargetCellTypeYZCompatibilityCleanup_from_fullPower
    K q 2 n partAt scaledData.toCompatibilityTargets coarseKept hcoarseKept hfull
      hX hY hZ reference hreferenceMem htargetsSupported
      (cwTotalWeightLevelFourReferenceProfiles top betaThree order sigma horder root region parent
        hvalid hboundary k n partAt reference hreference)

end MatrixMultiplication.TotalWeightExtractionClients
