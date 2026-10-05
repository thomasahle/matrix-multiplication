/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightExtractionClients
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightLocalizedSelection
import AlgebraicComplexity.MatrixMultiplication.MarkedXYPresentPartitionExtraction

/-!
# Uncycled total-weight cleanup on an actually present fixed cell type

Marked affine hashing isolates the `X` and `Y` block words of an abstract target family.  When
only some abstract targets occur in an actual source partition, present-support extraction keeps
their literal intersection with the source support.  This file continues from that uncycled
intersection: it selects one full tagged cell type using the already isolated `X` labels, applies
the total-weight `Y/Z` compatibility client, and retains the complete localized fine family in
every surviving quotient constituent.

The construction assumes no lower bound on the present family or on the final compatibility
support.  In particular, the missing-target estimate and the quantitative `Z`-competitor bound
remain separate counting obligations.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

noncomputable section

/-- **Uncycled present-support C2 adapter.**  An actual subpartition of the total-weight positive
power first restricts to its present marked `X/Y`-isolated family.  The isolated `X` labels then
select one full tagged cell type, whose reference profiles discharge both compatibility-pass
hypotheses.  Finally every surviving whole quotient constituent is restricted to its complete
localized fine typed family.

The reference is required to be actually present, so the selected full-cell family is nonempty
before the counted `Z` pass.  No claim is made that the reference survives that pass. -/
theorem cwTotalWeightPresentMarkedFixedTargetCellTypeCleanup_to_localizedFineTypes
    {R : Type u} [Field R] [NeZero (2 : R)]
    (K : Type v) [CommRing K] (q depth n : ℕ)
    {Part : Type w} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    {support : Finset (BlockAddress (fun _c : Leg ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (actualSupport : Finset
      (BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hactualSupport : actualSupport ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hmodeled : actualSupport ⊆
      H.modeledAddresses n (H.legalTargets n ambientWords))
    (reference : BlockAddress
      (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreferenceMem : reference ∈
      H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed
        ((((cwChunkPartitionedTensor K q depth).coarsen
          (cwTotalWeightChunkCoarsening depth)).positivePower n).withSupport actualSupport))
    (hreference : CWTotalWeightReferenceProfiles
      depth n partAt rawTargets reference)
    (fineType : ∀ _c : Leg,
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ) :
    let Q := (cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)
    let P := (Q.positivePower n).withSupport actualSupport
    let coarseKept := H.presentMarkedXYIsolatedPowerAddresses
      ambientWords markedWords B seed P
    let ambient := cwFixedTargetCellTypeCoarseSupport
      depth n partAt (Equiv.refl Leg) coarseKept reference
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    reference ∈ ambient ∧
      Restricts P.realize
        (Tensor.indexedDirectSum (fun address : zSupport ↦
          (cwTotalWeightLocalizedFineTypes
            K q depth n address.1 fineType).realize)) := by
  classical
  let Q := (cwChunkPartitionedTensor K q depth).coarsen
    (cwTotalWeightChunkCoarsening depth)
  let P := (Q.positivePower n).withSupport actualSupport
  let coarseKept := H.presentMarkedXYIsolatedPowerAddresses
    ambientWords markedWords B seed P
  let ambient := cwFixedTargetCellTypeCoarseSupport
    depth n partAt (Equiv.refl Leg) coarseKept reference
  let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
  let targets := cwTotalWeightPushforwardTargets rawTargets
  let ySupport := compatibilityIsolatedSupport ambient .Y
    (model.FeatureCompatibleY targets)
  let zSupport := compatibilityIsolatedSupport ySupport .Z
    (model.FeatureCompatibleZ targets)
  have hcoarseKept : coarseKept ⊆ (Q.positivePower n).support := by
    intro address haddress
    apply hactualSupport
    exact (Finset.mem_inter.mp haddress).1
  have hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X)
      coarseKept := by
    exact H.x_injectiveOn_presentMarkedXYIsolatedPowerAddresses
      ambientWords markedWords hwords B hB seed P
  have hambient : ambient ⊆ coarseKept :=
    cwFixedTargetCellTypeCoarseSupport_subset
      depth n partAt coarseKept reference
  have hreferenceAmbient : reference ∈ ambient :=
    cwReference_mem_fixedTargetCellTypeCoarseSupport
      depth n partAt coarseKept reference hreferenceMem
  have hpresent : Restricts P.realize (P.withSupport coarseKept).realize := by
    exact Tensor.Restricts.presentModeledTargets_to_presentMarkedXYIsolated
      H ambientWords markedWords hwords B hB seed P (by simpa [P] using hmodeled)
  have hselect : Restricts (P.withSupport coarseKept).realize
      ((Q.positivePower n).withSupport ambient).realize := by
    have hclosed : IsProjectionClosed
        (P.withSupport coarseKept).support ambient ({.X} : Finset Leg) := by
      refine ⟨?_, ?_⟩
      · simpa only [PartitionedTensor.withSupport_support] using hambient
      · intro address haddress hlabels
        obtain ⟨selected, hselected, hlabel⟩ :=
          hlabels .X (Finset.mem_singleton_self _)
        have haddressEq : address = selected :=
          hX (Finset.mem_coe.mpr haddress)
            (Finset.mem_coe.mpr (hambient hselected)) hlabel
        rw [haddressEq]
        exact hselected
    simpa only [P, PartitionedTensor.withSupport] using
      (Tensor.Restricts.partitionedProjectionClosed
        (P.withSupport coarseKept) ambient {Leg.X} hclosed)
  have hcleanup : Restricts ((Q.positivePower n).withSupport ambient).realize
      (Tensor.indexedDirectSum
        (fun address : zSupport ↦ (Q.positivePower n).constituent address.1)) := by
    simpa only [Q, coarseKept, ambient, model, targets, ySupport, zSupport,
      PartitionedTensor.withSupport_constituent] using
      (cwTotalWeightFixedTargetCellTypeYZCompatibilityCleanup_to_indexedDirectSum
        K q depth n partAt rawTargets coarseKept hcoarseKept hX reference hreference)
  have hzSupport : zSupport ⊆ (Q.positivePower n).support := by
    exact (compatibilityIsolatedSupport_subset ySupport .Z
      (model.FeatureCompatibleZ targets)).trans
        ((compatibilityIsolatedSupport_subset ambient .Y
          (model.FeatureCompatibleY targets)).trans
            (hambient.trans hcoarseKept))
  refine ⟨hreferenceAmbient, ?_⟩
  exact cwTotalWeightCleanup_to_localizedFineTypes
    K q depth n P.realize zSupport hzSupport
      (hpresent.trans (hselect.trans hcleanup)) fineType

end

end AlgebraicComplexity.Examples
