/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightDivisionLeafStage
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightPresentFixedCellCleanup

set_option autoImplicit false

/-!
# Whole inner extraction after present fixed-cell cleanup

The uncycled present-support cleanup produces an exact direct sum of localized total-weight
families, indexed by the surviving quotient addresses.  This file proves the next finite semantic
step.  Membership in one full tagged empirical cell type forces the recovered supported quotient
words to have one exact joint type.  Consequently one canonical exact inner extraction transports
to every survivor, and the outer and inner indices flatten with their literal product cardinality.

The source remains the supported coarse tensor used by the cleanup theorem.  No identification
with a finer interface-term source, asymptotic survivor estimate, or numerical certificate is
made here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w x

noncomputable section

/-- Equality of the full tagged cell type forces equality of the exact recovered supported
coarse-word type.

The proof uses the canonical common permutation of sample positions supplied by the full cell
type.  Transposition of a supported joint word commutes with that permutation, and position
reindexing preserves multiplicities. -/
theorem cwTotalWeightCoarseWord_multiplicity_eq_of_fullCellType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type v} [Fintype Part]
    (partAt : Fin (n + 1) → Part)
    (left right : BlockAddress
      (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n))
    (hleft : left ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hright : right ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hsame : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) left) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) right)) :
    WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n
          (cwTotalWeightCoarseWordOfAddress K q depth n left hleft)) =
      WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n
          (cwTotalWeightCoarseWordOfAddress K q depth n right hright)) := by
  classical
  let leftWord := cwTotalWeightCoarseWordOfAddress K q depth n left hleft
  let rightWord := cwTotalWeightCoarseWordOfAddress K q depth n right hright
  let tau := cwOrientedCellPositionPermOfSameMultiplicity
    depth n partAt (Equiv.refl Leg) left right hsame
  have haddress : cwPositionRelabelCoarseAddress depth n tau right = left :=
    cwPositionRelabelCoarseAddress_orientedCellPositionPerm
      depth n partAt (Equiv.refl Leg) left right hsame
  have hleftAddress :
      positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n leftWord = left :=
    positiveSupportWordBlockAddress_cwTotalWeightCoarseWordOfAddress
      K q depth n left hleft
  have hrightAddress :
      positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n rightWord = right :=
    positiveSupportWordBlockAddress_cwTotalWeightCoarseWordOfAddress
      K q depth n right hright
  have hword : positiveWordPositionEquiv
      (CWTotalWeightCoarseSupport K q depth) n tau rightWord = leftWord := by
    apply Tensor.positiveSupportWordBlockAddress_injective
      (CWTotalWeightCoarseSupport K q depth) n
    rw [← Tensor.positionRelabelBlockAddress_positiveSupportWordBlockAddress,
      hrightAddress, hleftAddress]
    exact haddress
  have hvalues :
      positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n rightWord ∘ tau =
        positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n leftWord := by
    simpa only [positiveWordEquiv_position_apply] using
      congrArg (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n) hword
  change WordType.multiplicity
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n leftWord) =
    WordType.multiplicity
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n rightWord)
  rw [← hvalues]
  simpa only [Equiv.symm_symm] using
    (WordType.multiplicity_reindex tau.symm
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n rightWord))

/-- **Present fixed-cell whole stage.**  The actual uncycled marked family is restricted to one
full tagged cell type and cleaned on `Y` and `Z`.  One exact inner extraction at the reference
address then transports to every survivor, yielding exactly
`zSupport.card * innerCopies` equal rectangular matrix-multiplication tensors.

The theorem derives the assembled product restriction.  Its remaining inputs are local: the
actual supported coarse source and reference profiles required by cleanup, plus one canonical
inner restriction and its exact finite cardinality. -/
noncomputable def cwTotalWeightPresentMarkedFixedTargetCellType_wholeStage
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
      PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    {J : Type x} [Fintype J]
    (innerCopies xSize ySize zSize : ℕ)
    (hcardJ : Fintype.card J = innerCopies)
    (hcanonical : Restricts
      (cwTotalWeightLocalizedFineTypes K q depth n reference fineType).realize
      (Tensor.indexedDirectSum (fun _j : J ↦
        matrixMultiplication (K := K) xSize ySize zSize))) :
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
    WholeConstituentLaserVolumeStage K P.realize
      (zSupport.card * innerCopies) xSize ySize zSize := by
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
  have hadapter : reference ∈ ambient ∧
      Restricts P.realize
        (Tensor.indexedDirectSum (fun address : zSupport ↦
          (cwTotalWeightLocalizedFineTypes
            K q depth n address.1 fineType).realize)) := by
    simpa only [Q, P, coarseKept, ambient, model, targets, ySupport, zSupport] using
      (cwTotalWeightPresentMarkedFixedTargetCellTypeCleanup_to_localizedFineTypes
        (R := R) K q depth n partAt rawTargets H ambientWords markedWords hwords
        B hB seed actualSupport hactualSupport hmodeled reference hreferenceMem
        hreference fineType)
  have hcoarseKept : coarseKept ⊆ (Q.positivePower n).support := by
    intro address haddress
    apply hactualSupport
    exact (Finset.mem_inter.mp haddress).1
  have hambient : ambient ⊆ coarseKept :=
    cwFixedTargetCellTypeCoarseSupport_subset
      depth n partAt coarseKept reference
  have hzSupport : zSupport ⊆ (Q.positivePower n).support :=
    (compatibilityIsolatedSupport_subset ySupport .Z
      (model.FeatureCompatibleZ targets)).trans
        ((compatibilityIsolatedSupport_subset ambient .Y
          (model.FeatureCompatibleY targets)).trans
            (hambient.trans hcoarseKept))
  have hreferenceSupport : reference ∈ (Q.positivePower n).support :=
    hcoarseKept (hambient hadapter.1)
  let referenceWord := cwTotalWeightCoarseWordOfAddress
    K q depth n reference hreferenceSupport
  let coarseWord : zSupport →
      PositiveWord (CWTotalWeightCoarseSupport K q depth) n :=
    fun address ↦ cwTotalWeightCoarseWordOfAddress
      K q depth n address.1 (hzSupport address.2)
  let coarseType : CWTotalWeightCoarseSupport K q depth → ℕ :=
    WordType.multiplicity
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n referenceWord)
  have hreferenceType : referenceWord ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) n coarseType := by
    rw [mem_positiveTypeClass]
  have hcoarseWordType : ∀ address, coarseWord address ∈ positiveTypeClass
      (CWTotalWeightCoarseSupport K q depth) n coarseType := by
    intro address
    rw [mem_positiveTypeClass]
    have haddressAmbient : address.1 ∈ ambient :=
      compatibilityIsolatedSupport_subset ambient .Y
        (model.FeatureCompatibleY targets)
        (compatibilityIsolatedSupport_subset ySupport .Z
          (model.FeatureCompatibleZ targets) address.2)
    have hsame := ((mem_cwFixedTargetCellTypeCoarseSupport_iff
      depth n partAt (Equiv.refl Leg) coarseKept reference address.1).mp
        haddressAmbient).2
    exact (cwTotalWeightCoarseWord_multiplicity_eq_of_fullCellType
      K q depth n partAt reference address.1 hreferenceSupport
        (hzSupport address.2) hsame).symm
  have hcoarseAddress (address : zSupport) :
      positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n (coarseWord address) = address.1 :=
    positiveSupportWordBlockAddress_cwTotalWeightCoarseWordOfAddress
      K q depth n address.1 (hzSupport address.2)
  have houter : Restricts P.realize
      (Tensor.indexedDirectSum (fun address : zSupport ↦
        (cwTotalWeightLocalizedFineTypes K q depth n
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n (coarseWord address))
          fineType).realize)) := by
    simpa only [hcoarseAddress] using hadapter.2
  have hreferenceAddress :
      positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n referenceWord = reference :=
    positiveSupportWordBlockAddress_cwTotalWeightCoarseWordOfAddress
      K q depth n reference hreferenceSupport
  have hcanonicalWord : Restricts
      (cwTotalWeightLocalizedFineTypes K q depth n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) n referenceWord)
        fineType).realize
      (Tensor.indexedDirectSum (fun _j : J ↦
        matrixMultiplication (K := K) xSize ySize zSize)) := by
    simpa only [hreferenceAddress] using hcanonical
  exact cwTotalWeightLocalizedOuter_wholeStage_of_fixedCoarseType
    K q depth n P.realize coarseWord referenceWord coarseType
      hreferenceType hcoarseWordType fineType (J := J)
      zSupport.card innerCopies xSize ySize zSize (by simp) hcardJ houter hcanonicalWord

end

end AlgebraicComplexity.Examples
