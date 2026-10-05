/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.CompatibilityHashingIsolation
import AlgebraicComplexity.Combinatorics.LegwiseHashingExtraction
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCoarseHashing
import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPairCompatibilityContainment
import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPairCompetitorClassification
import AlgebraicComplexity.MatrixMultiplication.CompatibilityTargetSupport

/-!
# Affine hashing for sorted-pair compatibility

This module connects the globally uniform sorted-pair quotient to affine collision isolation.
The key containment fact is derived from exact complete-split profile support: a compatible
logical-`Y` or logical-`Z` label has the same total coarse word as the corresponding address leg.

Compatibility is split soundly into two cases.  Alternatives with unequal coarse legal triples
share the pivot hash leg and are handled by `LegalTriple.collisionProxy`; equal-coarse-triple
alternatives are retained as an explicit residual relation for the exact incidence/type-class
count.  Thus no theorem assumes that raw compatibility alone determines the whole quotient
address.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- A pair-sorted supported level-two atom still has total coarse weight four. -/
theorem cwSortedPairCoarseSupport_weight_sum
    (K : Type u) [CommRing K] (q : ℕ)
    (address : BlockAddress (fun _c ↦ SplitWord 1))
    (haddress : address ∈
      ((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).support) :
    splitWordWeight (address .X) + splitWordWeight (address .Y) +
        splitWordWeight (address .Z) = coarseTotal 1 := by
  classical
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hmap⟩ := haddress
  have hmapAt (c : Leg) :
      cwSortedPairChunkCoarsening c (fine c) = address c := by
    simpa [coarsenBlockAddress] using congrFun hmap c
  rw [← hmapAt .X, ← hmapAt .Y, ← hmapAt .Z,
    cwSortedPairChunkCoarsening_total, cwSortedPairChunkCoarsening_total,
    cwSortedPairChunkCoarsening_total]
  have hlegal := cwChunkPartitionedTensor_isEncodedFineLegalOnSupport K q 1 fine hfine
  unfold splitWordWeight coarseTotal
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    (∑ position,
        ((cwChunkSplitWord 1 (fine .X) position : ℕ) +
          (cwChunkSplitWord 1 (fine .Y) position : ℕ) +
          (cwChunkSplitWord 1 (fine .Z) position : ℕ))) =
        ∑ _position : Fin (2 ^ 1), 2 := by
      apply Finset.sum_congr rfl
      intro position _
      exact hlegal position
    _ = 2 ^ (1 + 1) := by norm_num

/-- Supported words of pair-sorted level-two atoms give coordinatewise legal coarse triples. -/
theorem cwSortedPairPositivePower_coarse_sum
    (K : Type u) [CommRing K] (q n : ℕ)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (sample : Fin (n + 1)) :
    splitWordWeight (positiveWordEquiv (SplitWord 1) n (address .X) sample) +
        splitWordWeight (positiveWordEquiv (SplitWord 1) n (address .Y) sample) +
        splitWordWeight (positiveWordEquiv (SplitWord 1) n (address .Z) sample) =
      coarseTotal 1 := by
  let source := cwSortedPairSupportedWordOfAddress K q n address haddress
  let atom := positiveWordEquiv (CWSortedPairCoarseSupport K q) n source sample
  have hatom : atom.1 ∈
      ((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).support := atom.2
  have hsum := cwSortedPairCoarseSupport_weight_sum K q atom.1 hatom
  have haddressAt (c : Leg) : atom.1 c =
      positiveWordEquiv (SplitWord 1) n (address c) sample := by
    exact cwSortedPairTaggedAtomWord_address_apply K q n (fun _ ↦ ())
      address haddress sample c
  simpa only [haddressAt] using hsum

/-- Bundle one supported pair-sorted power address as a legal affine-hashing triple on its total
coarse words. -/
def cwSortedPairLegalTriple
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    (source : {address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n) //
      address ∈ (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support}) :
    ProgressionHash.LegalTriple R (Fin (n + 1)) encoding.target where
  xIndex sample := encoding.encode (cwSplitWordTotalDigit 1
    (positiveWordEquiv (SplitWord 1) n (source.1 .X) sample))
  yIndex sample := encoding.encode (cwSplitWordTotalDigit 1
    (positiveWordEquiv (SplitWord 1) n (source.1 .Y) sample))
  zIndex sample := encoding.encode (cwSplitWordTotalDigit 1
    (positiveWordEquiv (SplitWord 1) n (source.1 .Z) sample))
  legal sample := encoding.legal_of_val_sum _ _ _
    (cwSortedPairPositivePower_coarse_sum K q n source.1 source.2 sample)

/-- The total coarse word of a pair-sorted quotient label. -/
def cwSortedPairTotalWord (n : ℕ) (label : PositiveWord (SplitWord 1) n) :
    Fin (n + 1) → CWCoarseDigit 1 :=
  cwSplitWordTotalDigit 1 ∘ positiveWordEquiv (SplitWord 1) n label

@[simp] theorem cwSortedPairLegalTriple_legIndex
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    (source : {address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n) //
      address ∈ (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support})
    (c : Leg) :
    (cwSortedPairLegalTriple encoding K q n source).legIndex c =
      encoding.encode ∘ cwSortedPairTotalWord n (source.1 c) := by
  cases c <;> rfl

/-- Raw `Y` compatibility and target support force equality of the coarse total words. -/
theorem cwSortedPairCompatibilityY_totalWord_eq
    {Part : Type*} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsYWeightSupported)
    (label : PositiveWord (SplitWord 1) n)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (hcompatible : cwSortedPairCompatibilityY n partAt rawTargets label address) :
    cwSortedPairTotalWord n label = cwSortedPairTotalWord n (address .Y) := by
  funext sample
  apply Fin.ext
  exact cwSortedPair_splitWordWeight_eq_Y_of_featureCompatibleY
    n partAt rawTargets hsupported label address hcompatible sample

/-- Raw `Z` compatibility and target support force equality of the coarse total words. -/
theorem cwSortedPairCompatibilityZ_totalWord_eq
    {Part : Type*} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsZWeightSupported)
    (label : PositiveWord (SplitWord 1) n)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (hcompatible : cwSortedPairCompatibilityZ n partAt rawTargets label address) :
    cwSortedPairTotalWord n label = cwSortedPairTotalWord n (address .Z) := by
  funext sample
  apply Fin.ext
  exact cwSortedPair_splitWordWeight_eq_Z_of_featureCompatibleZ
    n partAt rawTargets hsupported label address hcompatible sample

/-- Supported addresses in the pair-sorted positive power. -/
abbrev CWSortedPairPowerSupport
    (K : Type u) [CommRing K] (q n : ℕ) :=
  {address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n) //
    address ∈ (((cwChunkPartitionedTensor K q 1).coarsen
      cwSortedPairChunkCoarsening).positivePower n).support}

/-- `Y`-compatible alternatives whose coarse legal triple is genuinely different.  These are
exactly the alternatives that can be represented by a nontrivial collision proxy. -/
def cwSortedPairCatchableCompatibilityY
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (target other : CWSortedPairPowerSupport K q n) : Prop :=
  cwSortedPairCompatibilityY n partAt rawTargets (target.1 .Y) other.1 ∧
    cwSortedPairLegalTriple encoding K q n other ≠
      cwSortedPairLegalTriple encoding K q n target

/-- The analogous catchable relation for `Z` compatibility. -/
def cwSortedPairCatchableCompatibilityZ
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (target other : CWSortedPairPowerSupport K q n) : Prop :=
  cwSortedPairCompatibilityZ n partAt rawTargets (target.1 .Z) other.1 ∧
    cwSortedPairLegalTriple encoding K q n other ≠
      cwSortedPairLegalTriple encoding K q n target

/-- Catchable alternatives for either compatibility-controlled leg.  A single affine seed can
therefore remove all unequal-coarse-triple `Y` and `Z` alternatives at once. -/
def cwSortedPairCatchableCompatibilityYZ
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (target other : CWSortedPairPowerSupport K q n) : Prop :=
  cwSortedPairCatchableCompatibilityY encoding K q n
      partAt rawTargets target other ∨
    cwSortedPairCatchableCompatibilityZ encoding K q n
      partAt rawTargets target other

/-- The part of `Y` compatibility that remains after unequal coarse legal triples have been
hash-isolated. -/
def cwSortedPairResidualCompatibilityY
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (target other : CWSortedPairPowerSupport K q n) : Prop :=
  cwSortedPairCompatibilityY n partAt rawTargets (target.1 .Y) other.1 ∧
    cwSortedPairLegalTriple encoding K q n other =
      cwSortedPairLegalTriple encoding K q n target

/-- The equal-coarse-triple residual relation for `Z`. -/
def cwSortedPairResidualCompatibilityZ
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (target other : CWSortedPairPowerSupport K q n) : Prop :=
  cwSortedPairCompatibilityZ n partAt rawTargets (target.1 .Z) other.1 ∧
    cwSortedPairLegalTriple encoding K q n other =
      cwSortedPairLegalTriple encoding K q n target

/-- Raw `Y` compatibility splits exactly into catchable unequal-triple and residual equal-triple
alternatives. -/
theorem cwSortedPairCompatibilityY_iff_catchable_or_residual
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (target other : CWSortedPairPowerSupport K q n) :
    cwSortedPairCompatibilityY n partAt rawTargets (target.1 .Y) other.1 ↔
      cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets target other ∨
      cwSortedPairResidualCompatibilityY encoding K q n partAt rawTargets target other := by
  by_cases heq : cwSortedPairLegalTriple encoding K q n other =
      cwSortedPairLegalTriple encoding K q n target
  · simp [cwSortedPairCatchableCompatibilityY,
      cwSortedPairResidualCompatibilityY, heq]
  · simp [cwSortedPairCatchableCompatibilityY,
      cwSortedPairResidualCompatibilityY, heq]

/-- Raw `Z` compatibility has the same catchable/residual decomposition. -/
theorem cwSortedPairCompatibilityZ_iff_catchable_or_residual
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (target other : CWSortedPairPowerSupport K q n) :
    cwSortedPairCompatibilityZ n partAt rawTargets (target.1 .Z) other.1 ↔
      cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets target other ∨
      cwSortedPairResidualCompatibilityZ encoding K q n partAt rawTargets target other := by
  by_cases heq : cwSortedPairLegalTriple encoding K q n other =
      cwSortedPairLegalTriple encoding K q n target
  · simp [cwSortedPairCatchableCompatibilityZ,
      cwSortedPairResidualCompatibilityZ, heq]
  · simp [cwSortedPairCatchableCompatibilityZ,
      cwSortedPairResidualCompatibilityZ, heq]

/-- Every catchable sorted-pair `Y` competitor shares its actual coarse hash leg with the
target. -/
theorem cwSortedPairCatchableCompatibilityY_sharesLeg
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsYWeightSupported)
    {target other : CWSortedPairPowerSupport K q n}
    (hcompatible : cwSortedPairCatchableCompatibilityY encoding K q n
      partAt rawTargets target other) :
    ProgressionHash.LegalTriple.SharesLeg
      (cwSortedPairLegalTriple encoding K q n target)
      (cwSortedPairLegalTriple encoding K q n other) := by
  refine ⟨.Y, ?_⟩
  rw [cwSortedPairLegalTriple_legIndex, cwSortedPairLegalTriple_legIndex]
  exact congrArg (fun word ↦ encoding.encode ∘ word)
    (cwSortedPairCompatibilityY_totalWord_eq n partAt rawTargets hsupported
      (target.1 .Y) other.1 hcompatible.1)

/-- Every catchable sorted-pair `Z` competitor shares its actual coarse hash leg with the
target. -/
theorem cwSortedPairCatchableCompatibilityZ_sharesLeg
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsZWeightSupported)
    {target other : CWSortedPairPowerSupport K q n}
    (hcompatible : cwSortedPairCatchableCompatibilityZ encoding K q n
      partAt rawTargets target other) :
    ProgressionHash.LegalTriple.SharesLeg
      (cwSortedPairLegalTriple encoding K q n target)
      (cwSortedPairLegalTriple encoding K q n other) := by
  refine ⟨.Z, ?_⟩
  rw [cwSortedPairLegalTriple_legIndex, cwSortedPairLegalTriple_legIndex]
  exact congrArg (fun word ↦ encoding.encode ∘ word)
    (cwSortedPairCompatibilityZ_totalWord_eq n partAt rawTargets hsupported
      (target.1 .Z) other.1 hcompatible.1)

/-- Reconstruction-facing `Y` containment: genuine exact and pooled profile realizations supply
the support hypothesis required by collision-proxy hashing. -/
theorem cwSortedPairCatchableCompatibilityY_sharesLeg_of_realizesTargets
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (data : ExactCompatibilityProfileFamily Part 1)
    (pooled : ExactSplitAvgFamily Part 1)
    (hdata : data.RealizesTargets rawTargets)
    (hpooled : pooled.RealizesTargets rawTargets)
    {target other : CWSortedPairPowerSupport K q n}
    (hcompatible : cwSortedPairCatchableCompatibilityY encoding K q n
      partAt rawTargets target other) :
    ProgressionHash.LegalTriple.SharesLeg
      (cwSortedPairLegalTriple encoding K q n target)
      (cwSortedPairLegalTriple encoding K q n other) :=
  cwSortedPairCatchableCompatibilityY_sharesLeg encoding K q n
    partAt rawTargets
      (data.isYWeightSupported_of_realizesTargets pooled rawTargets hdata hpooled)
    hcompatible

/-- Reconstruction-facing `Z` containment. -/
theorem cwSortedPairCatchableCompatibilityZ_sharesLeg_of_realizesTargets
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (data : ExactCompatibilityProfileFamily Part 1)
    (pooled : ExactSplitAvgFamily Part 1)
    (hdata : data.RealizesTargets rawTargets)
    (hpooled : pooled.RealizesTargets rawTargets)
    {target other : CWSortedPairPowerSupport K q n}
    (hcompatible : cwSortedPairCatchableCompatibilityZ encoding K q n
      partAt rawTargets target other) :
    ProgressionHash.LegalTriple.SharesLeg
      (cwSortedPairLegalTriple encoding K q n target)
      (cwSortedPairLegalTriple encoding K q n other) :=
  cwSortedPairCatchableCompatibilityZ_sharesLeg encoding K q n
    partAt rawTargets
      (data.isZWeightSupported_of_realizesTargets pooled rawTargets hdata hpooled)
    hcompatible

/-- The standard collision proxy of two common-bucket legal triples hashes to the target bucket
whenever the triples share a leg. -/
theorem legalTriple_yHash_collisionProxy_eq_of_commonBuckets_of_sharesLeg
    {R : Type*} [Field R] [NeZero (2 : R)]
    {ι : Type*} [Fintype ι] {total : R}
    (seed : ProgressionHash.Seed R ι)
    (target other : ProgressionHash.LegalTriple R ι total) (b c : R)
    (htarget : ProgressionHash.Seed.InCommonBucket
      target.xIndex target.yIndex b seed)
    (hother : ProgressionHash.Seed.InCommonBucket
      other.xIndex other.yIndex c seed)
    (hshare : ProgressionHash.LegalTriple.SharesLeg target other) :
    seed.yHash (ProgressionHash.LegalTriple.collisionProxy target other) = b := by
  obtain ⟨leg, hleg⟩ := hshare
  have hcb : c = b :=
    ProgressionHash.LegalTriple.commonBucket_eq_of_legIndex_eq seed target other b c
      htarget hother leg hleg.symm
  unfold ProgressionHash.LegalTriple.collisionProxy
  split_ifs with hx
  · exact hother.2.trans hcb
  · rw [ProgressionHash.Seed.yHash_transportXAlternative_eq_xHash seed
      target.xIndex target.yIndex other.xIndex b htarget]
    exact hother.1.trans hcb

/-- Collision indices needed for catchable sorted-pair `Y` competitors are no more numerous than
the evaluator's exact conditional feature class. -/
theorem cwSortedPair_card_YCatchableAlternativeIndices_le_typeClass
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (targets : Finset (CWSortedPairPowerSupport K q n))
    (target : CWSortedPairPowerSupport K q n) :
    (ProgressionHash.Seed.compatibilityAlternativeIndices targets
      (cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets)
      (fun target other ↦ ProgressionHash.LegalTriple.collisionProxy
        (cwSortedPairLegalTriple encoding K q n target)
        (cwSortedPairLegalTriple encoding K q n other)) target).card ≤
      (cwSortedPairYCompetitorTypeClass K q n rawTargets (target.1 .Y)).card := by
  classical
  let alternatives := ProgressionHash.Seed.compatibilityAlternativeTargets targets
    (cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets) target
  let ambient := targets.image Subtype.val
  have himageSubset : alternatives.image Subtype.val ⊆
      compatibilityCompetitors ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets) target.1 := by
    intro address haddress
    obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp haddress
    have hdata : (other ≠ target ∧ other ∈ targets) ∧
        cwSortedPairCatchableCompatibilityY encoding K q n
          partAt rawTargets target other := by
      simpa [alternatives,
        ProgressionHash.Seed.compatibilityAlternativeTargets] using hother
    apply (mem_compatibilityCompetitors ambient .Y
      (cwSortedPairCompatibilityY n partAt rawTargets) target.1 other.1).mpr
    refine ⟨Finset.mem_image.mpr ⟨other, hdata.1.2, rfl⟩, ?_, hdata.2.1⟩
    intro heq
    exact hdata.1.1 (Subtype.ext heq)
  calc
    (ProgressionHash.Seed.compatibilityAlternativeIndices targets
      (cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets)
      (fun target other ↦ ProgressionHash.LegalTriple.collisionProxy
        (cwSortedPairLegalTriple encoding K q n target)
        (cwSortedPairLegalTriple encoding K q n other)) target).card ≤
        alternatives.card :=
      ProgressionHash.Seed.card_compatibilityAlternativeIndices_le _ _ _ _
    _ = (alternatives.image Subtype.val).card := by
      rw [Finset.card_image_of_injOn Subtype.val_injective.injOn]
    _ ≤ (compatibilityCompetitors ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets) target.1).card :=
      Finset.card_le_card himageSubset
    _ ≤ (cwSortedPairYCompetitorTypeClass K q n rawTargets
        (target.1 .Y)).card := by
      apply cwSortedPair_card_compatibilityCompetitorsY_le_typeClass
        K q n partAt rawTargets ambient
      intro address haddress
      obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp haddress
      exact source.2

/-- The corresponding exact collision-index bound for catchable `Z` competitors. -/
theorem cwSortedPair_card_ZCatchableAlternativeIndices_le_typeClass
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (targets : Finset (CWSortedPairPowerSupport K q n))
    (target : CWSortedPairPowerSupport K q n) :
    (ProgressionHash.Seed.compatibilityAlternativeIndices targets
      (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets)
      (fun target other ↦ ProgressionHash.LegalTriple.collisionProxy
        (cwSortedPairLegalTriple encoding K q n target)
        (cwSortedPairLegalTriple encoding K q n other)) target).card ≤
      (cwSortedPairZCompetitorTypeClass K q n rawTargets (target.1 .Z)).card := by
  classical
  let alternatives := ProgressionHash.Seed.compatibilityAlternativeTargets targets
    (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets) target
  let ambient := targets.image Subtype.val
  have himageSubset : alternatives.image Subtype.val ⊆
      compatibilityCompetitors ambient .Z
        (cwSortedPairCompatibilityZ n partAt rawTargets) target.1 := by
    intro address haddress
    obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp haddress
    have hdata : (other ≠ target ∧ other ∈ targets) ∧
        cwSortedPairCatchableCompatibilityZ encoding K q n
          partAt rawTargets target other := by
      simpa [alternatives,
        ProgressionHash.Seed.compatibilityAlternativeTargets] using hother
    apply (mem_compatibilityCompetitors ambient .Z
      (cwSortedPairCompatibilityZ n partAt rawTargets) target.1 other.1).mpr
    refine ⟨Finset.mem_image.mpr ⟨other, hdata.1.2, rfl⟩, ?_, hdata.2.1⟩
    intro heq
    exact hdata.1.1 (Subtype.ext heq)
  calc
    (ProgressionHash.Seed.compatibilityAlternativeIndices targets
      (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets)
      (fun target other ↦ ProgressionHash.LegalTriple.collisionProxy
        (cwSortedPairLegalTriple encoding K q n target)
        (cwSortedPairLegalTriple encoding K q n other)) target).card ≤
        alternatives.card :=
      ProgressionHash.Seed.card_compatibilityAlternativeIndices_le _ _ _ _
    _ = (alternatives.image Subtype.val).card := by
      rw [Finset.card_image_of_injOn Subtype.val_injective.injOn]
    _ ≤ (compatibilityCompetitors ambient .Z
        (cwSortedPairCompatibilityZ n partAt rawTargets) target.1).card :=
      Finset.card_le_card himageSubset
    _ ≤ (cwSortedPairZCompetitorTypeClass K q n rawTargets
        (target.1 .Z)).card := by
      apply cwSortedPair_card_compatibilityCompetitorsZ_le_typeClass
        K q n partAt rawTargets ambient
      intro address haddress
      obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp haddress
      exact source.2

/-- Catchable `Y` alternative targets themselves inject into the evaluator type class. -/
theorem cwSortedPair_card_YCatchableAlternativeTargets_le_typeClass
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (targets : Finset (CWSortedPairPowerSupport K q n))
    (target : CWSortedPairPowerSupport K q n) :
    (ProgressionHash.Seed.compatibilityAlternativeTargets targets
      (cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets)
      target).card ≤
      (cwSortedPairYCompetitorTypeClass K q n rawTargets (target.1 .Y)).card := by
  classical
  let alternatives := ProgressionHash.Seed.compatibilityAlternativeTargets targets
    (cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets) target
  let ambient := targets.image Subtype.val
  have himageSubset : alternatives.image Subtype.val ⊆
      compatibilityCompetitors ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets) target.1 := by
    intro address haddress
    obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp haddress
    have hdata : (other ≠ target ∧ other ∈ targets) ∧
        cwSortedPairCatchableCompatibilityY encoding K q n
          partAt rawTargets target other := by
      simpa [alternatives,
        ProgressionHash.Seed.compatibilityAlternativeTargets] using hother
    apply (mem_compatibilityCompetitors ambient .Y
      (cwSortedPairCompatibilityY n partAt rawTargets) target.1 other.1).mpr
    refine ⟨Finset.mem_image.mpr ⟨other, hdata.1.2, rfl⟩, ?_, hdata.2.1⟩
    intro heq
    exact hdata.1.1 (Subtype.ext heq)
  calc
    (ProgressionHash.Seed.compatibilityAlternativeTargets targets
      (cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets)
      target).card = (alternatives.image Subtype.val).card := by
        rw [Finset.card_image_of_injOn Subtype.val_injective.injOn]
    _ ≤ (compatibilityCompetitors ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets) target.1).card :=
      Finset.card_le_card himageSubset
    _ ≤ (cwSortedPairYCompetitorTypeClass K q n rawTargets
        (target.1 .Y)).card := by
      apply cwSortedPair_card_compatibilityCompetitorsY_le_typeClass
        K q n partAt rawTargets ambient
      intro address haddress
      obtain ⟨source, _hsource, rfl⟩ := Finset.mem_image.mp haddress
      exact source.2

/-- Catchable `Z` alternative targets inject into their evaluator type class. -/
theorem cwSortedPair_card_ZCatchableAlternativeTargets_le_typeClass
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (targets : Finset (CWSortedPairPowerSupport K q n))
    (target : CWSortedPairPowerSupport K q n) :
    (ProgressionHash.Seed.compatibilityAlternativeTargets targets
      (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets)
      target).card ≤
      (cwSortedPairZCompetitorTypeClass K q n rawTargets (target.1 .Z)).card := by
  classical
  let alternatives := ProgressionHash.Seed.compatibilityAlternativeTargets targets
    (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets) target
  let ambient := targets.image Subtype.val
  have himageSubset : alternatives.image Subtype.val ⊆
      compatibilityCompetitors ambient .Z
        (cwSortedPairCompatibilityZ n partAt rawTargets) target.1 := by
    intro address haddress
    obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp haddress
    have hdata : (other ≠ target ∧ other ∈ targets) ∧
        cwSortedPairCatchableCompatibilityZ encoding K q n
          partAt rawTargets target other := by
      simpa [alternatives,
        ProgressionHash.Seed.compatibilityAlternativeTargets] using hother
    apply (mem_compatibilityCompetitors ambient .Z
      (cwSortedPairCompatibilityZ n partAt rawTargets) target.1 other.1).mpr
    refine ⟨Finset.mem_image.mpr ⟨other, hdata.1.2, rfl⟩, ?_, hdata.2.1⟩
    intro heq
    exact hdata.1.1 (Subtype.ext heq)
  calc
    (ProgressionHash.Seed.compatibilityAlternativeTargets targets
      (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets)
      target).card = (alternatives.image Subtype.val).card := by
        rw [Finset.card_image_of_injOn Subtype.val_injective.injOn]
    _ ≤ (compatibilityCompetitors ambient .Z
        (cwSortedPairCompatibilityZ n partAt rawTargets) target.1).card :=
      Finset.card_le_card himageSubset
    _ ≤ (cwSortedPairZCompetitorTypeClass K q n rawTargets
        (target.1 .Z)).card := by
      apply cwSortedPair_card_compatibilityCompetitorsZ_le_typeClass
        K q n partAt rawTargets ambient
      intro address haddress
      obtain ⟨source, _hsource, rfl⟩ := Finset.mem_image.mp haddress
      exact source.2

/-- A single collision family for both controlled legs is bounded by the sum of the exact `Y`
and `Z` evaluator type classes. -/
theorem cwSortedPair_card_YZCatchableAlternativeIndices_le_typeClasses
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (targets : Finset (CWSortedPairPowerSupport K q n))
    (target : CWSortedPairPowerSupport K q n) :
    (ProgressionHash.Seed.compatibilityAlternativeIndices targets
      (cwSortedPairCatchableCompatibilityYZ encoding K q n partAt rawTargets)
      (fun target other ↦ ProgressionHash.LegalTriple.collisionProxy
        (cwSortedPairLegalTriple encoding K q n target)
        (cwSortedPairLegalTriple encoding K q n other)) target).card ≤
      (cwSortedPairYCompetitorTypeClass K q n rawTargets (target.1 .Y)).card +
        (cwSortedPairZCompetitorTypeClass K q n rawTargets (target.1 .Z)).card := by
  classical
  let alternatives := ProgressionHash.Seed.compatibilityAlternativeTargets targets
    (cwSortedPairCatchableCompatibilityYZ encoding K q n partAt rawTargets) target
  let alternativesY := ProgressionHash.Seed.compatibilityAlternativeTargets targets
    (cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets) target
  let alternativesZ := ProgressionHash.Seed.compatibilityAlternativeTargets targets
    (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets) target
  have hsubset : alternatives ⊆ alternativesY ∪ alternativesZ := by
    intro other hother
    have hdata : (other ≠ target ∧ other ∈ targets) ∧
        cwSortedPairCatchableCompatibilityYZ encoding K q n
          partAt rawTargets target other := by
      simpa [alternatives,
        ProgressionHash.Seed.compatibilityAlternativeTargets] using hother
    rcases hdata.2 with hy | hz
    · apply Finset.mem_union_left
      simpa [alternativesY,
        ProgressionHash.Seed.compatibilityAlternativeTargets] using
          And.intro hdata.1 hy
    · apply Finset.mem_union_right
      simpa [alternativesZ,
        ProgressionHash.Seed.compatibilityAlternativeTargets] using
          And.intro hdata.1 hz
  calc
    (ProgressionHash.Seed.compatibilityAlternativeIndices targets
      (cwSortedPairCatchableCompatibilityYZ encoding K q n partAt rawTargets)
      (fun target other ↦ ProgressionHash.LegalTriple.collisionProxy
        (cwSortedPairLegalTriple encoding K q n target)
        (cwSortedPairLegalTriple encoding K q n other)) target).card ≤
        alternatives.card :=
      ProgressionHash.Seed.card_compatibilityAlternativeIndices_le _ _ _ _
    _ ≤ (alternativesY ∪ alternativesZ).card := Finset.card_le_card hsubset
    _ ≤ alternativesY.card + alternativesZ.card :=
      Finset.card_union_le alternativesY alternativesZ
    _ ≤ (cwSortedPairYCompetitorTypeClass K q n rawTargets
          (target.1 .Y)).card +
        (cwSortedPairZCompetitorTypeClass K q n rawTargets
          (target.1 .Z)).card :=
      Nat.add_le_add
        (cwSortedPair_card_YCatchableAlternativeTargets_le_typeClass
          encoding K q n partAt rawTargets targets target)
        (cwSortedPair_card_ZCatchableAlternativeTargets_le_typeClass
          encoding K q n partAt rawTargets targets target)

/-- `X` hash index of a supported pair-sorted power address. -/
def cwSortedPairXHashIndex
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ) :
    CWSortedPairPowerSupport K q n → Fin (n + 1) → R :=
  fun source ↦ (cwSortedPairLegalTriple encoding K q n source).xIndex

/-- `Y` hash index of a supported pair-sorted power address. -/
def cwSortedPairYHashIndex
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ) :
    CWSortedPairPowerSupport K q n → Fin (n + 1) → R :=
  fun source ↦ (cwSortedPairLegalTriple encoding K q n source).yIndex

/-- Target-dependent affine collision proxy for two supported quotient addresses. -/
noncomputable def cwSortedPairCollisionProxy
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ) :
    CWSortedPairPowerSupport K q n → CWSortedPairPowerSupport K q n →
      Fin (n + 1) → R :=
  fun target other ↦ ProgressionHash.LegalTriple.collisionProxy
    (cwSortedPairLegalTriple encoding K q n target)
    (cwSortedPairLegalTriple encoding K q n other)

/-- Hash-isolated quotient targets for the catchable `Y` compatibility relation. -/
noncomputable def cwSortedPairYHashIsolatedTargets
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (targets : Finset (CWSortedPairPowerSupport K q n)) (buckets : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (CWSortedPairPowerSupport K q n) :=
  ProgressionHash.Seed.compatibilityHashIsolatedTargets targets buckets
    (cwSortedPairXHashIndex encoding K q n)
    (cwSortedPairYHashIndex encoding K q n)
    (cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets)
    (cwSortedPairCollisionProxy encoding K q n) seed

/-- Hash-isolated quotient targets for all unequal-coarse-triple `Y` and `Z` alternatives. -/
noncomputable def cwSortedPairYZHashIsolatedTargets
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (targets : Finset (CWSortedPairPowerSupport K q n)) (buckets : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (CWSortedPairPowerSupport K q n) :=
  ProgressionHash.Seed.compatibilityHashIsolatedTargets targets buckets
    (cwSortedPairXHashIndex encoding K q n)
    (cwSortedPairYHashIndex encoding K q n)
    (cwSortedPairCatchableCompatibilityYZ encoding K q n partAt rawTargets)
    (cwSortedPairCollisionProxy encoding K q n) seed

/-- The common-bucket family underlying sorted-pair compatibility hashing. -/
noncomputable def cwSortedPairCommonBucketTargets
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    (targets : Finset (CWSortedPairPowerSupport K q n)) (buckets : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (CWSortedPairPowerSupport K q n) :=
  ProgressionHash.Seed.commonBucketFilteredTargets targets buckets
    (cwSortedPairXHashIndex encoding K q n)
    (cwSortedPairYHashIndex encoding K q n) seed

/-- Complete finite affine-hashing theorem for the unequal-coarse-triple part of sorted-pair
`Y` compatibility.  The exact evaluator type-class bound discharges the quarter budget. -/
theorem exists_seed_many_cwSortedPairYHashIsolatedTargets
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsYWeightSupported)
    (targets : Finset (CWSortedPairPowerSupport K q n)) (buckets : Finset R)
    (hquarter : ∀ target ∈ targets,
      4 * (cwSortedPairYCompetitorTypeClass K q n rawTargets
        (target.1 .Y)).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * targets.card * buckets.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (cwSortedPairYHashIsolatedTargets encoding K q n partAt rawTargets
              targets buckets seed).card ∧
        cwSortedPairYHashIsolatedTargets encoding K q n partAt rawTargets
            targets buckets seed ⊆
          cwSortedPairCommonBucketTargets encoding K q n targets buckets seed ∧
        cwSortedPairYHashIsolatedTargets encoding K q n partAt rawTargets
            targets buckets seed ⊆
          ProgressionHash.Seed.compatibilityIsolatedTargets
            (cwSortedPairCommonBucketTargets encoding K q n targets buckets seed)
            (cwSortedPairCatchableCompatibilityY encoding K q n
              partAt rawTargets) := by
  apply ProgressionHash.Seed.exists_seed_many_compatibilityHashIsolatedTargets
  · intro target _htarget other _hother _hne hcompatible
    exact ProgressionHash.LegalTriple.collisionProxy_ne
      (cwSortedPairLegalTriple encoding K q n target)
      (cwSortedPairLegalTriple encoding K q n other) hcompatible.2
  · intro target htarget
    exact (Nat.mul_le_mul_left 4
      (cwSortedPair_card_YCatchableAlternativeIndices_le_typeClass
        encoding K q n partAt rawTargets targets target)).trans
      (hquarter target htarget)
  · intro seed target other b c _htarget _hother htargetCommon hotherCommon hcompatible
    exact legalTriple_yHash_collisionProxy_eq_of_commonBuckets_of_sharesLeg
      seed (cwSortedPairLegalTriple encoding K q n target)
      (cwSortedPairLegalTriple encoding K q n other) b c
      htargetCommon hotherCommon
      (cwSortedPairCatchableCompatibilityY_sharesLeg
        encoding K q n partAt rawTargets hsupported hcompatible)

/-- `Z` counterpart of `exists_seed_many_cwSortedPairYHashIsolatedTargets`. -/
theorem exists_seed_many_cwSortedPairZHashIsolatedTargets
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsZWeightSupported)
    (targets : Finset (CWSortedPairPowerSupport K q n)) (buckets : Finset R)
    (hquarter : ∀ target ∈ targets,
      4 * (cwSortedPairZCompetitorTypeClass K q n rawTargets
        (target.1 .Z)).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * targets.card * buckets.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (ProgressionHash.Seed.compatibilityHashIsolatedTargets targets buckets
              (cwSortedPairXHashIndex encoding K q n)
              (cwSortedPairYHashIndex encoding K q n)
              (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets)
              (cwSortedPairCollisionProxy encoding K q n) seed).card ∧
        ProgressionHash.Seed.compatibilityHashIsolatedTargets targets buckets
            (cwSortedPairXHashIndex encoding K q n)
            (cwSortedPairYHashIndex encoding K q n)
            (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets)
            (cwSortedPairCollisionProxy encoding K q n) seed ⊆
          cwSortedPairCommonBucketTargets encoding K q n targets buckets seed ∧
        ProgressionHash.Seed.compatibilityHashIsolatedTargets targets buckets
            (cwSortedPairXHashIndex encoding K q n)
            (cwSortedPairYHashIndex encoding K q n)
            (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets)
            (cwSortedPairCollisionProxy encoding K q n) seed ⊆
          ProgressionHash.Seed.compatibilityIsolatedTargets
            (cwSortedPairCommonBucketTargets encoding K q n targets buckets seed)
            (cwSortedPairCatchableCompatibilityZ encoding K q n
              partAt rawTargets) := by
  apply ProgressionHash.Seed.exists_seed_many_compatibilityHashIsolatedTargets
  · intro target _htarget other _hother _hne hcompatible
    exact ProgressionHash.LegalTriple.collisionProxy_ne
      (cwSortedPairLegalTriple encoding K q n target)
      (cwSortedPairLegalTriple encoding K q n other) hcompatible.2
  · intro target htarget
    exact (Nat.mul_le_mul_left 4
      (cwSortedPair_card_ZCatchableAlternativeIndices_le_typeClass
        encoding K q n partAt rawTargets targets target)).trans
      (hquarter target htarget)
  · intro seed target other b c _htarget _hother htargetCommon hotherCommon hcompatible
    exact legalTriple_yHash_collisionProxy_eq_of_commonBuckets_of_sharesLeg
      seed (cwSortedPairLegalTriple encoding K q n target)
      (cwSortedPairLegalTriple encoding K q n other) b c
      htargetCommon hotherCommon
      (cwSortedPairCatchableCompatibilityZ_sharesLeg
        encoding K q n partAt rawTargets hsupported hcompatible)

/-- One affine seed simultaneously isolates every unequal-coarse-triple `Y` or `Z` competitor.
The quarter budget is discharged by the sum of the two exact evaluator type classes. -/
theorem exists_seed_many_cwSortedPairYZHashIsolatedTargets
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsWeightSupported)
    (targets : Finset (CWSortedPairPowerSupport K q n)) (buckets : Finset R)
    (hquarter : ∀ target ∈ targets,
      4 * ((cwSortedPairYCompetitorTypeClass K q n rawTargets
          (target.1 .Y)).card +
        (cwSortedPairZCompetitorTypeClass K q n rawTargets
          (target.1 .Z)).card) ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * targets.card * buckets.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (cwSortedPairYZHashIsolatedTargets encoding K q n partAt rawTargets
              targets buckets seed).card ∧
        cwSortedPairYZHashIsolatedTargets encoding K q n partAt rawTargets
            targets buckets seed ⊆
          cwSortedPairCommonBucketTargets encoding K q n targets buckets seed ∧
        cwSortedPairYZHashIsolatedTargets encoding K q n partAt rawTargets
            targets buckets seed ⊆
          ProgressionHash.Seed.compatibilityIsolatedTargets
            (cwSortedPairCommonBucketTargets encoding K q n targets buckets seed)
            (cwSortedPairCatchableCompatibilityYZ encoding K q n
              partAt rawTargets) := by
  apply ProgressionHash.Seed.exists_seed_many_compatibilityHashIsolatedTargets
  · intro target _htarget other _hother _hne hcompatible
    apply ProgressionHash.LegalTriple.collisionProxy_ne
      (cwSortedPairLegalTriple encoding K q n target)
      (cwSortedPairLegalTriple encoding K q n other)
    rcases hcompatible with hy | hz
    · exact hy.2
    · exact hz.2
  · intro target htarget
    exact (Nat.mul_le_mul_left 4
      (cwSortedPair_card_YZCatchableAlternativeIndices_le_typeClasses
        encoding K q n partAt rawTargets targets target)).trans
      (hquarter target htarget)
  · intro seed target other b c _htarget _hother htargetCommon hotherCommon hcompatible
    apply legalTriple_yHash_collisionProxy_eq_of_commonBuckets_of_sharesLeg
      seed (cwSortedPairLegalTriple encoding K q n target)
      (cwSortedPairLegalTriple encoding K q n other) b c
      htargetCommon hotherCommon
    rcases hcompatible with hy | hz
    · exact cwSortedPairCatchableCompatibilityY_sharesLeg
        encoding K q n partAt rawTargets hsupported.2.1 hy
    · exact cwSortedPairCatchableCompatibilityZ_sharesLeg
        encoding K q n partAt rawTargets hsupported.2.2 hz

/-- Once a target is isolated against catchable `Y` competitors, every remaining raw-compatible
address is either the target itself or an equal-coarse-triple residual. -/
theorem eq_or_residual_of_mem_cwSortedPairYCatchableIsolated
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset (CWSortedPairPowerSupport K q n))
    {target other : CWSortedPairPowerSupport K q n}
    (htarget : target ∈ ProgressionHash.Seed.compatibilityIsolatedTargets ambient
      (cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets))
    (hother : other ∈ ambient)
    (hcompatible :
      cwSortedPairCompatibilityY n partAt rawTargets (target.1 .Y) other.1) :
    other = target ∨
      cwSortedPairResidualCompatibilityY encoding K q n
        partAt rawTargets target other := by
  have hisolated := (ProgressionHash.Seed.mem_compatibilityIsolatedTargets
    ambient (cwSortedPairCatchableCompatibilityY encoding K q n partAt rawTargets)
    target).mp htarget
  by_cases heq : cwSortedPairLegalTriple encoding K q n other =
      cwSortedPairLegalTriple encoding K q n target
  · exact Or.inr ⟨hcompatible, heq⟩
  · exact Or.inl (hisolated.2 other hother ⟨hcompatible, heq⟩)

/-- `Z` analogue of `eq_or_residual_of_mem_cwSortedPairYCatchableIsolated`. -/
theorem eq_or_residual_of_mem_cwSortedPairZCatchableIsolated
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset (CWSortedPairPowerSupport K q n))
    {target other : CWSortedPairPowerSupport K q n}
    (htarget : target ∈ ProgressionHash.Seed.compatibilityIsolatedTargets ambient
      (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets))
    (hother : other ∈ ambient)
    (hcompatible :
      cwSortedPairCompatibilityZ n partAt rawTargets (target.1 .Z) other.1) :
    other = target ∨
      cwSortedPairResidualCompatibilityZ encoding K q n
        partAt rawTargets target other := by
  have hisolated := (ProgressionHash.Seed.mem_compatibilityIsolatedTargets
    ambient (cwSortedPairCatchableCompatibilityZ encoding K q n partAt rawTargets)
    target).mp htarget
  by_cases heq : cwSortedPairLegalTriple encoding K q n other =
      cwSortedPairLegalTriple encoding K q n target
  · exact Or.inr ⟨hcompatible, heq⟩
  · exact Or.inl (hisolated.2 other hother ⟨hcompatible, heq⟩)

end AlgebraicComplexity.Examples
