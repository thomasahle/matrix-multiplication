/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MarkedCompatibilityHashingIsolation
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightIsolatedSupport
import AlgebraicComplexity.MatrixMultiplication.MarkedPartitionedPowerHashing

/-!
# Single-pass total-weight compatibility hashing

This module specializes marked compatibility hashing to the total-weight quotient used by the
recursive Coppersmith--Winograd construction.  The isolated relation is the disjunction of

* ordinary equality on the legal target's `X` or `Y` hashing word; and
* total-weight `Z` feature compatibility after decoding the legal target to its modeled block
  address.

Supported total-weight compatibility is rigid: a compatible `Z` label equals the candidate's
actual `Z` word.  Therefore every pair in the combined relation shares a tensor leg, and the
generic affine collision proxy isolates both kinds of competitor in one seed.  The resulting
modeled address family has unique ambient `X` and `Y` fibers and is already semantically isolated
for the subsequent total-weight `Z` pass.

All statements are finite and certificate-parametric.  No tensor restriction, asymptotic count,
certificate table, or numerical endpoint is assumed.  In particular, this ordinary
`PartitionHashEncoding` client does not identify its `Fin (n + 1)` legal-target family with the
certificate's relaxed recursive family, whose hashing indices currently have type
`Fin ((n + 1) + (n + 1))`.  A certificate client must still provide that equality or an explicit
reindexing, prove the two proxy bounds on the literal occurrence-derived ambient family, and
derive the pre-isolation source restriction from the chosen recursive parent.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- Pull total-weight `Z` compatibility back from modeled block addresses to legal hash triples,
and combine it with ordinary `X/Y` sharing. -/
noncomputable def cwTotalWeightHashRelation
    {R : Type u} [Field R]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (left right : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target) : Prop :=
  ProgressionHash.LegalTriple.SharesXY left right ∨
    cwTotalWeightCompatibilityZ depth n partAt rawTargets
      (H.modeledAddress n left .Z) (H.modeledAddress n right)

/-- Every pair in the combined total-weight relation shares an actual legal-triple leg.  The
`Z` case is derived from total-weight support rigidity and faithful modeled-address decoding. -/
theorem cwTotalWeightHashRelation_sharesLeg
    {R : Type u} [Field R]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsZWeightSupported)
    {left right : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (hleft : left ∈ H.legalTargets n markedWords)
    (hright : right ∈ H.legalTargets n ambientWords)
    (hrelated : cwTotalWeightHashRelation depth n H partAt rawTargets left right) :
    ProgressionHash.LegalTriple.SharesLeg left right := by
  rcases hrelated with hxy | hz
  · rcases hxy with hx | hy
    · exact ⟨.X, hx⟩
    · exact ⟨.Y, hy⟩
  · have hleftAmbient : left ∈ H.legalTargets n ambientWords :=
      H.legalTargets_mono n hwords hleft
    have haddressZ : H.modeledAddress n left .Z = H.modeledAddress n right .Z :=
      cwTotalWeight_label_eq_Z_of_featureCompatibleZ
        depth n partAt rawTargets hsupported
          (H.modeledAddress n left .Z) (H.modeledAddress n right) hz
    exact ⟨.Z,
      (H.modeledAddress_leg_eq_iff
        n ambientWords hleftAmbient hright .Z).mp haddressZ⟩

/-- The single-pass proxy count is bounded by the ordinary `X/Y` proxy count plus the new
total-weight `Z`-compatibility proxy count. -/
theorem card_cwTotalWeightHashRelation_alternatives_le
    {R : Type u} [Field R]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords : Finset (PositiveWord support n))
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (left : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target) :
    (ProgressionHash.Seed.compatibilityAlternativeIndices
      (H.legalTargets n ambientWords)
      (cwTotalWeightHashRelation depth n H partAt rawTargets)
      ProgressionHash.LegalTriple.collisionProxy left).card ≤
        (ProgressionHash.LegalTriple.xyCompetitorYIndices
          (H.legalTargets n ambientWords) left).card +
        (ProgressionHash.Seed.compatibilityAlternativeIndices
          (H.legalTargets n ambientWords)
          (fun first second ↦ cwTotalWeightCompatibilityZ depth n partAt rawTargets
            (H.modeledAddress n first .Z) (H.modeledAddress n second))
          ProgressionHash.LegalTriple.collisionProxy left).card := by
  have h := ProgressionHash.Seed.card_compatibilityAlternativeIndices_or_le_add
    (H.legalTargets n ambientWords)
    ProgressionHash.LegalTriple.SharesXY
    (fun first second ↦ cwTotalWeightCompatibilityZ depth n partAt rawTargets
      (H.modeledAddress n first .Z) (H.modeledAddress n second))
    ProgressionHash.LegalTriple.collisionProxy left
  change
    (ProgressionHash.Seed.compatibilityAlternativeIndices
      (H.legalTargets n ambientWords)
      (fun first second ↦ ProgressionHash.LegalTriple.SharesXY first second ∨
        cwTotalWeightCompatibilityZ depth n partAt rawTargets
          (H.modeledAddress n first .Z) (H.modeledAddress n second))
      ProgressionHash.LegalTriple.collisionProxy left).card ≤
        (ProgressionHash.LegalTriple.xyCompetitorYIndices
          (H.legalTargets n ambientWords) left).card +
        (ProgressionHash.Seed.compatibilityAlternativeIndices
          (H.legalTargets n ambientWords)
          (fun first second ↦ cwTotalWeightCompatibilityZ depth n partAt rawTargets
            (H.modeledAddress n first .Z) (H.modeledAddress n second))
          ProgressionHash.LegalTriple.collisionProxy left).card
  simpa only [
    ProgressionHash.LegalTriple.compatibilityAlternativeIndices_sharesXY_eq_xyCompetitorYIndices]
    using h

/-- Legal triples selected by the single affine pass. -/
noncomputable def cwTotalWeightHashIsolatedTargets
    {R : Type u} [Field R]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (B : Finset R) (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :=
  ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
    (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B
    ProgressionHash.LegalTriple.xIndex ProgressionHash.LegalTriple.yIndex
    (cwTotalWeightHashRelation depth n H partAt rawTargets)
    ProgressionHash.LegalTriple.collisionProxy seed

/-- Original block addresses represented by the single-pass selected legal triples. -/
noncomputable def cwTotalWeightHashIsolatedPowerAddresses
    {R : Type u} [Field R]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (B : Finset R) (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :=
  H.modeledAddresses n
    (cwTotalWeightHashIsolatedTargets
      depth n H ambientWords markedWords B partAt rawTargets seed)

/-- Modeling preserves the cardinality of the single-pass selected legal-triple family. -/
theorem card_cwTotalWeightHashIsolatedPowerAddresses
    {R : Type u} [Field R]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    (cwTotalWeightHashIsolatedPowerAddresses
      depth n H ambientWords markedWords B partAt rawTargets seed).card =
      (cwTotalWeightHashIsolatedTargets
        depth n H ambientWords markedWords B partAt rawTargets seed).card := by
  apply H.card_modeledAddresses_of_subset n ambientWords
  exact (ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets_subset_marked
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B
      ProgressionHash.LegalTriple.xIndex ProgressionHash.LegalTriple.yIndex
      (cwTotalWeightHashRelation depth n H partAt rawTargets)
      ProgressionHash.LegalTriple.collisionProxy seed).trans
    (H.legalTargets_mono n hwords)

/-- The selected legal triples lie in the ordinary ambient progression-free hash filter. -/
theorem cwTotalWeightHashIsolatedTargets_subset_filteredTargets
    {R : Type u} [Field R] [NeZero (2 : R)]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    cwTotalWeightHashIsolatedTargets
        depth n H ambientWords markedWords B partAt rawTargets seed ⊆
      ProgressionHash.LegalTriple.filteredTargets
        (H.legalTargets n ambientWords) B seed := by
  change ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B
      ProgressionHash.LegalTriple.xIndex ProgressionHash.LegalTriple.yIndex
      (cwTotalWeightHashRelation depth n H partAt rawTargets)
      ProgressionHash.LegalTriple.collisionProxy seed ⊆ _
  rw [← ProgressionHash.LegalTriple.commonBucketFilteredTargets_eq_filteredTargets
    (H.legalTargets n ambientWords) B hB seed]
  exact ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets_subset_commonBucketFilteredTargets
    (H.legalTargets n ambientWords) (H.legalTargets n markedWords)
    (H.legalTargets_mono n hwords) B
    ProgressionHash.LegalTriple.xIndex ProgressionHash.LegalTriple.yIndex
    (cwTotalWeightHashRelation depth n H partAt rawTargets)
    ProgressionHash.LegalTriple.collisionProxy seed

/-- The selected legal triples are uniquely related inside the full ambient filtered family. -/
theorem cwTotalWeightHashIsolatedTargets_subset_relationIsolatedTargets
    {R : Type u} [Field R] [NeZero (2 : R)]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsZWeightSupported)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    cwTotalWeightHashIsolatedTargets
        depth n H ambientWords markedWords B partAt rawTargets seed ⊆
      ProgressionHash.Seed.compatibilityIsolatedTargets
        (ProgressionHash.LegalTriple.filteredTargets
          (H.legalTargets n ambientWords) B seed)
        (cwTotalWeightHashRelation depth n H partAt rawTargets) := by
  change ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B
      ProgressionHash.LegalTriple.xIndex ProgressionHash.LegalTriple.yIndex
      (cwTotalWeightHashRelation depth n H partAt rawTargets)
      ProgressionHash.LegalTriple.collisionProxy seed ⊆ _
  rw [← ProgressionHash.LegalTriple.commonBucketFilteredTargets_eq_filteredTargets
    (H.legalTargets n ambientWords) B hB seed]
  apply ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets_subset_compatibilityIsolatedTargets
    (H.legalTargets n ambientWords) (H.legalTargets n markedWords)
    (H.legalTargets_mono n hwords) B
    ProgressionHash.LegalTriple.xIndex ProgressionHash.LegalTriple.yIndex
    (cwTotalWeightHashRelation depth n H partAt rawTargets)
    ProgressionHash.LegalTriple.collisionProxy seed
  intro left right leftBucket rightBucket hleft hright hleftCommon hrightCommon hrelated
  exact ProgressionHash.LegalTriple.yHash_collisionProxy_eq_of_commonBuckets_of_sharesLeg
    seed left right leftBucket rightBucket hleftCommon hrightCommon
      (cwTotalWeightHashRelation_sharesLeg
        depth n H ambientWords markedWords hwords partAt rawTargets hsupported
          hleft hright hrelated)

/-- The selected modeled addresses remain inside the full ambient hash-filtered partition. -/
theorem cwTotalWeightHashIsolatedPowerAddresses_subset_filteredPowerAddresses
    {R : Type u} [Field R] [NeZero (2 : R)]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    cwTotalWeightHashIsolatedPowerAddresses
        depth n H ambientWords markedWords B partAt rawTargets seed ⊆
      H.filteredPowerAddresses n ambientWords B seed := by
  exact Finset.image_mono _
    (cwTotalWeightHashIsolatedTargets_subset_filteredTargets
      depth n H ambientWords markedWords hwords B hB partAt rawTargets seed)

/-- Every selected modeled address is the unique ambient filtered address in both its `X` and
its `Y` fiber. -/
theorem cwTotalWeightHashIsolatedPowerAddresses_hasUniqueXYFibers
    {R : Type u} [Field R] [NeZero (2 : R)]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsZWeightSupported)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    HasUniqueLegFibers (H.filteredPowerAddresses n ambientWords B seed)
        (cwTotalWeightHashIsolatedPowerAddresses
          depth n H ambientWords markedWords B partAt rawTargets seed) .X ∧
      HasUniqueLegFibers (H.filteredPowerAddresses n ambientWords B seed)
        (cwTotalWeightHashIsolatedPowerAddresses
          depth n H ambientWords markedWords B partAt rawTargets seed) .Y := by
  classical
  let selectedTargets := cwTotalWeightHashIsolatedTargets
    depth n H ambientWords markedWords B partAt rawTargets seed
  let selectedAddresses := cwTotalWeightHashIsolatedPowerAddresses
    depth n H ambientWords markedWords B partAt rawTargets seed
  have hselectedFiltered : selectedTargets ⊆
      ProgressionHash.LegalTriple.filteredTargets
        (H.legalTargets n ambientWords) B seed :=
    cwTotalWeightHashIsolatedTargets_subset_filteredTargets
      depth n H ambientWords markedWords hwords B hB partAt rawTargets seed
  have hselectedIsolated : selectedTargets ⊆
      ProgressionHash.Seed.compatibilityIsolatedTargets
        (ProgressionHash.LegalTriple.filteredTargets
          (H.legalTargets n ambientWords) B seed)
        (cwTotalWeightHashRelation depth n H partAt rawTargets) :=
    cwTotalWeightHashIsolatedTargets_subset_relationIsolatedTargets
      depth n H ambientWords markedWords hwords B hB partAt rawTargets hsupported seed
  have haddressSubset : selectedAddresses ⊆ H.filteredPowerAddresses n ambientWords B seed :=
    cwTotalWeightHashIsolatedPowerAddresses_subset_filteredPowerAddresses
      depth n H ambientWords markedWords hwords B hB partAt rawTargets seed
  have hunique (pivot : Leg) (hpivot : pivot = .X ∨ pivot = .Y) :
      HasUniqueLegFibers (H.filteredPowerAddresses n ambientWords B seed)
        selectedAddresses pivot := by
    refine ⟨haddressSubset, ?_⟩
    intro selected hselected other hother hleg
    unfold selectedAddresses cwTotalWeightHashIsolatedPowerAddresses
      PartitionHashEncoding.modeledAddresses at hselected
    obtain ⟨selectedTriple, hselectedTriple, rfl⟩ := Finset.mem_image.mp hselected
    unfold PartitionHashEncoding.filteredPowerAddresses
      PartitionHashEncoding.modeledAddresses at hother
    obtain ⟨otherTriple, hotherTriple, rfl⟩ := Finset.mem_image.mp hother
    have hselectedAmbient : selectedTriple ∈ H.legalTargets n ambientWords :=
      ProgressionHash.LegalTriple.filteredTargets_subset
        (H.legalTargets n ambientWords) B seed (hselectedFiltered hselectedTriple)
    have hotherAmbient : otherTriple ∈ H.legalTargets n ambientWords :=
      ProgressionHash.LegalTriple.filteredTargets_subset
        (H.legalTargets n ambientWords) B seed hotherTriple
    have hindex : otherTriple.legIndex pivot = selectedTriple.legIndex pivot :=
      (H.modeledAddress_leg_eq_iff
        n ambientWords hotherAmbient hselectedAmbient pivot).mp hleg
    have hshares : ProgressionHash.LegalTriple.SharesXY selectedTriple otherTriple := by
      rcases hpivot with rfl | rfl
      · exact Or.inl hindex.symm
      · exact Or.inr hindex.symm
    have hisolated := (ProgressionHash.Seed.mem_compatibilityIsolatedTargets
      (ProgressionHash.LegalTriple.filteredTargets
        (H.legalTargets n ambientWords) B seed)
      (cwTotalWeightHashRelation depth n H partAt rawTargets) selectedTriple).mp
        (hselectedIsolated hselectedTriple)
    have heq : otherTriple = selectedTriple :=
      hisolated.2 otherTriple hotherTriple (Or.inl hshares)
    subst otherTriple
    rfl
  exact ⟨hunique .X (Or.inl rfl), hunique .Y (Or.inr rfl)⟩

/-- A selected address is the unique total-weight `Z`-compatible address in the entire ambient
filtered family, even though literal `Z`-injectivity is not assumed. -/
theorem cwTotalWeightHashIsolatedPowerAddresses_zIsolatedAgainstFiltered
    {R : Type u} [Field R] [NeZero (2 : R)]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsZWeightSupported)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    ∀ selected ∈ cwTotalWeightHashIsolatedPowerAddresses
        depth n H ambientWords markedWords B partAt rawTargets seed,
      ∀ other ∈ H.filteredPowerAddresses n ambientWords B seed,
        cwTotalWeightCompatibilityZ depth n partAt rawTargets (selected .Z) other →
          other = selected := by
  classical
  intro selected hselected other hother hz
  unfold cwTotalWeightHashIsolatedPowerAddresses
    PartitionHashEncoding.modeledAddresses at hselected
  obtain ⟨selectedTriple, hselectedTriple, rfl⟩ := Finset.mem_image.mp hselected
  unfold PartitionHashEncoding.filteredPowerAddresses
    PartitionHashEncoding.modeledAddresses at hother
  obtain ⟨otherTriple, hotherTriple, rfl⟩ := Finset.mem_image.mp hother
  have hisolated := cwTotalWeightHashIsolatedTargets_subset_relationIsolatedTargets
    depth n H ambientWords markedWords hwords B hB partAt rawTargets hsupported seed
      hselectedTriple
  have heq : otherTriple = selectedTriple :=
    ((ProgressionHash.Seed.mem_compatibilityIsolatedTargets
      (ProgressionHash.LegalTriple.filteredTargets
        (H.legalTargets n ambientWords) B seed)
      (cwTotalWeightHashRelation depth n H partAt rawTargets) selectedTriple).mp hisolated).2
        otherTriple hotherTriple (Or.inr hz)
  subst otherTriple
  rfl

/-- The ordinary sequential total-weight `Y/Z` cleanup is the identity on a family produced by
the single-pass hash.  The `Y` step uses unique `Y` fibers; the `Z` step uses semantic isolation,
not literal `Z`-injectivity.  This is an equality of the finite cleanup support selectors; a tensor
zeroing client must still supply the first-zero-out exact and pooled profile equations that prove
compatibility soundness. -/
theorem cwTotalWeightYZIsolatedSupport_hashIsolated_eq
    {R : Type u} [Field R] [NeZero (2 : R)]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
        (cwTotalWeightHashIsolatedPowerAddresses
          depth n H ambientWords markedWords B partAt rawTargets seed) =
      cwTotalWeightHashIsolatedPowerAddresses
        depth n H ambientWords markedWords B partAt rawTargets seed := by
  let selected := cwTotalWeightHashIsolatedPowerAddresses
    depth n H ambientWords markedWords B partAt rawTargets seed
  have hXY := cwTotalWeightHashIsolatedPowerAddresses_hasUniqueXYFibers
    depth n H ambientWords markedWords hwords B hB partAt rawTargets hsupported.2.2 seed
  have hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y) selected := by
    intro left hleft right hright heq
    exact hXY.2.2 right hright left (hXY.2.1 hleft) heq
  rw [cwTotalWeightYZIsolatedSupport,
    cwTotalWeightYIsolatedSupport_eq_ambient_of_injOn
      depth n partAt rawTargets hsupported.2.1 selected hY]
  apply Finset.Subset.antisymm
  · exact compatibilityIsolatedSupport_subset selected .Z
      (cwTotalWeightCompatibilityZ depth n partAt rawTargets)
  · intro address haddress
    rw [mem_compatibilityIsolatedSupport]
    refine ⟨haddress, ?_⟩
    intro other hother hcompatible
    exact cwTotalWeightHashIsolatedPowerAddresses_zIsolatedAgainstFiltered
      depth n H ambientWords markedWords hwords B hB partAt rawTargets hsupported.2.2 seed
        address haddress other (hXY.1.1 hother) hcompatible

/-- One affine seed simultaneously supplies the marked count, unique ambient `X/Y` fibers,
semantic total-weight `Z` isolation, and lossless sequential cleanup.  The proxy budget is stated
as the sum of the separately checkable ordinary and total-weight competitor families. -/
theorem exists_seed_many_cwTotalWeightHashIsolatedPowerAddresses
    {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported)
    (hquarter : ∀ left ∈ H.legalTargets n markedWords,
      4 * ((ProgressionHash.LegalTriple.xyCompetitorYIndices
          (H.legalTargets n ambientWords) left).card +
        (ProgressionHash.Seed.compatibilityAlternativeIndices
          (H.legalTargets n ambientWords)
          (fun first second ↦ cwTotalWeightCompatibilityZ depth n partAt rawTargets
            (H.modeledAddress n first .Z) (H.modeledAddress n second))
          ProgressionHash.LegalTriple.collisionProxy left).card) ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (cwTotalWeightHashIsolatedPowerAddresses
              depth n H ambientWords markedWords B partAt rawTargets seed).card ∧
        HasUniqueLegFibers (H.filteredPowerAddresses n ambientWords B seed)
            (cwTotalWeightHashIsolatedPowerAddresses
              depth n H ambientWords markedWords B partAt rawTargets seed) .X ∧
        HasUniqueLegFibers (H.filteredPowerAddresses n ambientWords B seed)
            (cwTotalWeightHashIsolatedPowerAddresses
              depth n H ambientWords markedWords B partAt rawTargets seed) .Y ∧
        (∀ selected ∈ cwTotalWeightHashIsolatedPowerAddresses
            depth n H ambientWords markedWords B partAt rawTargets seed,
          ∀ other ∈ H.filteredPowerAddresses n ambientWords B seed,
            cwTotalWeightCompatibilityZ depth n partAt rawTargets (selected .Z) other →
              other = selected) ∧
        cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
            (cwTotalWeightHashIsolatedPowerAddresses
              depth n H ambientWords markedWords B partAt rawTargets seed) =
          cwTotalWeightHashIsolatedPowerAddresses
            depth n H ambientWords markedWords B partAt rawTargets seed := by
  have hmarked : H.legalTargets n markedWords ⊆ H.legalTargets n ambientWords :=
    H.legalTargets_mono n hwords
  have hcombinedQuarter : ∀ left ∈ H.legalTargets n markedWords,
      4 * (ProgressionHash.Seed.compatibilityAlternativeIndices
        (H.legalTargets n ambientWords)
        (cwTotalWeightHashRelation depth n H partAt rawTargets)
        ProgressionHash.LegalTriple.collisionProxy left).card ≤ Fintype.card R := by
    intro left hleft
    exact (Nat.mul_le_mul_left 4
      (card_cwTotalWeightHashRelation_alternatives_le
        depth n H ambientWords partAt rawTargets left)).trans (hquarter left hleft)
  obtain ⟨seed, hcount, _hfiltered, _hisolated⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_markedCompatibilityHashIsolatedLegalTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) hmarked B
      (cwTotalWeightHashRelation depth n H partAt rawTargets)
      (fun left hleft right hright hrelated ↦
        cwTotalWeightHashRelation_sharesLeg
          depth n H ambientWords markedWords hwords partAt rawTargets hsupported.2.2
            hleft hright hrelated)
      hcombinedQuarter
  have hcount' : 3 * markedWords.card * B.card ≤
      4 * (Fintype.card R * Fintype.card R) *
        (cwTotalWeightHashIsolatedPowerAddresses
          depth n H ambientWords markedWords B partAt rawTargets seed).card := by
    rw [card_cwTotalWeightHashIsolatedPowerAddresses
      depth n H ambientWords markedWords hwords B partAt rawTargets seed,
      cwTotalWeightHashIsolatedTargets, ← H.card_legalTargets n markedWords]
    exact hcount
  have hXY := cwTotalWeightHashIsolatedPowerAddresses_hasUniqueXYFibers
    depth n H ambientWords markedWords hwords B hB partAt rawTargets hsupported.2.2 seed
  exact ⟨seed, hcount', hXY.1, hXY.2,
    cwTotalWeightHashIsolatedPowerAddresses_zIsolatedAgainstFiltered
      depth n H ambientWords markedWords hwords B hB partAt rawTargets hsupported.2.2 seed,
    cwTotalWeightYZIsolatedSupport_hashIsolated_eq
      depth n H ambientWords markedWords hwords B hB partAt rawTargets hsupported seed⟩

end AlgebraicComplexity.Examples
