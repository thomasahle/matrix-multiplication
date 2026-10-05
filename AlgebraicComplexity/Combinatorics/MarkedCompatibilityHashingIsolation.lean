/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.CompatibilityHashingIsolation
import AlgebraicComplexity.Combinatorics.MarkedTwoLegHashingExtraction

/-!
# Marked compatibility isolation by affine hashing

Affine-hashing clients often distinguish a marked family, whose cardinality supplies the retained
copy count, from a larger ambient family, against which every collision must be removed.  The
unmarked compatibility theorem in `CompatibilityHashingIsolation` handles only the special case
in which these two families coincide.  This module proves the marked form.

The selected family is counted against `marked`, while its alternative indices, common-bucket
ambient, and semantic compatibility isolation all use `ambient`.  Thus replacing `ambient` by
`marked` cannot silently weaken the zeroing conclusion.  The theorem is finite and exact; it
contains no tensor, entropy, asymptotic, or matrix-multiplication input.

The legal-triple specialization uses the standard collision proxy.  Any relation whose unequal
pairs share at least one tensor leg can therefore be isolated in the same affine pass as ordinary
X/Y competitors.  The tiny client at the end is genuinely marked: one selected target is isolated
against a two-target ambient family.
-/

namespace AlgebraicComplexity

universe u v w

namespace ProgressionHash.Seed

variable {R : Type u} [Field R] [Fintype R]
variable {ι : Type v} [Fintype ι]
variable {τ : Type w}

omit [Fintype R] in
/-- Isolation is antitone in the alternative-index family: checking more possible collisions can
only remove targets.  The containment premise is needed only on the finite target family, which
keeps certificate clients from proving irrelevant global facts about their proxy functions. -/
theorem isolatedTargets_anti_alternatives
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (small large : τ → Finset (ι → R))
    (seed : ProgressionHash.Seed R ι)
    (hsub : ∀ target ∈ targets, small target ⊆ large target) :
    isolatedTargets targets buckets xIndex yIndex large seed ⊆
      isolatedTargets targets buckets xIndex yIndex small seed := by
  classical
  intro target htarget
  unfold isolatedTargets at htarget ⊢
  obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp htarget
  refine Finset.mem_image.mpr ⟨pair, ?_, rfl⟩
  unfold isolatedIncidences at hpair ⊢
  have hlarge := Finset.mem_filter.mp hpair
  have hpairMem := Finset.mem_product.mp hlarge.1
  refine Finset.mem_filter.mpr ⟨hlarge.1, hlarge.2.1, ?_⟩
  intro alternative halternative
  exact hlarge.2.2 alternative (hsub pair.1 hpairMem.1 halternative)

omit [Field R] [Fintype R] in
/-- Collision indices for a disjunction of compatibility relations lie in the union of the two
separate collision-index families.  This is the finite union bound used when ordinary leg
collisions and a new semantic compatibility relation are isolated in one affine pass. -/
theorem compatibilityAlternativeIndices_or_subset_union
    (targets : Finset τ) (left right : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R) (target : τ) :
    ∀ alternative ∈ compatibilityAlternativeIndices targets
        (fun first second ↦ left first second ∨ right first second)
        collisionIndex target,
      alternative ∈ compatibilityAlternativeIndices targets left collisionIndex target ∨
        alternative ∈
          compatibilityAlternativeIndices targets right collisionIndex target := by
  classical
  intro alternative halternative
  obtain ⟨other, hother, hne, hcompatible, rfl⟩ :=
    (mem_compatibilityAlternativeIndices _ _ _ _ _).mp halternative
  rcases hcompatible with hleft | hright
  · exact Or.inl ((mem_compatibilityAlternativeIndices _ _ _ _ _).mpr
      ⟨other, hother, hne, hleft, rfl⟩)
  · exact Or.inr ((mem_compatibilityAlternativeIndices _ _ _ _ _).mpr
      ⟨other, hother, hne, hright, rfl⟩)

omit [Field R] [Fintype R] in
/-- Cardinal form of `compatibilityAlternativeIndices_or_subset_union`. -/
theorem card_compatibilityAlternativeIndices_or_le_add
    (targets : Finset τ) (left right : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R) (target : τ) :
    (compatibilityAlternativeIndices targets
      (fun first second ↦ left first second ∨ right first second)
      collisionIndex target).card ≤
        (compatibilityAlternativeIndices targets left collisionIndex target).card +
          (compatibilityAlternativeIndices targets right collisionIndex target).card := by
  classical
  calc
    (compatibilityAlternativeIndices targets
      (fun first second ↦ left first second ∨ right first second)
      collisionIndex target).card ≤
        (compatibilityAlternativeIndices targets left collisionIndex target ∪
          compatibilityAlternativeIndices targets right collisionIndex target).card := by
      apply Finset.card_le_card
      intro alternative halternative
      rcases compatibilityAlternativeIndices_or_subset_union
          targets left right collisionIndex target alternative halternative with
        hleft | hright
      · exact Finset.mem_union_left _ hleft
      · exact Finset.mem_union_right _ hright
    _ ≤ (compatibilityAlternativeIndices targets left collisionIndex target).card +
          (compatibilityAlternativeIndices targets right collisionIndex target).card :=
      Finset.card_union_le _ _

/-- The marked affine selection whose alternatives are computed in the larger ambient family. -/
noncomputable def markedCompatibilityHashIsolatedTargets
    (ambient marked : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R) (compatible : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R)
    (seed : ProgressionHash.Seed R ι) : Finset τ :=
  isolatedTargets marked buckets xIndex yIndex
    (compatibilityAlternativeIndices ambient compatible collisionIndex) seed

omit [Fintype R] in
/-- Marked compatibility isolation never introduces a target outside the marked family. -/
theorem markedCompatibilityHashIsolatedTargets_subset_marked
    (ambient marked : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R) (compatible : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R)
    (seed : ProgressionHash.Seed R ι) :
    markedCompatibilityHashIsolatedTargets ambient marked buckets xIndex yIndex
        compatible collisionIndex seed ⊆ marked := by
  classical
  intro target htarget
  unfold markedCompatibilityHashIsolatedTargets isolatedTargets at htarget
  obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp htarget
  exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).1

omit [Fintype R] in
/-- Every marked isolated target survives the common-bucket filter of the full ambient family. -/
theorem markedCompatibilityHashIsolatedTargets_subset_commonBucketFilteredTargets
    (ambient marked : Finset τ) (hmarked : marked ⊆ ambient)
    (buckets : Finset R) (xIndex yIndex : τ → ι → R)
    (compatible : τ → τ → Prop) (collisionIndex : τ → τ → ι → R)
    (seed : ProgressionHash.Seed R ι) :
    markedCompatibilityHashIsolatedTargets ambient marked buckets xIndex yIndex
        compatible collisionIndex seed ⊆
      commonBucketFilteredTargets ambient buckets xIndex yIndex seed := by
  classical
  intro target htarget
  have himage : target ∈ isolatedTargets marked buckets xIndex yIndex
      (compatibilityAlternativeIndices ambient compatible collisionIndex) seed := by
    simpa only [markedCompatibilityHashIsolatedTargets] using htarget
  obtain ⟨⟨target', bucket⟩, hincidence, hfirst⟩ := Finset.mem_image.mp himage
  simp only at hfirst
  subst target'
  have hfilter := Finset.mem_filter.mp hincidence
  have hpair := Finset.mem_product.mp hfilter.1
  exact (mem_commonBucketFilteredTargets ambient buckets xIndex yIndex seed target).mpr
    ⟨hmarked hpair.1, bucket, hpair.2, hfilter.2.1⟩

omit [Fintype R] in
/-- Avoiding every ambient compatibility proxy makes each selected marked target uniquely
compatible inside the ambient common-bucket family. -/
theorem markedCompatibilityHashIsolatedTargets_subset_compatibilityIsolatedTargets
    (ambient marked : Finset τ) (hmarked : marked ⊆ ambient)
    (buckets : Finset R) (xIndex yIndex : τ → ι → R)
    (compatible : τ → τ → Prop) (collisionIndex : τ → τ → ι → R)
    (seed : ProgressionHash.Seed R ι)
    (hcollision : ∀ target other targetBucket otherBucket,
      target ∈ marked → other ∈ ambient →
      InCommonBucket (xIndex target) (yIndex target) targetBucket seed →
      InCommonBucket (xIndex other) (yIndex other) otherBucket seed →
      compatible target other → seed.yHash (collisionIndex target other) = targetBucket) :
    markedCompatibilityHashIsolatedTargets ambient marked buckets xIndex yIndex
        compatible collisionIndex seed ⊆
      compatibilityIsolatedTargets
        (commonBucketFilteredTargets ambient buckets xIndex yIndex seed) compatible := by
  classical
  intro target htarget
  have himage : target ∈ isolatedTargets marked buckets xIndex yIndex
      (compatibilityAlternativeIndices ambient compatible collisionIndex) seed := by
    simpa only [markedCompatibilityHashIsolatedTargets] using htarget
  obtain ⟨⟨target', bucket⟩, hincidence, hfirst⟩ := Finset.mem_image.mp himage
  simp only at hfirst
  subst target'
  have hfilter := Finset.mem_filter.mp hincidence
  have hpair := Finset.mem_product.mp hfilter.1
  have htargetMarked : target ∈ marked := hpair.1
  have htargetCommon : InCommonBucket (xIndex target) (yIndex target) bucket seed := hfilter.2.1
  apply (mem_compatibilityIsolatedTargets _ _ _).mpr
  refine ⟨(mem_commonBucketFilteredTargets ambient buckets xIndex yIndex seed target).mpr
    ⟨hmarked htargetMarked, bucket, hpair.2, htargetCommon⟩, ?_⟩
  intro other hother hcompatible
  obtain ⟨hotherAmbient, otherBucket, _hotherBucket, hotherCommon⟩ :=
    (mem_commonBucketFilteredTargets ambient buckets xIndex yIndex seed other).mp hother
  by_contra hne
  have hindex : collisionIndex target other ∈
      compatibilityAlternativeIndices ambient compatible collisionIndex target :=
    (mem_compatibilityAlternativeIndices _ _ _ _ _).mpr
      ⟨other, hotherAmbient, hne, hcompatible, rfl⟩
  exact hfilter.2.2 _ hindex
    (hcollision target other bucket otherBucket htargetMarked hotherAmbient
      htargetCommon hotherCommon hcompatible)

/-- Complete marked good-seed theorem for compatibility isolation.

The count is measured against `marked`; the proxy budget and the semantic uniqueness conclusion
are measured against `ambient`.  This is the marked/ambient acceptance boundary needed by refined
laser-method clients. -/
theorem exists_seed_many_markedCompatibilityHashIsolatedTargets
    (ambient marked : Finset τ) (hmarked : marked ⊆ ambient)
    (buckets : Finset R) (xIndex yIndex : τ → ι → R)
    (compatible : τ → τ → Prop) (collisionIndex : τ → τ → ι → R)
    (hdistinct : ∀ target ∈ marked, ∀ other ∈ ambient,
      other ≠ target → compatible target other →
        collisionIndex target other ≠ yIndex target)
    (hquarter : ∀ target ∈ marked,
      4 * (compatibilityAlternativeIndices ambient compatible collisionIndex target).card ≤
        Fintype.card R)
    (hcollision : ∀ seed : ProgressionHash.Seed R ι,
      ∀ target other targetBucket otherBucket,
      target ∈ marked → other ∈ ambient →
      InCommonBucket (xIndex target) (yIndex target) targetBucket seed →
      InCommonBucket (xIndex other) (yIndex other) otherBucket seed →
      compatible target other → seed.yHash (collisionIndex target other) = targetBucket) :
    ∃ seed : ProgressionHash.Seed R ι,
      3 * marked.card * buckets.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (markedCompatibilityHashIsolatedTargets ambient marked buckets xIndex yIndex
              compatible collisionIndex seed).card ∧
        markedCompatibilityHashIsolatedTargets ambient marked buckets xIndex yIndex
            compatible collisionIndex seed ⊆
          commonBucketFilteredTargets ambient buckets xIndex yIndex seed ∧
        markedCompatibilityHashIsolatedTargets ambient marked buckets xIndex yIndex
            compatible collisionIndex seed ⊆
          compatibilityIsolatedTargets
            (commonBucketFilteredTargets ambient buckets xIndex yIndex seed) compatible := by
  classical
  have hindicesDistinct : ∀ target ∈ marked,
      ∀ index ∈ compatibilityAlternativeIndices ambient compatible collisionIndex target,
        index ≠ yIndex target := by
    intro target htarget index hindex
    obtain ⟨other, hother, hne, hcompatible, rfl⟩ :=
      (mem_compatibilityAlternativeIndices _ _ _ _ _).mp hindex
    exact hdistinct target htarget other hother hne hcompatible
  obtain ⟨seed, hcount⟩ := exists_seed_many_isolatedTargets marked buckets xIndex yIndex
    (compatibilityAlternativeIndices ambient compatible collisionIndex)
    hindicesDistinct hquarter
  refine ⟨seed, ?_,
    markedCompatibilityHashIsolatedTargets_subset_commonBucketFilteredTargets
      ambient marked hmarked buckets xIndex yIndex compatible collisionIndex seed,
    markedCompatibilityHashIsolatedTargets_subset_compatibilityIsolatedTargets
      ambient marked hmarked buckets xIndex yIndex compatible collisionIndex seed
        (hcollision seed)⟩
  simpa only [markedCompatibilityHashIsolatedTargets] using hcount

end ProgressionHash.Seed

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
variable {ι : Type v} [Fintype ι]
variable {target : R}

omit [Fintype R] in
/-- On legal triples, the generic common-bucket ambient is exactly the standard three-leg
progression-free hash filter.  This bridge lets compatibility-isolation clients reuse the tensor
zeroing API without comparing two independently defined survivor families. -/
theorem commonBucketFilteredTargets_eq_filteredTargets
    (targets : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (hbuckets : ThreeAPFree (buckets : Set R))
    (seed : ProgressionHash.Seed R ι) :
    ProgressionHash.Seed.commonBucketFilteredTargets targets buckets
        LegalTriple.xIndex LegalTriple.yIndex seed =
      filteredTargets targets buckets seed := by
  classical
  ext triple
  rw [ProgressionHash.Seed.mem_commonBucketFilteredTargets,
    mem_filteredTargets targets buckets hbuckets seed triple]

omit [Fintype R] [NeZero (2 : R)] in
/-- The ordinary two-leg proxy family is the generic compatibility-index family for `SharesXY`.
This definitional bridge makes the single-pass disjunction budget split into the existing
two-leg budget plus the new semantic-compatibility budget. -/
theorem compatibilityAlternativeIndices_sharesXY_eq_xyCompetitorYIndices
    (targets : Finset (LegalTriple R ι target))
    (triple : LegalTriple R ι target) :
    ProgressionHash.Seed.compatibilityAlternativeIndices
        targets SharesXY collisionProxy triple =
      xyCompetitorYIndices targets triple := rfl

omit [Fintype R] in
/-- Two legal triples in common buckets that share any tensor leg turn the standard collision
proxy into a collision with the first triple's bucket. -/
theorem yHash_collisionProxy_eq_of_commonBuckets_of_sharesLeg
    (seed : ProgressionHash.Seed R ι)
    (left right : LegalTriple R ι target) (leftBucket rightBucket : R)
    (hleft : ProgressionHash.Seed.InCommonBucket
      left.xIndex left.yIndex leftBucket seed)
    (hright : ProgressionHash.Seed.InCommonBucket
      right.xIndex right.yIndex rightBucket seed)
    (hshare : SharesLeg left right) :
    seed.yHash (collisionProxy left right) = leftBucket := by
  obtain ⟨leg, hleg⟩ := hshare
  have hbucket : rightBucket = leftBucket :=
    commonBucket_eq_of_legIndex_eq seed left right leftBucket rightBucket
      hleft hright leg hleg.symm
  unfold collisionProxy
  split_ifs with hx
  · exact hright.2.trans hbucket
  · rw [ProgressionHash.Seed.yHash_transportXAlternative_eq_xHash seed
      left.xIndex left.yIndex right.xIndex leftBucket hleft]
    exact hright.1.trans hbucket

/-- Legal-triple specialization of marked compatibility isolation.  The only semantic premise on
the relation is that every compatible unequal pair shares some tensor leg; the standard collision
proxy supplies both collision distinctness and the affine collision equation. -/
theorem exists_seed_many_markedCompatibilityHashIsolatedLegalTargets
    (ambient marked : Finset (LegalTriple R ι target)) (hmarked : marked ⊆ ambient)
    (buckets : Finset R) (compatible : LegalTriple R ι target → LegalTriple R ι target → Prop)
    (hshare : ∀ left ∈ marked, ∀ right ∈ ambient,
      compatible left right → SharesLeg left right)
    (hquarter : ∀ left ∈ marked,
      4 * (ProgressionHash.Seed.compatibilityAlternativeIndices ambient compatible
        collisionProxy left).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R ι,
      3 * marked.card * buckets.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
              ambient marked buckets LegalTriple.xIndex LegalTriple.yIndex
              compatible collisionProxy seed).card ∧
        ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
            ambient marked buckets LegalTriple.xIndex LegalTriple.yIndex
            compatible collisionProxy seed ⊆
          ProgressionHash.Seed.commonBucketFilteredTargets
            ambient buckets LegalTriple.xIndex LegalTriple.yIndex seed ∧
        ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
            ambient marked buckets LegalTriple.xIndex LegalTriple.yIndex
            compatible collisionProxy seed ⊆
          ProgressionHash.Seed.compatibilityIsolatedTargets
            (ProgressionHash.Seed.commonBucketFilteredTargets
              ambient buckets LegalTriple.xIndex LegalTriple.yIndex seed) compatible := by
  apply ProgressionHash.Seed.exists_seed_many_markedCompatibilityHashIsolatedTargets
  · exact hmarked
  · intro left _hleft right _hright hne _hcompatible
    exact collisionProxy_ne left right hne
  · exact hquarter
  · intro seed left right leftBucket rightBucket hleftMem hrightMem
      hleftCommon hrightCommon hcompatible
    exact yHash_collisionProxy_eq_of_commonBuckets_of_sharesLeg
      seed left right leftBucket rightBucket hleftCommon hrightCommon
        (hshare left hleftMem right hrightMem hcompatible)

/-! ## Tiny genuinely marked client -/

/-- One marked target can be isolated against a strictly larger two-target ambient family.  This
guards the marked/ambient asymmetry against a vacuous or accidentally unmarked formulation. -/
example (target : R) (hcard : 4 ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin 1),
    (ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
      (tinyAmbient target) (tinyMarked target) {0}
      LegalTriple.xIndex LegalTriple.yIndex SharesXY collisionProxy seed).Nonempty := by
  classical
  have hshare : ∀ left ∈ tinyMarked target,
      ∀ right ∈ tinyAmbient target,
        SharesXY left right → SharesLeg left right := by
    intro left _hleft right _hright hxy
    rcases hxy with hx | hy
    · exact ⟨.X, hx⟩
    · exact ⟨.Y, hy⟩
  have hquarter : ∀ left ∈ tinyMarked target,
      4 * (ProgressionHash.Seed.compatibilityAlternativeIndices
        (tinyAmbient target) SharesXY collisionProxy left).card ≤ Fintype.card R := by
    intro left hleft
    rw [tinyMarked, Finset.mem_singleton] at hleft
    subst left
    rw [compatibilityAlternativeIndices_sharesXY_eq_xyCompetitorYIndices]
    have hcompetitors := card_tinyCompetitors_le (R := R) target
    omega
  obtain ⟨seed, hcount, _hfiltered, _hisolated⟩ :=
    exists_seed_many_markedCompatibilityHashIsolatedLegalTargets
      (tinyAmbient target) (tinyMarked target)
      (tinyMarked_subset_tinyAmbient target) {0} SharesXY hshare hquarter
  refine ⟨seed, Finset.card_pos.mp ?_⟩
  by_contra hzero
  have hcardZero :
      (ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
        (tinyAmbient target) (tinyMarked target) {0}
        LegalTriple.xIndex LegalTriple.yIndex SharesXY collisionProxy seed).card = 0 :=
    Nat.eq_zero_of_not_pos hzero
  rw [hcardZero, tinyMarked, Finset.card_singleton, Finset.card_singleton,
    Nat.mul_zero] at hcount
  omega

end ProgressionHash.LegalTriple

end AlgebraicComplexity
