import AlgebraicComplexity.Combinatorics.HashingIsolation
import AlgebraicComplexity.Tensor.CompatibilityZeroing

/-!
# Compatibility isolation by affine hashing

Compatibility cleanup is often preceded by an affine hash filter. For one target `t`, every
distinct compatible target contributes a collision index. If none of those indices hashes to
the bucket containing `t`, then `t` is uniquely compatible inside the hash-filtered family.

This file packages that argument independently of Coppersmith--Winograd tensors. The finite
good-seed theorem is inherited verbatim from `HashingIsolation`; the only new work is constructing
the exact alternative-index family and proving that its isolated targets lie in the semantic
compatibility-isolated support. A final bridge identifies the generic support with the tensor
library's `compatibilityIsolatedSupport`.
-/

namespace AlgebraicComplexity

universe u v w

namespace ProgressionHash.Seed

variable {R : Type u} [Field R] [Fintype R]
variable {ι : Type v} [Fintype ι]
variable {τ : Type w}

/-- Distinct targets compatible with `t`, before applying the collision-index map. -/
noncomputable def compatibilityAlternativeTargets
    (targets : Finset τ) (compatible : τ → τ → Prop) (t : τ) : Finset τ := by
  classical
  exact (targets.erase t).filter (compatible t)

/-- Collision indices of all distinct targets compatible with `t`.  The proxy may depend on
both the intended target and its competitor, as in the standard affine transport
`LegalTriple.collisionProxy t u`. -/
noncomputable def compatibilityAlternativeIndices
    (targets : Finset τ) (compatible : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R) (t : τ) : Finset (ι → R) := by
  classical
  exact (compatibilityAlternativeTargets targets compatible t).image (collisionIndex t)

omit [Field R] [Fintype R] in
@[simp] theorem mem_compatibilityAlternativeIndices
    (targets : Finset τ) (compatible : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R) (t : τ) (J : ι → R) :
    J ∈ compatibilityAlternativeIndices targets compatible collisionIndex t ↔
      ∃ u ∈ targets, u ≠ t ∧ compatible t u ∧ collisionIndex t u = J := by
  classical
  simp only [compatibilityAlternativeIndices, compatibilityAlternativeTargets,
    Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨u, ⟨⟨hut, hu⟩, hcompatible⟩, rfl⟩
    exact ⟨u, hu, hut, hcompatible, rfl⟩
  · rintro ⟨u, hu, hut, hcompatible, rfl⟩
    exact ⟨u, ⟨⟨hut, hu⟩, hcompatible⟩, rfl⟩

omit [Field R] [Fintype R] in
/-- Taking collision indices cannot increase the number of compatible alternatives. -/
theorem card_compatibilityAlternativeIndices_le
    (targets : Finset τ) (compatible : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R) (t : τ) :
    (compatibilityAlternativeIndices targets compatible collisionIndex t).card ≤
      (compatibilityAlternativeTargets targets compatible t).card := by
  classical
  exact Finset.card_image_le

/-- Targets surviving the two common-bucket hash equations, before collision isolation. -/
noncomputable def commonBucketFilteredTargets
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R) (seed : ProgressionHash.Seed R ι) : Finset τ := by
  classical
  exact targets.filter fun t ↦
    ∃ b ∈ buckets, InCommonBucket (xIndex t) (yIndex t) b seed

omit [Fintype R] in
@[simp] theorem mem_commonBucketFilteredTargets
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R) (seed : ProgressionHash.Seed R ι) (t : τ) :
    t ∈ commonBucketFilteredTargets targets buckets xIndex yIndex seed ↔
      t ∈ targets ∧
        ∃ b ∈ buckets, InCommonBucket (xIndex t) (yIndex t) b seed := by
  classical
  simp [commonBucketFilteredTargets]

/-- Targets uniquely compatible inside an arbitrary finite ambient family. -/
noncomputable def compatibilityIsolatedTargets
    (ambient : Finset τ) (compatible : τ → τ → Prop) : Finset τ := by
  classical
  exact ambient.filter fun t ↦
    ∀ u ∈ ambient, compatible t u → u = t

@[simp] theorem mem_compatibilityIsolatedTargets
    (ambient : Finset τ) (compatible : τ → τ → Prop) (t : τ) :
    t ∈ compatibilityIsolatedTargets ambient compatible ↔
      t ∈ ambient ∧ ∀ u ∈ ambient, compatible t u → u = t := by
  classical
  simp [compatibilityIsolatedTargets]

/-- The affine-hash selection obtained by forbidding all compatible collision indices. -/
noncomputable def compatibilityHashIsolatedTargets
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R) (compatible : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R)
    (seed : ProgressionHash.Seed R ι) : Finset τ :=
  isolatedTargets targets buckets xIndex yIndex
    (compatibilityAlternativeIndices targets compatible collisionIndex) seed

omit [Fintype R] in
/-- Hash-isolated targets survive the underlying common-bucket filter. -/
theorem compatibilityHashIsolatedTargets_subset_commonBucketFilteredTargets
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R) (compatible : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R)
    (seed : ProgressionHash.Seed R ι) :
    compatibilityHashIsolatedTargets targets buckets xIndex yIndex
        compatible collisionIndex seed ⊆
      commonBucketFilteredTargets targets buckets xIndex yIndex seed := by
  classical
  intro t ht
  have himage : t ∈ isolatedTargets targets buckets xIndex yIndex
      (compatibilityAlternativeIndices targets compatible collisionIndex) seed := by
    simpa only [compatibilityHashIsolatedTargets] using ht
  obtain ⟨⟨t', b⟩, hincidence, hfst⟩ := Finset.mem_image.mp himage
  simp only at hfst
  subst t'
  have hfilter := Finset.mem_filter.mp hincidence
  have hpair := Finset.mem_product.mp hfilter.1
  exact mem_commonBucketFilteredTargets targets buckets xIndex yIndex seed t |>.2
    ⟨hpair.1, b, hpair.2, hfilter.2.1⟩

omit [Fintype R] in
/-- If every compatible survivor's collision index hashes to the target bucket, affine isolation
implies semantic unique compatibility inside the hash-filtered target family. -/
theorem compatibilityHashIsolatedTargets_subset_compatibilityIsolatedTargets
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R) (compatible : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R)
    (seed : ProgressionHash.Seed R ι)
    (hcollision : ∀ t u b c,
      t ∈ targets → u ∈ targets →
      InCommonBucket (xIndex t) (yIndex t) b seed →
      InCommonBucket (xIndex u) (yIndex u) c seed →
      compatible t u → seed.yHash (collisionIndex t u) = b) :
    compatibilityHashIsolatedTargets targets buckets xIndex yIndex
        compatible collisionIndex seed ⊆
      compatibilityIsolatedTargets
        (commonBucketFilteredTargets targets buckets xIndex yIndex seed) compatible := by
  classical
  intro t ht
  have himage : t ∈ isolatedTargets targets buckets xIndex yIndex
      (compatibilityAlternativeIndices targets compatible collisionIndex) seed := by
    simpa only [compatibilityHashIsolatedTargets] using ht
  obtain ⟨⟨t', b⟩, hincidence, hfst⟩ := Finset.mem_image.mp himage
  simp only at hfst
  subst t'
  have hfilter := Finset.mem_filter.mp hincidence
  have hpair := Finset.mem_product.mp hfilter.1
  have htTarget : t ∈ targets := hpair.1
  have htCommon : InCommonBucket (xIndex t) (yIndex t) b seed := hfilter.2.1
  apply (mem_compatibilityIsolatedTargets _ _ _).mpr
  refine ⟨(mem_commonBucketFilteredTargets targets buckets xIndex yIndex seed t).mpr
    ⟨htTarget, b, hpair.2, htCommon⟩, ?_⟩
  intro u hu hcompatible
  have huData :=
    (mem_commonBucketFilteredTargets targets buckets xIndex yIndex seed u).mp hu
  obtain ⟨huTarget, c, _hcBucket, huCommon⟩ := huData
  by_contra hne
  have hindexMem : collisionIndex t u ∈
      compatibilityAlternativeIndices targets compatible collisionIndex t :=
    (mem_compatibilityAlternativeIndices _ _ _ _ _).mpr
      ⟨u, huTarget, hne, hcompatible, rfl⟩
  have hnot := hfilter.2.2 _ hindexMem
  exact hnot (hcollision t u b c htTarget huTarget htCommon huCommon hcompatible)

/-- Complete good-seed adapter for compatibility isolation. The exact `3/4` finite count is
unchanged; the selected family lies in the semantic unique-compatibility support of the filtered
family. -/
theorem exists_seed_many_compatibilityHashIsolatedTargets
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R) (compatible : τ → τ → Prop)
    (collisionIndex : τ → τ → ι → R)
    (hdistinct : ∀ t ∈ targets, ∀ u ∈ targets,
      u ≠ t → compatible t u → collisionIndex t u ≠ yIndex t)
    (hquarter : ∀ t ∈ targets,
      4 * (compatibilityAlternativeIndices targets compatible collisionIndex t).card ≤
        Fintype.card R)
    (hcollision : ∀ seed : ProgressionHash.Seed R ι, ∀ t u b c,
      t ∈ targets → u ∈ targets →
      InCommonBucket (xIndex t) (yIndex t) b seed →
      InCommonBucket (xIndex u) (yIndex u) c seed →
      compatible t u → seed.yHash (collisionIndex t u) = b) :
    ∃ seed : ProgressionHash.Seed R ι,
      3 * targets.card * buckets.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (compatibilityHashIsolatedTargets targets buckets xIndex yIndex
              compatible collisionIndex seed).card ∧
        compatibilityHashIsolatedTargets targets buckets xIndex yIndex
            compatible collisionIndex seed ⊆
          commonBucketFilteredTargets targets buckets xIndex yIndex seed ∧
        compatibilityHashIsolatedTargets targets buckets xIndex yIndex
            compatible collisionIndex seed ⊆
          compatibilityIsolatedTargets
            (commonBucketFilteredTargets targets buckets xIndex yIndex seed) compatible := by
  classical
  have hindicesDistinct : ∀ t ∈ targets,
      ∀ J ∈ compatibilityAlternativeIndices targets compatible collisionIndex t,
        J ≠ yIndex t := by
    intro t ht J hJ
    obtain ⟨u, hu, hut, hcompatible, rfl⟩ :=
      (mem_compatibilityAlternativeIndices _ _ _ _ _).mp hJ
    exact hdistinct t ht u hu hut hcompatible
  obtain ⟨seed, hcount⟩ := exists_seed_many_isolatedTargets
    targets buckets xIndex yIndex
      (compatibilityAlternativeIndices targets compatible collisionIndex)
      hindicesDistinct hquarter
  refine ⟨seed, ?_,
    compatibilityHashIsolatedTargets_subset_commonBucketFilteredTargets
      targets buckets xIndex yIndex compatible collisionIndex seed,
    compatibilityHashIsolatedTargets_subset_compatibilityIsolatedTargets
      targets buckets xIndex yIndex compatible collisionIndex seed
        (hcollision seed)⟩
  simpa only [compatibilityHashIsolatedTargets] using hcount

omit [Fintype R] in
/-- Self-compatibility on the original target family is inherited by every common-bucket
filtered subfamily. -/
theorem commonBucketFilteredTargets_selfCompatible
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R) (compatible : τ → τ → Prop)
    (seed : ProgressionHash.Seed R ι)
    (hself : ∀ t ∈ targets, compatible t t) :
    ∀ t ∈ commonBucketFilteredTargets targets buckets xIndex yIndex seed,
      compatible t t := by
  intro t ht
  exact hself t
    ((mem_commonBucketFilteredTargets targets buckets xIndex yIndex seed t).mp ht).1

end ProgressionHash.Seed

/-! ## Tensor compatibility-support bridge -/

namespace Tensor

variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Binary relation on addresses induced by one pivot-label compatibility predicate. -/
def pivotCompatibilityRelation (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) :
    BlockAddress A → BlockAddress A → Prop :=
  fun address other ↦ compatible (address pivot) other

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The generic finite compatibility-isolation set is exactly the tensor cleanup support. -/
theorem compatibilityIsolatedTargets_pivot_eq_compatibilityIsolatedSupport
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) :
    ProgressionHash.Seed.compatibilityIsolatedTargets ambient
        (pivotCompatibilityRelation pivot compatible) =
      compatibilityIsolatedSupport ambient pivot compatible := by
  classical
  ext address
  simp [ProgressionHash.Seed.mem_compatibilityIsolatedTargets,
    mem_compatibilityIsolatedSupport, IsUniquelyCompatible, pivotCompatibilityRelation]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Generic self-compatibility is precisely the tensor cleanup's soundness hypothesis. -/
theorem isCompatibilitySound_of_selfCompatible
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hself : ∀ address ∈ ambient,
      pivotCompatibilityRelation pivot compatible address address) :
    IsCompatibilitySound ambient pivot compatible := by
  exact hself

end Tensor

end AlgebraicComplexity
