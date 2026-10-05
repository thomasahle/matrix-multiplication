/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ChargedFiniteAveraging
import AlgebraicComplexity.Combinatorics.HashingIsolationIncidenceAveraging
import AlgebraicComplexity.Combinatorics.HashingSeedHoleMass
import AlgebraicComplexity.Combinatorics.MarkedXHashingExtraction

set_option autoImplicit false

/-!
# Joint affine-seed selection with arbitrary shared-leg hole charges

This file separates the finite hashing argument used in Claim 6.18 of [alman2025more] from the
paper-specific compatibility count.  A fine block may have competitors sharing either the `Y` or
the `Z` leg of its owner.  The shared leg may even depend on the owner, fine block, and competitor.
The exact affine collision law is unchanged: two distinct legal triples which share any one leg
land in one prescribed bucket for exactly a `|R|⁻³` fraction of all seeds.

The isolated-target family and its alternative indices are parameters.  The main theorem chooses
one seed which simultaneously

* retains at least a prescribed number of isolated targets; and
* makes the total fine-hole mass at most a `1 / D` fraction of the available fine blocks.

All statements are division-free.  The variable damage scale `D` appears in the field-size
premise `8 * D * V ≤ 3 * |R|`, where `V` bounds the number of compatible competitors of one fine
block.  Taking `D = Θ(n²)` is the finite form of the `O(1/n²)` hole fraction in Claim 6.18.

The final theorem specializes the abstract isolation family to marked X-only hashing.  It asserts
only filtered survival and X-injectivity; Y/Z uniqueness is deliberately left to compatibility
cleanup and hole repair.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*, Claim 6.18;
  `papers/sources/2404.16349/constituent.tex:177-479`.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
variable {ι : Type v} [Fintype ι]
variable {target : R}
variable {A : Type w}

/-- Total fine-hole mass over the target/bucket incidences isolated by one affine seed.

The definition does not choose a shared leg.  That semantic fact is a hypothesis of the subsequent
counting theorem, so a multiplicity-weighted tagged alphabet can combine several cleanup
directions in one average. -/
noncomputable def seedSharedLegHoleMass
    [Fintype A]
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (alternatives : LegalTriple R ι target → Finset (ι → R))
    (seed : Seed R ι) : ℕ := by
  classical
  exact ∑ pair ∈ Seed.isolatedIncidences marked buckets
      LegalTriple.xIndex LegalTriple.yIndex alternatives seed,
    (seedSharedHoles ambient compat seed pair.1 pair.2).card

/-- The exact seed-summed collision count for one owner, bucket, and fine block when every
competitor shares a specified (possibly competitor-dependent) leg with the owner.

This is the arbitrary-leg form of `sum_card_bucketWitnesses_mul_cube`. -/
theorem sum_card_bucketWitnesses_mul_cube_of_sharedLeg
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (owner : LegalTriple R ι target) (bucket : R) (fine : A)
    (sharedLeg : LegalTriple R ι target → Tensor.Leg)
    (hshared : ∀ competitor ∈ fineCompetitors ambient compat owner fine,
      competitor.legIndex (sharedLeg competitor) =
        owner.legIndex (sharedLeg competitor)) :
    (∑ seed : Seed R ι,
        (bucketWitnesses ambient compat seed owner bucket fine).card) *
        (Fintype.card R * Fintype.card R * Fintype.card R) =
      (fineCompetitors ambient compat owner fine).card *
        Fintype.card (Seed R ι) := by
  classical
  have hswap :
      (∑ seed : Seed R ι,
          (bucketWitnesses ambient compat seed owner bucket fine).card) =
        ∑ competitor ∈ fineCompetitors ambient compat owner fine,
          (Finset.univ.filter fun seed : Seed R ι ↦
            Seed.InCommonTriple owner.xIndex owner.yIndex owner.zIndex
                target bucket seed ∧
              Seed.InCommonTriple competitor.xIndex competitor.yIndex competitor.zIndex
                target bucket seed).card := by
    have hleft : ∀ seed : Seed R ι,
        (bucketWitnesses ambient compat seed owner bucket fine).card =
          ∑ competitor ∈ fineCompetitors ambient compat owner fine,
            (if Seed.InCommonTriple owner.xIndex owner.yIndex owner.zIndex
                  target bucket seed ∧
                Seed.InCommonTriple competitor.xIndex competitor.yIndex competitor.zIndex
                  target bucket seed then 1 else 0) := by
      intro seed
      rw [bucketWitnesses, Finset.card_filter]
    have hright : ∀ competitor : LegalTriple R ι target,
        (Finset.univ.filter fun seed : Seed R ι ↦
            Seed.InCommonTriple owner.xIndex owner.yIndex owner.zIndex
                target bucket seed ∧
              Seed.InCommonTriple competitor.xIndex competitor.yIndex competitor.zIndex
                target bucket seed).card =
          ∑ seed : Seed R ι,
            (if Seed.InCommonTriple owner.xIndex owner.yIndex owner.zIndex
                  target bucket seed ∧
                Seed.InCommonTriple competitor.xIndex competitor.yIndex competitor.zIndex
                  target bucket seed then 1 else 0) := by
      intro competitor
      rw [Finset.card_filter]
    simp only [hleft, hright]
    exact Finset.sum_comm
  rw [hswap, Finset.sum_mul]
  have hterm : ∀ competitor ∈ fineCompetitors ambient compat owner fine,
      (Finset.univ.filter fun seed : Seed R ι ↦
          Seed.InCommonTriple owner.xIndex owner.yIndex owner.zIndex target bucket seed ∧
            Seed.InCommonTriple competitor.xIndex competitor.yIndex competitor.zIndex
              target bucket seed).card *
        (Fintype.card R * Fintype.card R * Fintype.card R) =
      Fintype.card (Seed R ι) := by
    intro competitor hcompetitor
    have hne : competitor ≠ owner :=
      (mem_fineCompetitors.mp hcompetitor).1.1
    have hbridge :
        (Finset.univ.filter fun seed : Seed R ι ↦
            Seed.InCommonTriple owner.xIndex owner.yIndex owner.zIndex
                target bucket seed ∧
              Seed.InCommonTriple competitor.xIndex competitor.yIndex competitor.zIndex
                target bucket seed).card =
          Nat.card {seed : Seed R ι //
            Seed.InCommonTriple owner.xIndex owner.yIndex owner.zIndex
                target bucket seed ∧
              Seed.InCommonTriple competitor.xIndex competitor.yIndex competitor.zIndex
                target bucket seed} := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hbridge]
    exact card_inCommonTriple_pair_mul_cube hne (hshared competitor hcompetitor) bucket
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]

/-- Seed-summed fine-hole mass for arbitrary shared-leg competitors.

`V` is a pointwise bound on the compatible competitors of one owner/fine-block pair.  The proof
first bounds each union of holes by its witness incidences, then applies the exact arbitrary-leg
pair-collision identity and sums over owners, buckets, and fine blocks. -/
theorem sum_seedSharedLegHoleMass_mul_cube_le
    [Fintype A]
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (alternatives : LegalTriple R ι target → Finset (ι → R))
    (sharedLeg : LegalTriple R ι target → A →
      LegalTriple R ι target → Tensor.Leg)
    (V : ℕ)
    (hshared : ∀ owner ∈ marked, ∀ fine : A,
      ∀ competitor ∈ fineCompetitors ambient compat owner fine,
        competitor.legIndex (sharedLeg owner fine competitor) =
          owner.legIndex (sharedLeg owner fine competitor))
    (hcompetitors : ∀ owner ∈ marked, ∀ fine : A,
      (fineCompetitors ambient compat owner fine).card ≤ V) :
    (∑ seed : Seed R ι,
        seedSharedLegHoleMass ambient marked buckets compat alternatives seed) *
        (Fintype.card R * Fintype.card R * Fintype.card R) ≤
      marked.card * buckets.card * Fintype.card A * V *
        Fintype.card (Seed R ι) := by
  classical
  have hseed : ∀ seed : Seed R ι,
      seedSharedLegHoleMass ambient marked buckets compat alternatives seed ≤
        ∑ pair ∈ marked.product buckets,
          ∑ fine : A,
            (bucketWitnesses ambient compat seed pair.1 pair.2 fine).card := by
    intro seed
    have hsub : Seed.isolatedIncidences marked buckets
        LegalTriple.xIndex LegalTriple.yIndex alternatives seed ⊆
      marked.product buckets := by
      rw [Seed.isolatedIncidences]
      exact Finset.filter_subset _ _
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
    · intro pair hpair
      have hevent := (Finset.mem_filter.mp hpair).2
      have hbucket : Seed.InCommonBucket pair.1.xIndex pair.1.yIndex pair.2 seed :=
        hevent.1
      exact card_seedSharedHoles_le ambient compat seed pair.1 pair.2
        ((Seed.inCommonTriple_iff_commonBucket seed
          pair.1.xIndex pair.1.yIndex pair.1.zIndex target pair.2 pair.1.legal).mpr hbucket)
    · intro pair _ _
      exact Nat.zero_le _
  have hsum :
      (∑ seed : Seed R ι,
          seedSharedLegHoleMass ambient marked buckets compat alternatives seed) ≤
        ∑ pair ∈ marked.product buckets,
          ∑ fine : A,
            ∑ seed : Seed R ι,
              (bucketWitnesses ambient compat seed pair.1 pair.2 fine).card := by
    calc
      (∑ seed : Seed R ι,
          seedSharedLegHoleMass ambient marked buckets compat alternatives seed) ≤
          ∑ seed : Seed R ι, ∑ pair ∈ marked.product buckets,
            ∑ fine : A,
              (bucketWitnesses ambient compat seed pair.1 pair.2 fine).card :=
        Finset.sum_le_sum fun seed _ ↦ hseed seed
      _ = ∑ pair ∈ marked.product buckets, ∑ seed : Seed R ι,
            ∑ fine : A,
              (bucketWitnesses ambient compat seed pair.1 pair.2 fine).card :=
        Finset.sum_comm
      _ = ∑ pair ∈ marked.product buckets, ∑ fine : A,
            ∑ seed : Seed R ι,
              (bucketWitnesses ambient compat seed pair.1 pair.2 fine).card :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  calc
    (∑ seed : Seed R ι,
        seedSharedLegHoleMass ambient marked buckets compat alternatives seed) *
          (Fintype.card R * Fintype.card R * Fintype.card R) ≤
        (∑ pair ∈ marked.product buckets, ∑ fine : A,
          ∑ seed : Seed R ι,
            (bucketWitnesses ambient compat seed pair.1 pair.2 fine).card) *
              (Fintype.card R * Fintype.card R * Fintype.card R) :=
      Nat.mul_le_mul hsum (le_refl _)
    _ = ∑ pair ∈ marked.product buckets, ∑ fine : A,
          ((∑ seed : Seed R ι,
              (bucketWitnesses ambient compat seed pair.1 pair.2 fine).card) *
            (Fintype.card R * Fintype.card R * Fintype.card R)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_mul _ _ _
    _ = ∑ pair ∈ marked.product buckets, ∑ fine : A,
          (fineCompetitors ambient compat pair.1 fine).card *
            Fintype.card (Seed R ι) := by
      refine Finset.sum_congr rfl fun pair hpair ↦
        Finset.sum_congr rfl fun fine _ ↦ ?_
      have howner := (Finset.mem_product.mp hpair).1
      exact sum_card_bucketWitnesses_mul_cube_of_sharedLeg
        ambient compat pair.1 pair.2 fine (sharedLeg pair.1 fine)
          (hshared pair.1 howner fine)
    _ ≤ ∑ _pair ∈ marked.product buckets, ∑ _fine : A,
          V * Fintype.card (Seed R ι) := by
      refine Finset.sum_le_sum fun pair hpair ↦ Finset.sum_le_sum fun fine _ ↦ ?_
      have howner := (Finset.mem_product.mp hpair).1
      exact Nat.mul_le_mul (hcompetitors pair.1 howner fine) (le_refl _)
    _ = marked.card * buckets.card * Fintype.card A * V *
          Fintype.card (Seed R ι) := by
      simp [Finset.sum_const, Finset.card_product, mul_comm, mul_assoc, mul_left_comm]

/-- Division-free arithmetic for a variable hole-repair scale.

The first two hypotheses are the seed-summed hole and isolation estimates.  The modulus premise
allocates half of the isolation reward to a `D`-fold hole charge; the count premise allocates the
other half to the requested retained-count floor. -/
theorem scaledHoleMass_averaging_arith
    {P Q seedCount targetCount bucketCount fineCount V count q D : ℕ}
    (hq : 0 < q)
    (hholes : P * (q * q * q) ≤
      targetCount * bucketCount * fineCount * V * seedCount)
    (hisolation : 3 * targetCount * bucketCount * seedCount ≤
      4 * (q * q) * Q)
    (hmodulus : 8 * D * V ≤ 3 * q)
    (hcount : 8 * (q * q) * count ≤ 3 * (targetCount * bucketCount)) :
    D * P + seedCount * (fineCount * count) ≤ fineCount * Q := by
  have hq2 : 0 < q * q := Nat.mul_pos hq hq
  have hq3 : 0 < q * q * q := Nat.mul_pos hq2 hq
  have hdamageScaled :
      (8 * (D * P)) * (q * q * q) ≤
        (4 * (fineCount * Q)) * (q * q * q) := by
    calc
      (8 * (D * P)) * (q * q * q) =
          (8 * D) * (P * (q * q * q)) := by ring
      _ ≤ (8 * D) *
          (targetCount * bucketCount * fineCount * V * seedCount) :=
        Nat.mul_le_mul (le_refl _) hholes
      _ = (8 * D * V) *
          (targetCount * bucketCount * fineCount * seedCount) := by ring
      _ ≤ (3 * q) *
          (targetCount * bucketCount * fineCount * seedCount) :=
        Nat.mul_le_mul hmodulus (le_refl _)
      _ = (q * fineCount) *
          (3 * targetCount * bucketCount * seedCount) := by ring
      _ ≤ (q * fineCount) * (4 * (q * q) * Q) :=
        Nat.mul_le_mul (le_refl _) hisolation
      _ = (4 * (fineCount * Q)) * (q * q * q) := by ring
  have hdamage : 8 * (D * P) ≤ 4 * (fineCount * Q) :=
    Nat.le_of_mul_le_mul_right hdamageScaled hq3
  have hfloorScaled :
      (8 * (seedCount * (fineCount * count))) * (q * q) ≤
        (4 * (fineCount * Q)) * (q * q) := by
    calc
      (8 * (seedCount * (fineCount * count))) * (q * q) =
          (8 * (q * q) * count) * (fineCount * seedCount) := by ring
      _ ≤ (3 * (targetCount * bucketCount)) * (fineCount * seedCount) :=
        Nat.mul_le_mul hcount (le_refl _)
      _ = fineCount * (3 * targetCount * bucketCount * seedCount) := by ring
      _ ≤ fineCount * (4 * (q * q) * Q) :=
        Nat.mul_le_mul (le_refl _) hisolation
      _ = (4 * (fineCount * Q)) * (q * q) := by ring
  have hfloor : 8 * (seedCount * (fineCount * count)) ≤
      4 * (fineCount * Q) :=
    Nat.le_of_mul_le_mul_right hfloorScaled hq2
  omega

/-- One affine seed simultaneously realizes an isolated-target count and a scaled arbitrary-leg
fine-hole bound.

The alternatives used for isolation remain abstract.  This lets both X-only and stronger hashing
clients reuse the same charged averaging theorem without changing their selected family. -/
theorem exists_seed_isolation_and_sharedLegHoleMass
    [Fintype A]
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (alternatives : LegalTriple R ι target → Finset (ι → R))
    (sharedLeg : LegalTriple R ι target → A →
      LegalTriple R ι target → Tensor.Leg)
    (V count D : ℕ)
    (hdistinct : ∀ owner ∈ marked,
      ∀ alternative ∈ alternatives owner, alternative ≠ owner.yIndex)
    (hquarter : ∀ owner ∈ marked,
      4 * (alternatives owner).card ≤ Fintype.card R)
    (hshared : ∀ owner ∈ marked, ∀ fine : A,
      ∀ competitor ∈ fineCompetitors ambient compat owner fine,
        competitor.legIndex (sharedLeg owner fine competitor) =
          owner.legIndex (sharedLeg owner fine competitor))
    (hcompetitors : ∀ owner ∈ marked, ∀ fine : A,
      (fineCompetitors ambient compat owner fine).card ≤ V)
    (hmodulus : 8 * D * V ≤ 3 * Fintype.card R)
    (hcount : 8 * (Fintype.card R * Fintype.card R) * count ≤
      3 * (marked.card * buckets.card))
    (hA : 0 < Fintype.card A) :
    ∃ seed : Seed R ι,
      count ≤ (Seed.isolatedTargets marked buckets
        LegalTriple.xIndex LegalTriple.yIndex alternatives seed).card ∧
      D * seedSharedLegHoleMass
          ambient marked buckets compat alternatives seed ≤
        Fintype.card A *
          (Seed.isolatedTargets marked buckets
            LegalTriple.xIndex LegalTriple.yIndex alternatives seed).card := by
  classical
  let reward : Seed R ι → ℕ := fun seed ↦
    (Seed.isolatedIncidences marked buckets
      LegalTriple.xIndex LegalTriple.yIndex alternatives seed).card
  let damage : Seed R ι → ℕ := fun seed ↦
    seedSharedLegHoleMass ambient marked buckets compat alternatives seed
  have hisolation :
      3 * marked.card * buckets.card * Fintype.card (Seed R ι) ≤
        4 * (Fintype.card R * Fintype.card R) *
          ∑ seed : Seed R ι, reward seed := by
    simpa only [reward] using
      Seed.three_mul_targets_mul_buckets_mul_seeds_le_four_mul_square_mul_sum_isolatedIncidences
        marked buckets LegalTriple.xIndex LegalTriple.yIndex alternatives
          hdistinct hquarter
  have hholes :
      (∑ seed : Seed R ι, damage seed) *
          (Fintype.card R * Fintype.card R * Fintype.card R) ≤
        marked.card * buckets.card * Fintype.card A * V *
          Fintype.card (Seed R ι) := by
    simpa only [damage] using
      sum_seedSharedLegHoleMass_mul_cube_le
        ambient marked buckets compat alternatives sharedLeg V hshared hcompetitors
  have harith :
      D * (∑ seed : Seed R ι, damage seed) +
          Fintype.card (Seed R ι) * (Fintype.card A * count) ≤
        Fintype.card A * (∑ seed : Seed R ι, reward seed) :=
    scaledHoleMass_averaging_arith (Fintype.card_pos (α := R))
      hholes hisolation hmodulus hcount
  have hglobal :
      (Finset.univ : Finset (Seed R ι)).card * (Fintype.card A * count) +
          ∑ seed ∈ (Finset.univ : Finset (Seed R ι)), D * damage seed ≤
        ∑ seed ∈ (Finset.univ : Finset (Seed R ι)),
          Fintype.card A * reward seed := by
    simpa only [Finset.card_univ, Finset.mul_sum, Nat.add_comm] using harith
  obtain ⟨seed, _hseed, hseed⟩ :=
    exists_mem_floor_add_charge_le_reward
      (Finset.univ : Finset (Seed R ι)) Finset.univ_nonempty
      (fun seed ↦ Fintype.card A * reward seed)
      (fun seed ↦ D * damage seed)
      (Fintype.card A * count) hglobal
  have hcountScaled : Fintype.card A * count ≤ Fintype.card A * reward seed :=
    le_trans (Nat.le_add_right _ _) hseed
  have hcountSeed : count ≤ reward seed :=
    Nat.le_of_mul_le_mul_left hcountScaled hA
  have hdamageSeed : D * damage seed ≤ Fintype.card A * reward seed :=
    le_trans (Nat.le_add_left _ _) hseed
  refine ⟨seed, ?_, ?_⟩
  · rw [Seed.card_isolatedTargets_eq_card_isolatedIncidences]
    exact hcountSeed
  · rw [Seed.card_isolatedTargets_eq_card_isolatedIncidences]
    exact hdamageSeed

/-- Fine-hole mass attached to the marked X-only isolated incidences. -/
noncomputable def markedXSeedSharedLegHoleMass
    [Fintype A]
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) : ℕ :=
  seedSharedLegHoleMass ambient marked buckets compat
    (xCompetitorYIndices ambient) seed

/-- Marked X-only hashing with a simultaneous scaled fine-hole guarantee.

Only X is isolated.  The arbitrary shared-leg premise is intended for a tagged union of the
later logical-Y and logical-Z compatibility witnesses; the theorem itself does not perform that
cleanup. -/
theorem exists_seed_many_markedXIsolatedTargets_and_sharedLegHoleMass
    [Fintype A]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (sharedLeg : LegalTriple R ι target → A →
      LegalTriple R ι target → Tensor.Leg)
    (V count D : ℕ)
    (hquarter : ∀ owner ∈ marked,
      4 * (xCompetitorYIndices ambient owner).card ≤ Fintype.card R)
    (hshared : ∀ owner ∈ marked, ∀ fine : A,
      ∀ competitor ∈ fineCompetitors ambient compat owner fine,
        competitor.legIndex (sharedLeg owner fine competitor) =
          owner.legIndex (sharedLeg owner fine competitor))
    (hcompetitors : ∀ owner ∈ marked, ∀ fine : A,
      (fineCompetitors ambient compat owner fine).card ≤ V)
    (hmodulus : 8 * D * V ≤ 3 * Fintype.card R)
    (hcount : 8 * (Fintype.card R * Fintype.card R) * count ≤
      3 * (marked.card * buckets.card))
    (hA : 0 < Fintype.card A) :
    ∃ seed : Seed R ι,
      count ≤ (markedXIsolatedTargets ambient marked buckets seed).card ∧
      D * markedXSeedSharedLegHoleMass
          ambient marked buckets compat seed ≤
        Fintype.card A *
          (markedXIsolatedTargets ambient marked buckets seed).card ∧
      markedXIsolatedTargets ambient marked buckets seed ⊆
        filteredTargets ambient buckets seed ∧
      Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
        (markedXIsolatedTargets ambient marked buckets seed : Set _) := by
  have hdistinct : ∀ owner ∈ marked,
      ∀ alternative ∈ xCompetitorYIndices ambient owner,
        alternative ≠ owner.yIndex := by
    intro owner _ alternative halternative
    exact yIndex_ne_of_mem_xCompetitorYIndices ambient owner halternative
  obtain ⟨seed, hretained, hholes⟩ :=
    exists_seed_isolation_and_sharedLegHoleMass
      ambient marked buckets compat (xCompetitorYIndices ambient) sharedLeg
      V count D hdistinct hquarter hshared hcompetitors hmodulus hcount hA
  refine ⟨seed, ?_, ?_,
    markedXIsolatedTargets_subset_filteredTargets ambient marked hmarked buckets seed,
    xIndex_injectiveOn_markedXIsolatedTargets ambient marked hmarked buckets seed⟩
  · simpa only [markedXIsolatedTargets] using hretained
  · simpa only [markedXSeedSharedLegHoleMass, markedXIsolatedTargets] using hholes

end ProgressionHash.LegalTriple

end AlgebraicComplexity
