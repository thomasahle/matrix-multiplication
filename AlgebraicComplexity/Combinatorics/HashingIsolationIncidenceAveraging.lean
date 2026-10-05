/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HashingIsolation

/-!
# Aggregate isolated-target reward before choosing a seed

`HashingIsolation.exists_seed_many_isolatedIncidences` chooses a seed maximizing the number of
isolated target/bucket incidences.  Sparse compatibility repair must choose a seed and a recursive
type simultaneously while charging the holes in that same cell.  For that application one needs
the stronger inequality *before* taking the maximum: the sum of the isolated rewards over every
affine seed.

This file exposes that exact double count and then partitions each seed's reward by an arbitrary
finite type tag.  It contains no tensor, entropy, compatibility predicate, repair hypothesis, or
certificate constant.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

namespace ProgressionHash.Seed

variable {R : Type u} [Field R] [Fintype R]
variable {ι : Type v} [Fintype ι]
variable {τ : Type w}

/-- Exact pre-maximization survival inequality.  The left side is the sum of the paper's
`3/4` lower bound over every target/bucket pair; the right side is four times the total isolated
incidence reward over all affine seeds. -/
theorem three_mul_total_commonBucketBase_le_four_mul_sum_isolatedIncidences
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (hdistinct : ∀ t ∈ targets, ∀ J' ∈ alternatives t, J' ≠ yIndex t)
    (hquarter : ∀ t ∈ targets,
      4 * (alternatives t).card ≤ Fintype.card R) :
    targets.card * buckets.card *
        (3 * (Fintype.card R ^ Fintype.card ι)) ≤
      4 * ∑ seed : ProgressionHash.Seed R ι,
        (isolatedIncidences targets buckets xIndex yIndex alternatives seed).card := by
  classical
  let pairs := targets.product buckets
  let seeds : Finset (ProgressionHash.Seed R ι) := Finset.univ
  let relation : (τ × R) → ProgressionHash.Seed R ι → Prop := fun pair seed ↦
    seed ∈ isolatedSeeds (xIndex pair.1) (yIndex pair.1)
      (alternatives pair.1) pair.2
  have habove (pair : τ × R) :
      (seeds.bipartiteAbove relation pair).card =
        (isolatedSeeds (xIndex pair.1) (yIndex pair.1)
          (alternatives pair.1) pair.2).ncard := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext seed
    simp [seeds, relation, Finset.bipartiteAbove]
  have hpair (pair : τ × R) (hpairMem : pair ∈ pairs) :
      3 * (Fintype.card R ^ Fintype.card ι) ≤
        4 * (seeds.bipartiteAbove relation pair).card := by
    obtain ⟨t, b⟩ := pair
    have hmem : t ∈ targets ∧ b ∈ buckets := by
      simpa [pairs] using hpairMem
    have hisolated :=
      three_mul_ncard_commonBucketSeeds_le_four_mul_ncard_isolatedSeeds
        (xIndex t) (yIndex t) (alternatives t) b
        (hdistinct t hmem.1) (hquarter t hmem.1)
    rw [ncard_commonBucketSeeds] at hisolated
    simpa [habove] using hisolated
  have hdouble :
      (∑ pair ∈ pairs, (seeds.bipartiteAbove relation pair).card) =
        ∑ seed ∈ seeds, (pairs.bipartiteBelow relation seed).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow relation
  calc
    targets.card * buckets.card *
          (3 * (Fintype.card R ^ Fintype.card ι)) =
        ∑ pair ∈ pairs, 3 * (Fintype.card R ^ Fintype.card ι) := by
      simp [pairs]
    _ ≤ ∑ pair ∈ pairs,
        4 * (seeds.bipartiteAbove relation pair).card :=
      Finset.sum_le_sum fun pair hpairMem ↦ hpair pair hpairMem
    _ = 4 * ∑ pair ∈ pairs,
        (seeds.bipartiteAbove relation pair).card := by
      rw [Finset.mul_sum]
    _ = 4 * ∑ seed ∈ seeds,
        (pairs.bipartiteBelow relation seed).card := by
      rw [hdouble]
    _ = 4 * ∑ seed : ProgressionHash.Seed R ι,
        (isolatedIncidences
          targets buckets xIndex yIndex alternatives seed).card := by
      simpa only [seeds, pairs, relation, isolatedIncidences,
        Finset.bipartiteBelow]

/-- Seed-cardinality form of the aggregate reward inequality.  It makes the averaging measure
explicit and is often the convenient input after all finite denominators have been cleared. -/
theorem three_mul_targets_mul_buckets_mul_seeds_le_four_mul_square_mul_sum_isolatedIncidences
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (hdistinct : ∀ t ∈ targets, ∀ J' ∈ alternatives t, J' ≠ yIndex t)
    (hquarter : ∀ t ∈ targets,
      4 * (alternatives t).card ≤ Fintype.card R) :
    3 * targets.card * buckets.card *
        Fintype.card (ProgressionHash.Seed R ι) ≤
      4 * (Fintype.card R * Fintype.card R) *
        ∑ seed : ProgressionHash.Seed R ι,
          (isolatedIncidences
            targets buckets xIndex yIndex alternatives seed).card := by
  have hbase :=
    three_mul_total_commonBucketBase_le_four_mul_sum_isolatedIncidences
      targets buckets xIndex yIndex alternatives hdistinct hquarter
  have hscaled := Nat.mul_le_mul_left
    (Fintype.card R * Fintype.card R) hbase
  have hseedCard :
      Fintype.card (ProgressionHash.Seed R ι) =
        Fintype.card R *
          (Fintype.card R * (Fintype.card R ^ Fintype.card ι)) := by
    simpa using (card_seed (R := R) (ι := ι))
  rw [hseedCard]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled

/-! ## Partition the reward by a recursive type tag -/

/-- Isolated target/bucket incidences of one seed carrying one specified target type tag. -/
noncomputable def isolatedIncidenceTypeReward
    {TypeTag : Type*} [DecidableEq TypeTag]
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (tag : τ → TypeTag)
    (seed : ProgressionHash.Seed R ι) (type : TypeTag) : ℕ := by
  classical
  exact ((isolatedIncidences
    targets buckets xIndex yIndex alternatives seed).filter
      fun pair ↦ tag pair.1 = type).card

/-- For one seed, summing the tagged rewards over the image of the target family recovers the
entire isolated incidence reward exactly. -/
theorem sum_isolatedIncidenceTypeReward_eq
    {TypeTag : Type*} [DecidableEq TypeTag]
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (tag : τ → TypeTag) (seed : ProgressionHash.Seed R ι) :
    ∑ type ∈ targets.image tag,
        isolatedIncidenceTypeReward
          targets buckets xIndex yIndex alternatives tag seed type =
      (isolatedIncidences
        targets buckets xIndex yIndex alternatives seed).card := by
  classical
  let incidences := isolatedIncidences
    targets buckets xIndex yIndex alternatives seed
  have hmaps : (incidences : Set (τ × R)).MapsTo
      (fun pair ↦ tag pair.1) (targets.image tag) := by
    intro pair hpair
    apply Finset.mem_image.mpr
    refine ⟨pair.1, ?_, rfl⟩
    unfold incidences isolatedIncidences at hpair
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).1
  simpa [incidences, isolatedIncidenceTypeReward] using
    (Finset.card_eq_sum_card_fiberwise hmaps).symm

/-- The seed/type partition preserves the aggregate isolated reward exactly. -/
theorem sum_seed_sum_isolatedIncidenceTypeReward_eq
    {TypeTag : Type*} [DecidableEq TypeTag]
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (tag : τ → TypeTag) :
    (∑ seed : ProgressionHash.Seed R ι,
        ∑ type ∈ targets.image tag,
          isolatedIncidenceTypeReward
            targets buckets xIndex yIndex alternatives tag seed type) =
      ∑ seed : ProgressionHash.Seed R ι,
        (isolatedIncidences
          targets buckets xIndex yIndex alternatives seed).card := by
  apply Finset.sum_congr rfl
  intro seed _hseed
  exact sum_isolatedIncidenceTypeReward_eq
    targets buckets xIndex yIndex alternatives tag seed

end ProgressionHash.Seed

end AlgebraicComplexity
