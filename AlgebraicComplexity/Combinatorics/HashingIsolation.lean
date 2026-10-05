/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.Hashing
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Isolation by affine hashing

This file proves the finite union-bound step used after affine hashing in the laser method.  Fix
an `X`-index `I`, its intended `Y`-index `J`, and a prescribed bucket `b`.  If a finite family of
alternative `Y`-indices is distinct from `J`, then each alternative removes exactly one field
degree of freedom from the common-bucket seed fiber.  Consequently the seeds spoiled by any
alternative occupy at most the sum of those collision fibers.

The main statements are deliberately division-free cardinality inequalities.  In particular,
`three_mul_ncard_commonBucketSeeds_le_four_mul_ncard_isolatedSeeds` is the exact finite form of the
published `3/4` conditional-survival claim.  It applies unchanged in the global and recursive
constituent hashing stages of *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace AlgebraicComplexity

universe u v

namespace ProgressionHash.Seed

variable {R : Type u} [Field R] [Fintype R]
variable {ι : Type v} [Fintype ι]

/-- Seeds that put the intended `X`- and `Y`-indices in the prescribed bucket. -/
def commonBucketSeeds (I J : ι → R) (b : R) : Set (ProgressionHash.Seed R ι) :=
  {seed | InCommonBucket I J b seed}

/-- Seeds in the intended common-bucket fiber that also collide with an alternative `Y`-index. -/
def collisionSeeds (I J J' : ι → R) (b : R) : Set (ProgressionHash.Seed R ι) :=
  {seed | InCommonBucket I J b seed ∧ seed.yHash J' = b}

/-- Seeds in the intended common-bucket fiber for which none of the listed alternative
`Y`-indices hits the same bucket. -/
def isolatedSeeds (I J : ι → R) (alternatives : Finset (ι → R)) (b : R) :
    Set (ProgressionHash.Seed R ι) :=
  {seed | InCommonBucket I J b seed ∧
    ∀ J' ∈ alternatives, seed.yHash J' ≠ b}

/-- The intended common-bucket seed fiber has one element for each linear weight table. -/
theorem ncard_commonBucketSeeds (I J : ι → R) (b : R) :
    (commonBucketSeeds I J b).ncard = Fintype.card R ^ Fintype.card ι := by
  rw [← Nat.card_coe_set_eq]
  change Nat.card {seed : ProgressionHash.Seed R ι // InCommonBucket I J b seed} =
    Fintype.card R ^ Fintype.card ι
  exact card_commonBucket I J b

/-- Every intended common-bucket seed is either isolated or belongs to one of the collision
fibers.  This is the set-theoretic union bound before taking cardinalities. -/
theorem commonBucketSeeds_subset_isolatedSeeds_union_iUnion_collisionSeeds
    (I J : ι → R) (alternatives : Finset (ι → R)) (b : R) :
    commonBucketSeeds I J b ⊆
      isolatedSeeds I J alternatives b ∪
        ⋃ J' ∈ alternatives, collisionSeeds I J J' b := by
  classical
  intro seed hseed
  by_cases hisolated : ∀ J' ∈ alternatives, seed.yHash J' ≠ b
  · exact Or.inl ⟨hseed, hisolated⟩
  · simp only [not_forall, ne_eq, not_not] at hisolated
    obtain ⟨J', hJ'mem, hcollision⟩ := hisolated
    refine Or.inr (Set.mem_iUnion.2 ⟨J', Set.mem_iUnion.2 ⟨hJ'mem, ?_⟩⟩)
    exact ⟨hseed, hcollision⟩

/-- Cardinality union bound for the seeds spoiled by a finite family of alternatives. -/
theorem ncard_commonBucketSeeds_le_ncard_isolatedSeeds_add_sum_ncard_collisionSeeds
    (I J : ι → R) (alternatives : Finset (ι → R)) (b : R) :
    (commonBucketSeeds I J b).ncard ≤
      (isolatedSeeds I J alternatives b).ncard +
        ∑ J' ∈ alternatives, (collisionSeeds I J J' b).ncard := by
  classical
  let collisions : Set (ProgressionHash.Seed R ι) :=
    ⋃ J' ∈ alternatives, collisionSeeds I J J' b
  calc
    (commonBucketSeeds I J b).ncard ≤
        (isolatedSeeds I J alternatives b ∪ collisions).ncard :=
      Set.ncard_le_ncard
        (commonBucketSeeds_subset_isolatedSeeds_union_iUnion_collisionSeeds
          I J alternatives b)
    _ ≤ (isolatedSeeds I J alternatives b).ncard + collisions.ncard :=
      Set.ncard_union_le _ _
    _ ≤ (isolatedSeeds I J alternatives b).ncard +
        ∑ J' ∈ alternatives, (collisionSeeds I J J' b).ncard := by
      exact Nat.add_le_add_left (alternatives.set_ncard_biUnion_le
        (fun J' => collisionSeeds I J J' b)) _

/-- Each collision fiber, multiplied by the field cardinality, has the cardinality of the
intended common-bucket fiber. -/
theorem ncard_collisionSeeds_mul_card (I J J' : ι → R) (b : R) (hJJ' : J' ≠ J) :
    (collisionSeeds I J J' b).ncard * Fintype.card R =
      (commonBucketSeeds I J b).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  change Nat.card {seed : ProgressionHash.Seed R ι //
      InCommonBucket I J b seed ∧ seed.yHash J' = b} * Fintype.card R =
    Nat.card {seed : ProgressionHash.Seed R ι // InCommonBucket I J b seed}
  simpa only [Nat.card_eq_fintype_card] using
      card_commonBucket_collision_mul I J J' b hJJ'

/-- Division-free conditional union bound.  If every listed alternative differs from the intended
`Y`-index, multiplying the common-bucket count by `|R|` is bounded by the isolated count times
`|R|`, plus one common-bucket count for each possible collision. -/
theorem ncard_commonBucketSeeds_mul_card_le_ncard_isolatedSeeds_mul_card_add
    (I J : ι → R) (alternatives : Finset (ι → R)) (b : R)
    (hdistinct : ∀ J' ∈ alternatives, J' ≠ J) :
    (commonBucketSeeds I J b).ncard * Fintype.card R ≤
      (isolatedSeeds I J alternatives b).ncard * Fintype.card R +
        alternatives.card * (commonBucketSeeds I J b).ncard := by
  classical
  have hunion :=
    ncard_commonBucketSeeds_le_ncard_isolatedSeeds_add_sum_ncard_collisionSeeds
      I J alternatives b
  calc
    (commonBucketSeeds I J b).ncard * Fintype.card R ≤
        ((isolatedSeeds I J alternatives b).ncard +
          ∑ J' ∈ alternatives, (collisionSeeds I J J' b).ncard) *
            Fintype.card R := Nat.mul_le_mul_right _ hunion
    _ = (isolatedSeeds I J alternatives b).ncard * Fintype.card R +
        ∑ J' ∈ alternatives,
          (collisionSeeds I J J' b).ncard * Fintype.card R := by
      rw [Nat.add_mul, Finset.sum_mul]
    _ = (isolatedSeeds I J alternatives b).ncard * Fintype.card R +
        ∑ _J' ∈ alternatives, (commonBucketSeeds I J b).ncard := by
      congr 1
      apply Finset.sum_congr rfl
      intro J' hJ'
      exact ncard_collisionSeeds_mul_card I J J' b (hdistinct J' hJ')
    _ = (isolatedSeeds I J alternatives b).ncard * Fintype.card R +
        alternatives.card * (commonBucketSeeds I J b).ncard := by simp

/-- Exact finite `3/4` survival statement used by the asymmetric hashing proofs.  If the number
of competing `Y`-indices is at most one quarter of the field size, at least three quarters of the
intended common-bucket seeds are isolated against all competitors. -/
theorem three_mul_ncard_commonBucketSeeds_le_four_mul_ncard_isolatedSeeds
    (I J : ι → R) (alternatives : Finset (ι → R)) (b : R)
    (hdistinct : ∀ J' ∈ alternatives, J' ≠ J)
    (hquarter : 4 * alternatives.card ≤ Fintype.card R) :
    3 * (commonBucketSeeds I J b).ncard ≤
      4 * (isolatedSeeds I J alternatives b).ncard := by
  let base := (commonBucketSeeds I J b).ncard
  let isolated := (isolatedSeeds I J alternatives b).ncard
  let degree := alternatives.card
  let q := Fintype.card R
  have hq : 0 < q := Fintype.card_pos
  have hquarter' : 4 * degree ≤ q := hquarter
  have hunion : base * q ≤ isolated * q + degree * base := by
    exact ncard_commonBucketSeeds_mul_card_le_ncard_isolatedSeeds_mul_card_add
      I J alternatives b hdistinct
  have hcancel : (3 * base) * q ≤ (4 * isolated) * q := by
    nlinarith [hunion, hquarter']
  have hresult : 3 * base ≤ 4 * isolated := le_of_mul_le_mul_right hcancel hq
  simpa [base, isolated] using hresult

section Averaging

variable {τ : Type*}

/-- Target/bucket incidences isolated by a fixed affine-hash seed.  Counting incidences is the
convenient double-counting representation; a later lemma shows that a target can occur in at most
one bucket. -/
noncomputable def isolatedIncidences
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (seed : ProgressionHash.Seed R ι) : Finset (τ × R) :=
  by
    classical
    exact (targets.product buckets).filter fun pair =>
      seed ∈ isolatedSeeds (xIndex pair.1) (yIndex pair.1) (alternatives pair.1) pair.2

/-- Targets represented by the isolated target/bucket incidences of a fixed seed. -/
noncomputable def isolatedTargets
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (seed : ProgressionHash.Seed R ι) : Finset τ :=
  by
    classical
    exact (isolatedIncidences targets buckets xIndex yIndex alternatives seed).image Prod.fst

omit [Fintype R] in
/-- A fixed target cannot occur in two distinct hash buckets. -/
theorem isolatedIncidences_fst_injOn
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (seed : ProgressionHash.Seed R ι) :
    Set.InjOn Prod.fst
      (isolatedIncidences targets buckets xIndex yIndex alternatives seed : Set (τ × R)) := by
  classical
  rintro ⟨t, b⟩ ht ⟨u, c⟩ hu htu
  simp only at htu
  subst u
  have htEvent := (Finset.mem_filter.mp ht).2
  have huEvent := (Finset.mem_filter.mp hu).2
  change seed ∈ isolatedSeeds (xIndex t) (yIndex t) (alternatives t) b at htEvent
  change seed ∈ isolatedSeeds (xIndex t) (yIndex t) (alternatives t) c at huEvent
  have hbc : b = c := htEvent.1.1.symm.trans huEvent.1.1
  exact Prod.ext rfl hbc

omit [Fintype R] in
/-- Counting target/bucket incidences is the same as counting their target projections. -/
theorem card_isolatedTargets_eq_card_isolatedIncidences
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (seed : ProgressionHash.Seed R ι) :
    (isolatedTargets targets buckets xIndex yIndex alternatives seed).card =
      (isolatedIncidences targets buckets xIndex yIndex alternatives seed).card := by
  classical
  unfold isolatedTargets
  exact Finset.card_image_of_injOn
    (isolatedIncidences_fst_injOn targets buckets xIndex yIndex alternatives seed)

/-- Finite good-seed theorem for asymmetric hashing.  If every target has at most `|R|/4`
competing `Y`-indices, some affine seed isolates at least
`3 * |targets| * |buckets| / (4 * |R|²)` target/bucket incidences.  The inequality is written
without division, so it is exact over natural numbers.

This is the finite averaging step shared by the global and recursive constituent hashing stages.
-/
theorem exists_seed_many_isolatedIncidences
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (hdistinct : ∀ t ∈ targets, ∀ J' ∈ alternatives t, J' ≠ yIndex t)
    (hquarter : ∀ t ∈ targets, 4 * (alternatives t).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R ι,
      3 * targets.card * buckets.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (isolatedIncidences targets buckets xIndex yIndex alternatives seed).card := by
  classical
  let pairs := targets.product buckets
  let seeds : Finset (ProgressionHash.Seed R ι) := Finset.univ
  let relation : (τ × R) → ProgressionHash.Seed R ι → Prop := fun pair seed =>
    seed ∈ isolatedSeeds (xIndex pair.1) (yIndex pair.1)
      (alternatives pair.1) pair.2
  have hseeds : seeds.Nonempty := by simp [seeds]
  obtain ⟨chosen, hchosen, hmax⟩ := Finset.exists_max_image seeds
    (fun seed => (pairs.bipartiteBelow relation seed).card) hseeds
  let base := Fintype.card R ^ Fintype.card ι
  have habove (pair : τ × R) :
      (seeds.bipartiteAbove relation pair).card =
        (isolatedSeeds (xIndex pair.1) (yIndex pair.1)
          (alternatives pair.1) pair.2).ncard := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext seed
    simp [seeds, relation, Finset.bipartiteAbove]
  have hpair (pair : τ × R) (hpairMem : pair ∈ pairs) :
      3 * base ≤ 4 * (seeds.bipartiteAbove relation pair).card := by
    obtain ⟨t, b⟩ := pair
    have hmem : t ∈ targets ∧ b ∈ buckets := by
      simpa [pairs] using hpairMem
    have hisolated :=
      three_mul_ncard_commonBucketSeeds_le_four_mul_ncard_isolatedSeeds
        (xIndex t) (yIndex t) (alternatives t) b
        (hdistinct t hmem.1) (hquarter t hmem.1)
    rw [ncard_commonBucketSeeds] at hisolated
    simpa [base, habove] using hisolated
  have hlower :
      pairs.card * (3 * base) ≤
        ∑ pair ∈ pairs, 4 * (seeds.bipartiteAbove relation pair).card := by
    calc
      pairs.card * (3 * base) = ∑ _pair ∈ pairs, 3 * base := by simp
      _ ≤ ∑ pair ∈ pairs, 4 * (seeds.bipartiteAbove relation pair).card :=
        Finset.sum_le_sum fun pair hpairMem => hpair pair hpairMem
  have hdouble :
      (∑ pair ∈ pairs, (seeds.bipartiteAbove relation pair).card) =
        ∑ seed ∈ seeds, (pairs.bipartiteBelow relation seed).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow relation
  have hupper :
      (∑ seed ∈ seeds, (pairs.bipartiteBelow relation seed).card) ≤
        seeds.card * (pairs.bipartiteBelow relation chosen).card := by
    calc
      (∑ seed ∈ seeds, (pairs.bipartiteBelow relation seed).card) ≤
          ∑ _seed ∈ seeds, (pairs.bipartiteBelow relation chosen).card :=
        Finset.sum_le_sum fun seed hseed => hmax seed hseed
      _ = seeds.card * (pairs.bipartiteBelow relation chosen).card := by simp
  have hraw :
      pairs.card * (3 * base) ≤
        4 * (seeds.card * (pairs.bipartiteBelow relation chosen).card) := by
    calc
      pairs.card * (3 * base) ≤
          ∑ pair ∈ pairs, 4 * (seeds.bipartiteAbove relation pair).card := hlower
      _ = 4 * (∑ pair ∈ pairs, (seeds.bipartiteAbove relation pair).card) := by
        rw [Finset.mul_sum]
      _ = 4 * (∑ seed ∈ seeds, (pairs.bipartiteBelow relation seed).card) := by
        rw [hdouble]
      _ ≤ 4 * (seeds.card * (pairs.bipartiteBelow relation chosen).card) :=
        Nat.mul_le_mul_left 4 hupper
  have hpairsCard : pairs.card = targets.card * buckets.card := by
    simp [pairs]
  have hseedsCard :
      seeds.card = Fintype.card R * (Fintype.card R * base) := by
    rw [show seeds.card = Fintype.card (ProgressionHash.Seed R ι) by simp [seeds]]
    simpa [base] using (card_seed (R := R) (ι := ι))
  have hbasePos : 0 < base := pow_pos Fintype.card_pos _
  have hcancel :
      (3 * targets.card * buckets.card) * base ≤
        (4 * (Fintype.card R * Fintype.card R) *
          (pairs.bipartiteBelow relation chosen).card) * base := by
    rw [hpairsCard, hseedsCard] at hraw
    simpa [mul_assoc, mul_comm, mul_left_comm] using hraw
  have hresult :
      3 * targets.card * buckets.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (pairs.bipartiteBelow relation chosen).card :=
    le_of_mul_le_mul_right hcancel hbasePos
  refine ⟨chosen, ?_⟩
  simpa [pairs, relation, isolatedIncidences, Finset.bipartiteBelow] using hresult

/-- Target-count form of `exists_seed_many_isolatedIncidences`. -/
theorem exists_seed_many_isolatedTargets
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (hdistinct : ∀ t ∈ targets, ∀ J' ∈ alternatives t, J' ≠ yIndex t)
    (hquarter : ∀ t ∈ targets, 4 * (alternatives t).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R ι,
      3 * targets.card * buckets.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (isolatedTargets targets buckets xIndex yIndex alternatives seed).card := by
  obtain ⟨seed, hseed⟩ := exists_seed_many_isolatedIncidences
    targets buckets xIndex yIndex alternatives hdistinct hquarter
  refine ⟨seed, ?_⟩
  rwa [card_isolatedTargets_eq_card_isolatedIncidences] 

omit [Fintype R] in
/-- If every genuine competitor sharing a target's `X`-index contributes its `Y`-index to the
alternative list, the isolated target family has pairwise distinct `X`-indices.  This is the exact
combinatorial extraction property produced by the more-asymmetric hashing cleanup. -/
theorem xIndex_injectiveOn_isolatedTargets
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (seed : ProgressionHash.Seed R ι)
    (hcomplete : ∀ t ∈ targets, ∀ u ∈ targets, u ≠ t →
      xIndex u = xIndex t → yIndex u ∈ alternatives t) :
    Set.InjOn xIndex
      (isolatedTargets targets buckets xIndex yIndex alternatives seed : Set τ) := by
  classical
  intro t ht u hu hxu
  have ht' : t ∈ (isolatedIncidences targets buckets xIndex yIndex alternatives seed).image
      Prod.fst := by simpa [isolatedTargets] using ht
  have hu' : u ∈ (isolatedIncidences targets buckets xIndex yIndex alternatives seed).image
      Prod.fst := by simpa [isolatedTargets] using hu
  obtain ⟨⟨t', b⟩, htb, rfl⟩ := Finset.mem_image.mp ht'
  obtain ⟨⟨u', c⟩, huc, rfl⟩ := Finset.mem_image.mp hu'
  have htFilter := Finset.mem_filter.mp htb
  have huFilter := Finset.mem_filter.mp huc
  have htTarget : t' ∈ targets := (Finset.mem_product.mp htFilter.1).1
  have huTarget : u' ∈ targets := (Finset.mem_product.mp huFilter.1).1
  have htEvent := htFilter.2
  have huEvent := huFilter.2
  change xIndex t' = xIndex u' at hxu
  change seed ∈ isolatedSeeds (xIndex t') (yIndex t') (alternatives t') b at htEvent
  change seed ∈ isolatedSeeds (xIndex u') (yIndex u') (alternatives u') c at huEvent
  have hbc : b = c := by
    calc
      b = seed.xHash (xIndex t') := htEvent.1.1.symm
      _ = seed.xHash (xIndex u') := congrArg (seed.xHash ·) hxu
      _ = c := huEvent.1.1
  by_contra hne
  change t' ≠ u' at hne
  have hyAlternative : yIndex u' ∈ alternatives t' :=
    hcomplete t' htTarget u' huTarget hne.symm hxu.symm
  have hnot : seed.yHash (yIndex u') ≠ b := htEvent.2 _ hyAlternative
  apply hnot
  rw [hbc]
  exact huEvent.1.2

end Averaging

end ProgressionHash.Seed

end AlgebraicComplexity
