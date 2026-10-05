/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ChargedFiniteAveraging
import AlgebraicComplexity.Combinatorics.HashingCollisionIncidence
import AlgebraicComplexity.Combinatorics.HashingIsolationIncidenceAveraging

/-!
# Choosing one affine seed after charging shared-leg collisions

The aggregate isolation theorem gives a lower bound on the reward summed over all affine seeds,
while the shared-leg collision theorem computes the damage summed over the same seeds.  This file
combines those two exact identities before choosing a seed.

If `targets` is the coarse target family and `witnesses` is a family of distinct legal-triple
pairs sharing one leg, the degree condition

`4 * witnesses.card ≤ targets.card * Fintype.card R`

ensures that the total collision charge consumes at most two of the three units in the aggregate
isolation lower bound.  Consequently one seed simultaneously pays the baseline
`targets.card * buckets.card` and eight times its shared-leg collision incidence.  The statement is
division-free and uses only natural-number cardinalities.

This theorem deliberately does not identify collision witnesses with holes in a tensor cleanup.
A client must construct an injection from its literal damaged fine blocks into `witnesses`; in the
recursive CW application, bounding that witness family is the paper's compatibility quotient
count.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w x

namespace ProgressionHash

variable {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
variable {ι : Type v} [Fintype ι]
variable {τ : Type w} {W : Type x}
variable {target : R}

/-- A single affine seed whose isolated-incidence reward pays both the target/bucket baseline and
shared-leg collision damage.

Proof sketch: aggregate isolation supplies three copies of the target/bucket/seed count.  The
exact collision double count, together with `4 * |W| ≤ |targets| * |R|`, bounds the collision
charge by two such copies.  Division-free charged averaging then selects one seed from the
remaining copy. -/
theorem exists_seed_baseline_add_sharedLegCollisionCharge_le_isolatedReward
    (targets : Finset τ) (buckets : Finset R)
    (xIndex yIndex : τ → ι → R)
    (alternatives : τ → Finset (ι → R))
    (hdistinct : ∀ t ∈ targets, ∀ J' ∈ alternatives t, J' ≠ yIndex t)
    (hquarter : ∀ t ∈ targets,
      4 * (alternatives t).card ≤ Fintype.card R)
    (witnesses : Finset W)
    (left right : W → LegalTriple R ι target)
    (sharedLeg : W → Tensor.Leg)
    (hne : ∀ witness ∈ witnesses, right witness ≠ left witness)
    (hshared : ∀ witness ∈ witnesses,
      (right witness).legIndex (sharedLeg witness) =
        (left witness).legIndex (sharedLeg witness))
    (hdegree : 4 * witnesses.card ≤ targets.card * Fintype.card R) :
    ∃ seed : Seed R ι,
      targets.card * buckets.card +
          8 * (Fintype.card R * Fintype.card R) *
            LegalTriple.sharedLegPairCollisionIncidence
              witnesses left right buckets seed ≤
        4 * (Fintype.card R * Fintype.card R) *
          (Seed.isolatedIncidences
            targets buckets xIndex yIndex alternatives seed).card := by
  classical
  let q := Fintype.card R
  let seedCount := Fintype.card (Seed R ι)
  let targetCount := targets.card
  let bucketCount := buckets.card
  let witnessCount := witnesses.card
  let reward : Seed R ι → ℕ := fun seed ↦
    (Seed.isolatedIncidences
      targets buckets xIndex yIndex alternatives seed).card
  let damage : Seed R ι → ℕ := fun seed ↦
    LegalTriple.sharedLegPairCollisionIncidence witnesses left right buckets seed
  let totalReward := ∑ seed : Seed R ι, reward seed
  let totalDamage := ∑ seed : Seed R ι, damage seed

  have hrewards :
      3 * targetCount * bucketCount * seedCount ≤
        4 * (q * q) * totalReward := by
    simpa only [q, seedCount, targetCount, bucketCount, reward, totalReward] using
      Seed.three_mul_targets_mul_buckets_mul_seeds_le_four_mul_square_mul_sum_isolatedIncidences
        targets buckets xIndex yIndex alternatives hdistinct hquarter

  have hdamages :
      totalDamage * (q * q * q) = witnessCount * bucketCount * seedCount := by
    simpa only [q, seedCount, bucketCount, witnessCount, damage, totalDamage] using
      LegalTriple.sum_sharedLegPairCollisionIncidence_mul_cube
        witnesses left right sharedLeg hne hshared buckets

  have hq : 0 < q := by
    exact Fintype.card_pos
  have hchargedScaled :
      (8 * (q * q) * totalDamage) * q ≤
        (2 * targetCount * bucketCount * seedCount) * q := by
    calc
      (8 * (q * q) * totalDamage) * q =
          8 * (totalDamage * (q * q * q)) := by ring
      _ = 8 * (witnessCount * bucketCount * seedCount) := by rw [hdamages]
      _ = (2 * (4 * witnessCount)) * bucketCount * seedCount := by ring
      _ ≤ (2 * (targetCount * q)) * bucketCount * seedCount := by
        simpa only [mul_assoc] using
          Nat.mul_le_mul_right (bucketCount * seedCount)
            (Nat.mul_le_mul_left 2 hdegree)
      _ = (2 * targetCount * bucketCount * seedCount) * q := by ring
  have hcharged :
      8 * (q * q) * totalDamage ≤
        2 * targetCount * bucketCount * seedCount :=
    Nat.le_of_mul_le_mul_right hchargedScaled hq

  have hglobalTotals :
      seedCount * (targetCount * bucketCount) +
        8 * (q * q) * totalDamage ≤ 4 * (q * q) * totalReward
      := by
    calc
      seedCount * (targetCount * bucketCount) + 8 * (q * q) * totalDamage =
          targetCount * bucketCount * seedCount + 8 * (q * q) * totalDamage := by ring
      _ ≤ targetCount * bucketCount * seedCount +
          2 * targetCount * bucketCount * seedCount :=
        Nat.add_le_add_left hcharged _
      _ = 3 * targetCount * bucketCount * seedCount := by ring
      _ ≤ 4 * (q * q) * totalReward := hrewards
  have hglobal :
      seedCount * (targetCount * bucketCount) +
          ∑ seed : Seed R ι, 8 * (q * q) * damage seed ≤
        ∑ seed : Seed R ι, 4 * (q * q) * reward seed := by
    simpa only [totalDamage, totalReward, Finset.mul_sum] using hglobalTotals

  have hglobalUniv :
      (Finset.univ : Finset (Seed R ι)).card * (targetCount * bucketCount) +
          ∑ seed ∈ (Finset.univ : Finset (Seed R ι)),
            8 * (q * q) * damage seed ≤
        ∑ seed ∈ (Finset.univ : Finset (Seed R ι)),
          4 * (q * q) * reward seed := by
    simpa only [Finset.card_univ, seedCount] using hglobal
  obtain ⟨seed, _hseed, hseedBound⟩ :=
    exists_mem_floor_add_charge_le_reward
      (Finset.univ : Finset (Seed R ι)) Finset.univ_nonempty
      (fun seed ↦ 4 * (q * q) * reward seed)
      (fun seed ↦ 8 * (q * q) * damage seed)
      (targetCount * bucketCount) hglobalUniv
  refine ⟨seed, ?_⟩
  simpa only [q, targetCount, bucketCount, reward, damage] using hseedBound

end ProgressionHash

end AlgebraicComplexity
