/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HashingConditionalIndependence
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Aggregate incidence of shared-leg affine-hash collisions

`HashingConditionalIndependence` proves the exact collision probability for one pair of distinct
legal triples sharing one leg and one fixed bucket.  Repair arguments need the sum of that law over
an arbitrary finite family of compatibility witnesses, all allowed buckets, and all affine seeds.
This file supplies precisely that finite double count.

For a witness family `W`, `sharedLegPairCollisionCount ... b seed` is the number of witnesses whose
two triples both land in bucket `b` under `seed`.  The main identity is

`(sum_seed sum_b collisionCount) * |R|^3 = |W| * |B| * |Seed|`.

It is exact over natural numbers.  There is no probability division, asymptotic estimate, entropy
bound, or tensor premise.  In particular, a later CW client must still construct an injection from
its actual damaged labels into the witness incidences counted here.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
variable {ι : Type v} [Fintype ι]
variable {target : R}

/-- Number of witnesses in a finite shared-leg pair family whose two legal triples both land in
one fixed bucket under one fixed affine seed.  Shared-leg validity and pair distinctness are kept
as theorem hypotheses rather than fields of the witness type. -/
noncomputable def sharedLegPairCollisionCount
    {W : Type w} (witnesses : Finset W)
    (left right : W → LegalTriple R ι target)
    (b : R) (seed : Seed R ι) : ℕ := by
  classical
  exact (witnesses.filter fun witness ↦
    Seed.InCommonTriple
        (left witness).xIndex (left witness).yIndex (left witness).zIndex target b seed ∧
      Seed.InCommonTriple
        (right witness).xIndex (right witness).yIndex (right witness).zIndex target b seed).card

/-- Exact collision incidence for one fixed bucket, summed over every affine seed.

Proof sketch: double-count witness/seed incidences.  For each witness, the existing shared-leg
pair theorem says that its seed fiber, multiplied by `|R|^3`, is the whole seed space.  Summing
that identity over witnesses gives the result. -/
theorem sum_sharedLegPairCollisionCount_mul_cube
    {W : Type w} (witnesses : Finset W)
    (left right : W → LegalTriple R ι target) (sharedLeg : W → Tensor.Leg)
    (hne : ∀ witness ∈ witnesses, right witness ≠ left witness)
    (hshared : ∀ witness ∈ witnesses,
      (right witness).legIndex (sharedLeg witness) =
        (left witness).legIndex (sharedLeg witness))
    (b : R) :
    (∑ seed : Seed R ι,
        sharedLegPairCollisionCount witnesses left right b seed) *
        (Fintype.card R * Fintype.card R * Fintype.card R) =
      witnesses.card * Fintype.card (Seed R ι) := by
  classical
  let seeds : Finset (Seed R ι) := Finset.univ
  let relation : W → Seed R ι → Prop := fun witness seed ↦
    Seed.InCommonTriple
        (left witness).xIndex (left witness).yIndex (left witness).zIndex target b seed ∧
      Seed.InCommonTriple
        (right witness).xIndex (right witness).yIndex (right witness).zIndex target b seed
  have hdouble :
      (∑ seed ∈ seeds, (witnesses.bipartiteBelow relation seed).card) =
        ∑ witness ∈ witnesses, (seeds.bipartiteAbove relation witness).card :=
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := witnesses) (t := seeds) relation).symm
  have hone (witness : W) (hwitness : witness ∈ witnesses) :
      (seeds.bipartiteAbove relation witness).card *
          (Fintype.card R * Fintype.card R * Fintype.card R) =
        seeds.card := by
    have hpair := card_inCommonTriple_pair_mul_cube
      (hne witness hwitness) (hshared witness hwitness) b
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hpair
    simpa only [seeds, relation, Finset.bipartiteAbove, Finset.card_univ] using hpair
  calc
    (∑ seed : Seed R ι,
        sharedLegPairCollisionCount witnesses left right b seed) *
          (Fintype.card R * Fintype.card R * Fintype.card R) =
        (∑ seed ∈ seeds, (witnesses.bipartiteBelow relation seed).card) *
          (Fintype.card R * Fintype.card R * Fintype.card R) := by
      congr 1
    _ = (∑ witness ∈ witnesses, (seeds.bipartiteAbove relation witness).card) *
          (Fintype.card R * Fintype.card R * Fintype.card R) := by
      rw [hdouble]
    _ = ∑ witness ∈ witnesses,
          (seeds.bipartiteAbove relation witness).card *
            (Fintype.card R * Fintype.card R * Fintype.card R) := by
      rw [Finset.sum_mul]
    _ = ∑ _witness ∈ witnesses, seeds.card := by
      apply Finset.sum_congr rfl
      exact hone
    _ = witnesses.card * Fintype.card (Seed R ι) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, seeds, Finset.card_univ]

/-- Total collision incidence of a finite shared-leg witness family over a finite bucket set for
one affine seed. -/
noncomputable def sharedLegPairCollisionIncidence
    {W : Type w} (witnesses : Finset W)
    (left right : W → LegalTriple R ι target)
    (buckets : Finset R) (seed : Seed R ι) : ℕ :=
  ∑ b ∈ buckets, sharedLegPairCollisionCount witnesses left right b seed

/-- Exact aggregate shared-leg collision identity over witnesses, buckets, and affine seeds. -/
theorem sum_sharedLegPairCollisionIncidence_mul_cube
    {W : Type w} (witnesses : Finset W)
    (left right : W → LegalTriple R ι target) (sharedLeg : W → Tensor.Leg)
    (hne : ∀ witness ∈ witnesses, right witness ≠ left witness)
    (hshared : ∀ witness ∈ witnesses,
      (right witness).legIndex (sharedLeg witness) =
        (left witness).legIndex (sharedLeg witness))
    (buckets : Finset R) :
    (∑ seed : Seed R ι,
        sharedLegPairCollisionIncidence witnesses left right buckets seed) *
        (Fintype.card R * Fintype.card R * Fintype.card R) =
      witnesses.card * buckets.card * Fintype.card (Seed R ι) := by
  classical
  calc
    (∑ seed : Seed R ι,
        sharedLegPairCollisionIncidence witnesses left right buckets seed) *
          (Fintype.card R * Fintype.card R * Fintype.card R) =
        (∑ b ∈ buckets, ∑ seed : Seed R ι,
          sharedLegPairCollisionCount witnesses left right b seed) *
            (Fintype.card R * Fintype.card R * Fintype.card R) := by
      congr 1
      simp only [sharedLegPairCollisionIncidence]
      rw [Finset.sum_comm]
    _ = ∑ b ∈ buckets,
          (∑ seed : Seed R ι,
            sharedLegPairCollisionCount witnesses left right b seed) *
              (Fintype.card R * Fintype.card R * Fintype.card R) := by
      rw [Finset.sum_mul]
    _ = ∑ _b ∈ buckets,
          witnesses.card * Fintype.card (Seed R ι) := by
      apply Finset.sum_congr rfl
      intro b _hb
      exact sum_sharedLegPairCollisionCount_mul_cube
        witnesses left right sharedLeg hne hshared b
    _ = witnesses.card * buckets.card * Fintype.card (Seed R ι) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      ring

end ProgressionHash.LegalTriple

end AlgebraicComplexity
