/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HashingExtraction
import Mathlib.Algebra.Field.ZMod

/-!
# Tiny hashing regression client

This file specializes the generic affine-hashing API to one coordinate over `ZMod 5`.  It is
deliberately tiny: its purpose is to catch changes in event direction, the `Z`-hash convention,
or conditional-collision normalization without importing the optional probability adapter.

## Regression theorems

* `inCommonTriple_iff_inCommonBucket`: the `Z`-hash convention;
* `card_commonBucketCollision_mul_card_field`: the exact conditional-collision fiber count;
* `three_mul_ncard_commonBucketSeeds_le_four_mul_ncard_isolatedSeeds`: the `3/4` isolation
  bound with a single competitor;
* `survivesHashFilter_iff_exists_commonBucket`: the direction of the progression-free filter
  event.
-/

namespace AlgebraicComplexity.Examples.Hashing

open ProgressionHash

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : NeZero (2 : ZMod 5) := ⟨by decide⟩

private def zeroIndex : Fin 1 → ZMod 5 := fun _ => 0
private def oneIndex : Fin 1 → ZMod 5 := fun _ => 1

private def unitTriple : LegalTriple (ZMod 5) (Fin 1) 1 where
  xIndex := zeroIndex
  yIndex := zeroIndex
  zIndex := oneIndex
  legal := by intro i; simp [zeroIndex, oneIndex]

private theorem oneIndex_ne_zeroIndex : oneIndex ≠ zeroIndex := by
  intro h
  have h10 : (1 : ZMod 5) = 0 := congrFun h 0
  exact one_ne_zero h10

/-- For a legal one-coordinate triple, the third hash follows from the first two: the
`X`/`Y`/`Z` triple lands in the common bucket `b` exactly when the two input hashes already
do.  This pins down the `Z`-hash convention of `Seed.InCommonTriple`. -/
theorem inCommonTriple_iff_inCommonBucket (seed : Seed (ZMod 5) (Fin 1)) (b : ZMod 5) :
    Seed.InCommonTriple zeroIndex zeroIndex oneIndex 1 b seed ↔
      Seed.InCommonBucket zeroIndex zeroIndex b seed := by
  apply Seed.inCommonTriple_iff_commonBucket
  intro i
  simp [zeroIndex, oneIndex]

/-- Replacing the zero `Y`-index by the one `Y`-index removes exactly one field degree of
freedom from the common-bucket fiber: the sub-fiber on which the competitor `oneIndex` also
hashes to `b` is exactly `|ZMod 5|` times smaller than the whole common-bucket fiber. -/
theorem card_commonBucketCollision_mul_card_field (b : ZMod 5) :
    Nat.card {seed : Seed (ZMod 5) (Fin 1) //
        Seed.InCommonBucket zeroIndex zeroIndex b seed ∧ seed.yHash oneIndex = b} *
          Nat.card (ZMod 5) =
      Nat.card {seed : Seed (ZMod 5) (Fin 1) //
        Seed.InCommonBucket zeroIndex zeroIndex b seed} := by
  apply Seed.card_commonBucket_collision_mul
  exact oneIndex_ne_zeroIndex

/-- With one competitor over a five-element field, the generic isolation theorem gives the
paper-facing `3/4` survival bound: at least three quarters of the common-bucket seeds isolate
the target from the single competitor `oneIndex`. -/
theorem three_mul_ncard_commonBucketSeeds_le_four_mul_ncard_isolatedSeeds (b : ZMod 5) :
    3 * (Seed.commonBucketSeeds zeroIndex zeroIndex b).ncard ≤
      4 * (Seed.isolatedSeeds zeroIndex zeroIndex {oneIndex} b).ncard := by
  apply Seed.three_mul_ncard_commonBucketSeeds_le_four_mul_ncard_isolatedSeeds
  · intro J' hJ'
    simp only [Finset.mem_singleton] at hJ'
    subst J'
    exact oneIndex_ne_zeroIndex
  · norm_num [ZMod.card]

/-- The progression-free filtering interface specializes to the expected common-bucket event:
the one-coordinate legal triple survives the `B`-filter for a seed exactly when some `b ∈ B`
is a common bucket of its two input hashes. -/
theorem survivesHashFilter_iff_exists_commonBucket
    (B : Set (ZMod 5)) (hB : ThreeAPFree B) (seed : Seed (ZMod 5) (Fin 1)) :
    LegalTriple.SurvivesHashFilter B seed unitTriple ↔
      ∃ b ∈ B, Seed.InCommonBucket zeroIndex zeroIndex b seed := by
  simpa [unitTriple] using
    (LegalTriple.survivesHashFilter_iff_exists_commonBucket hB seed unitTriple)

end AlgebraicComplexity.Examples.Hashing
