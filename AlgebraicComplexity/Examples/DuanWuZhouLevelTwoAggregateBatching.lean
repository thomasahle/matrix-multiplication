/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoBatching
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAggregateHoleBudget

set_option autoImplicit false

/-!
# Batching from the aggregate hole fraction

`Examples/DuanWuZhouLevelTwoBatching.lean` derives the Hole-Lemma budget from a **per-copy** bound
`8 * |holes a| ≤ card(avail)`, which `Examples/DuanWuZhouLevelTwoHoleFractionRefutation.lean`
shows is unreachable: it forces `card(avail) = 0`.  That arithmetic stays posted and stays valid;
this module replaces its *input* by the aggregate form
`Dwz63AggregateHoleFraction`, `16 * ∑_a |holes a| ≤ #retained * card(avail)`, and takes the
good-subset batching of `Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean`, which batches only
the copies whose own hole set is small and absorbs the rest by a Markov count.

The two size constants are linear in the word length, so the copy-count loss stays polynomial:
`card(avail) ≤ 9 ^ (n+1) ≤ 2 ^ (4 * (n+1))`, so `L := dwz63AvailLog n = 4 * (n+1)` works, and
`k := dwz63GoodBatchSize n = 5 * (n+1) + 1` satisfies the good-subset requirement
`8 * (L + 1) ≤ 7 * k`, i.e. `32n + 40 ≤ 35n + 42`.

`[DuanWuZhou2022]`, `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v w

/-- The binary log bound on the number of available words. -/
def dwz63AvailLog (n : ℕ) : ℕ := 4 * (n + 1)

/-- The good-subset batch size. -/
def dwz63GoodBatchSize (n : ℕ) : ℕ := 5 * (n + 1) + 1

theorem dwz63GoodBatchSize_pos (n : ℕ) : 0 < dwz63GoodBatchSize n := by
  unfold dwz63GoodBatchSize
  omega

/-- **The available words fit in `2 ^ (4 * (n+1))`.** -/
theorem card_segmentedAvailableWord_le_two_pow {n m : ℕ} (seg : Fin (n + 1) → Fin m)
    (α : Fin m → PositiveWord CWBlock 1 → ℕ) :
    Fintype.card (SegmentedAvailableWord seg α) ≤ 2 ^ dwz63AvailLog n := by
  refine le_trans (card_segmentedAvailableWord_le seg α) ?_
  calc (9 : ℕ) ^ (n + 1) ≤ 16 ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) _
    _ = 2 ^ dwz63AvailLog n := by
        unfold dwz63AvailLog
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]

/-- **The good-subset size requirement.**  `8 * (L + 1) ≤ 7 * k`. -/
theorem dwz63_eight_mul_availLog_le (n : ℕ) :
    8 * (dwz63AvailLog n + 1) ≤ 7 * dwz63GoodBatchSize n := by
  unfold dwz63AvailLog dwz63GoodBatchSize
  omega

section Package

variable {n m : ℕ} {τ : Type v} [Fintype τ] [DecidableEq τ]

/-- **`hbatch` from the aggregate hole fraction.** -/
theorem dwz63_aggregate_hbatch (seg : Fin (n + 1) → Fin m)
    (α : Fin m → PositiveWord CWBlock 1 → ℕ)
    (retained : Finset τ)
    (holes : retained → Finset (SegmentedAvailableWord seg α))
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (haggregate : Dwz63AggregateHoleFraction seg α retained holes)
    {batches : ℕ} (hbatches : 0 < batches)
    (hfit : 2 * (batches * dwz63GoodBatchSize n) ≤ retained.card) :
    Function.Surjective
      (dwz63GoodBatch (dwz63GoodCopies holes) (dwz63GoodBatchSize n) hbatches) :=
  dwz63GoodBatch_surjective_of_aggregateHoleFraction seg α retained holes hpos haggregate
    (dwz63GoodBatchSize_pos n) hbatches hfit

/-- **`hbudget` from the aggregate hole fraction**, in the shape the stage requires. -/
theorem dwz63_aggregate_hbudget (seg : Fin (n + 1) → Fin m)
    (α : Fin m → PositiveWord CWBlock 1 → ℕ)
    (retained : Finset τ)
    (holes : retained → Finset (SegmentedAvailableWord seg α))
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (haggregate : Dwz63AggregateHoleFraction seg α retained holes)
    {batches : ℕ} (hbatches : 0 < batches)
    (hfit : 2 * (batches * dwz63GoodBatchSize n) ≤ retained.card) :
    ∀ b : Fin batches,
      Fintype.card (SegmentedAvailableWord seg α) *
          ∏ a : {a : retained //
            dwz63GoodBatch (dwz63GoodCopies holes) (dwz63GoodBatchSize n) hbatches a = b},
            (holes a.1).card <
        Fintype.card (SegmentedAvailableWord seg α) ^
          Fintype.card {a : retained //
            dwz63GoodBatch (dwz63GoodCopies holes) (dwz63GoodBatchSize n) hbatches a = b} :=
  dwz63_hbudget_of_aggregateHoleFraction_of_card seg α retained holes (dwz63AvailLog n) hpos
    (card_segmentedAvailableWord_le_two_pow seg α) haggregate
    (dwz63GoodBatchSize_pos n) hbatches (dwz63_eight_mul_availLog_le n) hfit

end Package

/-! ## The number of batches, and the copy-count loss -/

/-- The number of good-subset batches: as many as fit twice over. -/
def dwz63GoodBatchCount (N n : ℕ) : ℕ := N / (2 * dwz63GoodBatchSize n)

theorem dwz63GoodBatchCount_fit (N n : ℕ) :
    2 * (dwz63GoodBatchCount N n * dwz63GoodBatchSize n) ≤ N := by
  have h : (N / (2 * dwz63GoodBatchSize n)) * (2 * dwz63GoodBatchSize n) ≤ N :=
    Nat.div_mul_le_self _ _
  unfold dwz63GoodBatchCount
  calc 2 * (N / (2 * dwz63GoodBatchSize n) * dwz63GoodBatchSize n)
      = (N / (2 * dwz63GoodBatchSize n)) * (2 * dwz63GoodBatchSize n) := by ring
    _ ≤ N := h

theorem dwz63GoodBatchCount_pos {N n : ℕ} (h : 2 * dwz63GoodBatchSize n ≤ N) :
    0 < dwz63GoodBatchCount N n :=
  Nat.div_pos h (by have := dwz63GoodBatchSize_pos n; omega)

/-- **The copy-count loss is the linear factor `4 * dwz63GoodBatchSize n = 20 * (n+1) + 4`.** -/
theorem card_le_four_mul_batchSize_mul_batchCount {N n : ℕ}
    (h : 2 * dwz63GoodBatchSize n ≤ N) :
    N ≤ 4 * dwz63GoodBatchSize n * dwz63GoodBatchCount N n := by
  have hk : 0 < dwz63GoodBatchSize n := dwz63GoodBatchSize_pos n
  have hpos : 0 < 2 * dwz63GoodBatchSize n := by omega
  have hmod := Nat.div_add_mod N (2 * dwz63GoodBatchSize n)
  have hlt := Nat.mod_lt N hpos
  have hone : 2 * dwz63GoodBatchSize n ≤
      2 * dwz63GoodBatchSize n * (N / (2 * dwz63GoodBatchSize n)) :=
    Nat.le_mul_of_pos_right _ (dwz63GoodBatchCount_pos h)
  have hsplit : 4 * dwz63GoodBatchSize n * (N / (2 * dwz63GoodBatchSize n)) =
      2 * dwz63GoodBatchSize n * (N / (2 * dwz63GoodBatchSize n)) +
        2 * dwz63GoodBatchSize n * (N / (2 * dwz63GoodBatchSize n)) := by ring
  unfold dwz63GoodBatchCount
  omega

end AlgebraicComplexity.Examples
