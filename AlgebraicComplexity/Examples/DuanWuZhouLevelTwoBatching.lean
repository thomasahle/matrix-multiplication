/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGroupedLeaf

set_option autoImplicit false

/-!
# Batching the retained triples

`dwz63_groupedStage_of_claim3` carries `batch`, `hbatch` and `hbudget`.  This module supplies all
three.

The budget, in the shape that theorem states it, is
`card(avail) * ∏_{a ∈ batch b} |holes a| < card(avail) ^ #(batch b)`.  With the per-triple hole
bound `8 * |holes a| ≤ card(avail)` the product over a batch of `k` triples is at most
`card(avail)^k / 8^k`, so the budget holds as soon as `card(avail) < 8 ^ k`.  A batch of one
therefore forces `holes = ∅` --- the seam recorded at image 58 --- and every batch must have size
at least `k₀`.

`k₀` is *linear in `n`*: a segmented available word is a word of length `n + 1` over the
nine-letter pair alphabet `PositiveWord CWBlock 1`, so `card(avail) ≤ 9 ^ (n + 1)`, and
`dwz63BatchSize n = 4 * (n + 1) + 1` already satisfies `9 ^ (n + 1) < 8 ^ (4 * (n + 1) + 1)`.  The
resulting copy count `#β = #retained / k₀` loses only the polynomial factor `2 * k₀`, which is the
subexponential loss the open-integration endpoint absorbs.

The batching itself is the obvious one: number the retained triples, cut them into consecutive
blocks of `k₀`, and let the last block absorb the remainder, so every block has size in
`[k₀, 2 * k₀)`.

`[DuanWuZhou2022]`, `hole_lemma.tex`, `global_value.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v w

/-! ## The budget from a per-triple hole bound -/

/-- **The batched budget from the per-triple bound.**

If every triple in the batch loses at most an eighth of the available words, and the batch is
large enough that `card(avail) < 8 ^ k`, the Hole Lemma's finite budget holds. -/
theorem mul_prod_lt_pow_of_eight_mul_le {ι : Type w} [Fintype ι] {A : ℕ} (hA : 0 < A)
    (c : ι → ℕ) (hc : ∀ a, 8 * c a ≤ A)
    {k₀ : ℕ} (hk₀ : A < 8 ^ k₀) (hcard : k₀ ≤ Fintype.card ι) :
    A * ∏ a : ι, c a < A ^ Fintype.card ι := by
  classical
  have hprod : 8 ^ Fintype.card ι * ∏ a : ι, c a ≤ A ^ Fintype.card ι := by
    have h : ∏ a : ι, (8 * c a) ≤ ∏ _a : ι, A :=
      Finset.prod_le_prod' fun a _ ↦ hc a
    simpa [Finset.prod_mul_distrib, Finset.prod_const] using h
  have hlt : A < 8 ^ Fintype.card ι :=
    lt_of_lt_of_le hk₀ (Nat.pow_le_pow_right (by norm_num) hcard)
  rcases Nat.eq_zero_or_pos (∏ a : ι, c a) with h0 | hpos
  · rw [h0, Nat.mul_zero]
    exact pow_pos hA _
  · exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hlt hpos) hprod

/-! ## Consecutive blocks of a fixed size -/

section Blocks

variable (ι : Type w) [Fintype ι]

/-- Every index inside block `j` is an index of `ι`. -/
theorem blockIndex_lt {k : ℕ} (_hk : 0 < k)
    (j : Fin (Fintype.card ι / k)) {i : ℕ} (hi : i < k) :
    j.val * k + i < Fintype.card ι := by
  have hj : j.val + 1 ≤ Fintype.card ι / k := j.isLt
  calc j.val * k + i < j.val * k + k := by omega
    _ = (j.val + 1) * k := by ring
    _ ≤ (Fintype.card ι / k) * k := Nat.mul_le_mul_right k hj
    _ ≤ Fintype.card ι := Nat.div_mul_le_self _ _

/-- **The batching**: number the elements, cut into consecutive blocks of `k`, and let the last
block absorb the remainder. -/
noncomputable def blockBatch {k : ℕ} (hq : 0 < Fintype.card ι / k) :
    ι → Fin (Fintype.card ι / k) := fun a ↦
  ⟨min ((Fintype.equivFin ι a).val / k) (Fintype.card ι / k - 1),
    Nat.lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

variable {ι}

/-- The element at offset `i` of block `j` is in block `j`. -/
theorem blockBatch_apply {k : ℕ} (hk : 0 < k) (hq : 0 < Fintype.card ι / k)
    (j : Fin (Fintype.card ι / k)) {i : ℕ} (hi : i < k) :
    blockBatch ι hq ((Fintype.equivFin ι).symm
      ⟨j.val * k + i, blockIndex_lt ι hk j hi⟩) = j := by
  have hdiv : (j.val * k + i) / k = j.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hi, Nat.zero_add]
  apply Fin.ext
  show min (((Fintype.equivFin ι) ((Fintype.equivFin ι).symm
    ⟨j.val * k + i, blockIndex_lt ι hk j hi⟩)).val / k) (Fintype.card ι / k - 1) = j.val
  rw [Equiv.apply_symm_apply]
  show min ((j.val * k + i) / k) (Fintype.card ι / k - 1) = j.val
  rw [hdiv]
  have := j.isLt
  omega

/-- The batching is surjective: no batch is empty. -/
theorem blockBatch_surjective {k : ℕ} (hk : 0 < k) (hq : 0 < Fintype.card ι / k) :
    Function.Surjective (blockBatch ι hq) := fun j ↦
  ⟨_, blockBatch_apply hk hq j hk⟩

/-- **Every batch has at least `k` elements.**  This is the hypothesis `hbudget` needs. -/
theorem card_le_blockBatch_fiber {k : ℕ} (hk : 0 < k) (hq : 0 < Fintype.card ι / k)
    (j : Fin (Fintype.card ι / k)) :
    k ≤ Fintype.card {a : ι // blockBatch ι hq a = j} := by
  classical
  have hinj : Function.Injective
      (fun i : Fin k ↦ (⟨(Fintype.equivFin ι).symm
        ⟨j.val * k + i.val, blockIndex_lt ι hk j i.isLt⟩,
        blockBatch_apply hk hq j i.isLt⟩ : {a : ι // blockBatch ι hq a = j})) := by
    intro i₁ i₂ h
    have h' := congrArg Subtype.val h
    have h'' := congrArg (Fintype.equivFin ι) h'
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h''
    have hval : j.val * k + i₁.val = j.val * k + i₂.val := by
      have h3 := congrArg Fin.val h''
      simpa using h3
    exact Fin.ext (by omega)
  simpa using Fintype.card_le_of_injective _ hinj

/-- **The copy-count loss is the factor `2 * k`.** -/
theorem card_le_two_mul_card_blockBatch {k : ℕ} (hk : 0 < k)
    (hq : 0 < Fintype.card ι / k) :
    Fintype.card ι ≤ 2 * k * Fintype.card (Fin (Fintype.card ι / k)) := by
  rw [Fintype.card_fin]
  have hmod := Nat.div_add_mod (Fintype.card ι) k
  have hlt := Nat.mod_lt (Fintype.card ι) hk
  have hone : k ≤ k * (Fintype.card ι / k) := Nat.le_mul_of_pos_right k hq
  have hsplit : 2 * k * (Fintype.card ι / k) =
      k * (Fintype.card ι / k) + k * (Fintype.card ι / k) := by ring
  omega

end Blocks

/-! ## The section 6.3 batch size -/

/-- The number of available words of length `n + 1` over an alphabet of size `card I`. -/
theorem card_positiveWord (I : Type w) [Fintype I] (n : ℕ) :
    Fintype.card (PositiveWord I n) = Fintype.card I ^ (n + 1) := by
  rw [Fintype.card_congr (positiveWordEquiv I n), Fintype.card_fun, Fintype.card_fin]

/-- **The batch size of section 6.3**, linear in the word length. -/
def dwz63BatchSize (n : ℕ) : ℕ := 4 * (n + 1) + 1

/-- The pair alphabet has nine letters. -/
theorem card_pairAlphabet : Fintype.card (PositiveWord CWBlock 1) = 9 := by
  rw [card_positiveWord]
  rfl

/-- **The available words are words over the nine-letter pair alphabet.** -/
theorem card_segmentedAvailableWord_le {n m : ℕ} (seg : Fin (n + 1) → Fin m)
    (α : Fin m → PositiveWord CWBlock 1 → ℕ) :
    Fintype.card (SegmentedAvailableWord seg α) ≤ 9 ^ (n + 1) := by
  classical
  refine le_trans (Fintype.card_subtype_le _) ?_
  rw [card_positiveWord, card_pairAlphabet]

/-- **`dwz63BatchSize` is large enough.**  `9 ^ (n+1) ≤ (8^4) ^ (n+1) < 8 ^ (4*(n+1)+1)`. -/
theorem card_segmentedAvailableWord_lt_eight_pow {n m : ℕ} (seg : Fin (n + 1) → Fin m)
    (α : Fin m → PositiveWord CWBlock 1 → ℕ) :
    Fintype.card (SegmentedAvailableWord seg α) < 8 ^ dwz63BatchSize n := by
  refine lt_of_le_of_lt (card_segmentedAvailableWord_le seg α) ?_
  calc (9 : ℕ) ^ (n + 1) ≤ 4096 ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) _
    _ = 8 ^ (4 * (n + 1)) := by
        rw [show (4096 : ℕ) = 8 ^ 4 by norm_num, ← pow_mul]
    _ < 8 ^ dwz63BatchSize n := by
        refine Nat.pow_lt_pow_right (by norm_num) ?_
        unfold dwz63BatchSize
        omega

theorem dwz63BatchSize_pos (n : ℕ) : 0 < dwz63BatchSize n := by
  unfold dwz63BatchSize
  omega

/-! ## The packaged batching of the retained triples -/

section Dwz63Batch

variable (retained : Type w) [Fintype retained] {n : ℕ}

/-- **The section 6.3 batching**: consecutive blocks of `dwz63BatchSize n` retained triples. -/
noncomputable abbrev dwz63Batch (n : ℕ)
    (hq : 0 < Fintype.card retained / dwz63BatchSize n) :
    retained → Fin (Fintype.card retained / dwz63BatchSize n) :=
  blockBatch retained hq

variable {retained}

/-- `hbatch`, in the shape `dwz63_groupedStage_of_claim3` requires. -/
theorem dwz63Batch_surjective (hq : 0 < Fintype.card retained / dwz63BatchSize n) :
    Function.Surjective (dwz63Batch retained n hq) :=
  blockBatch_surjective (dwz63BatchSize_pos n) hq

/-- **`hbudget`, in the shape `dwz63_groupedStage_of_claim3` requires**, from the per-triple hole
bound `8 * |holes a| ≤ card(avail)` that image 59's hole budget delivers. -/
theorem dwz63_hbudget {m : ℕ} (seg : Fin (n + 1) → Fin m)
    (α : Fin m → PositiveWord CWBlock 1 → ℕ)
    (hq : 0 < Fintype.card retained / dwz63BatchSize n)
    (hA : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (holes : retained → Finset (SegmentedAvailableWord seg α))
    (hholes : ∀ a, 8 * (holes a).card ≤ Fintype.card (SegmentedAvailableWord seg α)) :
    ∀ b : Fin (Fintype.card retained / dwz63BatchSize n),
      Fintype.card (SegmentedAvailableWord seg α) *
          ∏ a : {a // dwz63Batch retained n hq a = b}, (holes a.1).card <
        Fintype.card (SegmentedAvailableWord seg α) ^
          Fintype.card {a // dwz63Batch retained n hq a = b} := fun b ↦
  mul_prod_lt_pow_of_eight_mul_le (ι := {a // dwz63Batch retained n hq a = b}) hA
    (fun a ↦ (holes a.1).card) (fun a ↦ hholes a.1)
    (card_segmentedAvailableWord_lt_eight_pow seg α)
    (card_le_blockBatch_fiber (dwz63BatchSize_pos n) hq b)

/-- **The copy-count loss**: the number of batches is the number of retained triples divided by a
factor linear in `n`.  `dwz63BatchSize n = 4 * (n + 1) + 1`, so this is the polynomial loss the
open-integration endpoint absorbs. -/
theorem card_le_two_mul_batchSize_mul_card_batches
    (hq : 0 < Fintype.card retained / dwz63BatchSize n) :
    Fintype.card retained ≤
      2 * dwz63BatchSize n *
        Fintype.card (Fin (Fintype.card retained / dwz63BatchSize n)) :=
  card_le_two_mul_card_blockBatch (dwz63BatchSize_pos n) hq

/-- The batching exists as soon as there are at least `dwz63BatchSize n` retained triples. -/
theorem dwz63Batch_index_pos (hcard : dwz63BatchSize n ≤ Fintype.card retained) :
    0 < Fintype.card retained / dwz63BatchSize n :=
  Nat.div_pos hcard (dwz63BatchSize_pos n)

end Dwz63Batch

end AlgebraicComplexity.Examples
