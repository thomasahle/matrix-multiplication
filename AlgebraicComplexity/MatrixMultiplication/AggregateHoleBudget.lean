/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.AggregateHoleFraction
import AlgebraicComplexity.MatrixMultiplication.AsymmetricGlobalBudget
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizedHashing

set_option autoImplicit false

/-!
# The Hole-Lemma budget and batching when only a subset of the copies is controlled

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `Combinatorics/AggregateHoleFraction.lean`
turns an *aggregate* hole bound into a subset `goodCopies holes` of at least half the copies on
which the per-copy `1/8` bound holds.  This module supplies the two consequences of such a subset
that a hole-repair client actually consumes, and neither mentions a particular alphabet, partition
or hashing seed:

* `AsymmetricGlobal.holeBudget_of_goodSubset` — the copy budget when only the copies of a subset
  `G` are under control.  A bad copy contributes the trivial survival fraction `η = 0` rather than
  `η = 7/8` to `AsymmetricGlobal.holeBudget_of_etaSum`, and its hole count is bounded by `|A|` for
  free because a hole set is a `Finset` of the alphabet; so `8 (L + 1) ≤ 7 · #G` already
  suffices,
  with the *same* constant as the all-good `AsymmetricGlobal.holeBudget_of_eight_mul_card_le`.
  `holeBudget_fiber_of_goodSubset` is the same statement on one batch.
* `goodBatch` — a batching that puts `k` copies of `G` in every batch and dumps every copy outside
  `G` into batch `0`, where it is harmless because `holeBudget_of_goodSubset` never uses it.  It is
  `uniformBatch` run on `G` alone, so `uniformBatch_surjective` and `le_card_uniformBatch_fiber`
  are reused verbatim and the only cost of the retention pass is `batches = #G / k` instead of
  `#ι / k`.

Both groups are stated for an arbitrary finite alphabet `A` and an arbitrary finite copy index
`ι`.  The `[duan2023faster]` level-two instances
(`Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean`)
are the specializations at `A := SegmentedAvailableWord seg α` and `ι := ↥retained`.

The import of `Combinatorics/AggregateHoleFraction.lean` is deliberate rather than used: the
retention pass is one argument split across two layers only because
`AsymmetricGlobal.holeBudget_of_etaSum` and `uniformBatch` are layer-3 declarations, and a client
that needs the budget always needs `goodCopies` to produce the subset `G`.  Importing this module
therefore supplies the whole pass.  The Mathlib-only lower half stays separately importable for
clients that need only the Markov step.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §5 (`hole_lemma.tex`) and §6.2 (`global_value.tex`)
(`[duan2023faster]`).

Exact source lines: `papers/sources/2210.10173/hole_lemma.tex:1-168` (§5),
`papers/sources/2210.10173/global_value.tex:124-331` (§6.2).
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

/-! ## The copy budget when only part of the batch is under control -/

namespace AsymmetricGlobal

section GoodSubset

variable {A : Type u} [Fintype A] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **The Hole-Lemma budget from a good subset of the copies.**

`AsymmetricGlobal.holeBudget_of_eight_mul_card_le` asks the `1/8` bound of every copy.  Here only
the copies in `G` are controlled; the others contribute the trivial survival fraction `η = 0`, and
their hole count is at most `|A|` because a hole set is a `Finset` of the alphabet.  The threshold
`8 (L + 1) ≤ 7 · #G` is `[duan2023faster]`'s own `∑_t η_t ≥ Nℓ + 1`. -/
theorem holeBudget_of_goodSubset (holes : ι → Finset A) (G : Finset ι) (L : ℕ)
    (hpos : 0 < Fintype.card A) (hbound : Fintype.card A ≤ 2 ^ L)
    (hgood : ∀ t ∈ G, 8 * (holes t).card ≤ Fintype.card A)
    (hcopies : 8 * (L + 1) ≤ 7 * G.card) :
    Fintype.card A * ∏ t, (holes t).card < Fintype.card A ^ Fintype.card ι := by
  refine AsymmetricGlobal.holeBudget_of_etaSum holes
    (fun t ↦ if t ∈ G then (7 : ℝ) / 8 else 0) L hpos hbound ?_ ?_
  · intro t
    by_cases ht : t ∈ G
    · have h8 : (8 : ℝ) * ((holes t).card : ℝ) ≤ (Fintype.card A : ℝ) := by
        exact_mod_cast hgood t ht
      have heq : (1 : ℝ) - (if t ∈ G then (7 : ℝ) / 8 else 0) = 1 / 8 := by
        simp only [ht, if_true]
        norm_num
      rw [heq]
      linarith
    · have hle : ((holes t).card : ℝ) ≤ (Fintype.card A : ℝ) := by
        exact_mod_cast Finset.card_le_univ (holes t)
      have heq : (1 : ℝ) - (if t ∈ G then (7 : ℝ) / 8 else 0) = 1 := by
        simp only [ht, if_false]
        norm_num
      rw [heq, one_mul]
      exact hle
  · have hsum : (∑ _t : ι, (if _t ∈ G then (7 : ℝ) / 8 else 0)) = (G.card : ℝ) * (7 / 8)
      := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    have hcast : (8 : ℝ) * ((L : ℝ) + 1) ≤ 7 * (G.card : ℝ) := by
      have h : ((8 * (L + 1) : ℕ) : ℝ) ≤ ((7 * G.card : ℕ) : ℝ) := by exact_mod_cast
        hcopies
      push_cast at h
      linarith
    linarith

/-- **The same budget on one batch.**  The good copies of the batch are the ones of `G` that
`batch` sends to `b`. -/
theorem holeBudget_fiber_of_goodSubset {β : Type w} [DecidableEq β]
    (holes : ι → Finset A) (G : Finset ι) (L : ℕ) (batch : ι → β) (b : β)
    (hpos : 0 < Fintype.card A) (hbound : Fintype.card A ≤ 2 ^ L)
    (hgood : ∀ t ∈ G, 8 * (holes t).card ≤ Fintype.card A)
    (hcopies : 8 * (L + 1) ≤ 7 * (G.filter fun a ↦ batch a = b).card) :
    Fintype.card A * ∏ a : {a : ι // batch a = b}, (holes a.1).card <
      Fintype.card A ^ Fintype.card {a : ι // batch a = b} := by
  have hcardEq : (G.filter fun a ↦ batch a = b).card =
      (Finset.univ.filter fun a : {a : ι // batch a = b} ↦ (a : ι) ∈ G).card := by
    rw [← Finset.card_image_of_injective
      (Finset.univ.filter fun a : {a : ι // batch a = b} ↦ (a : ι) ∈ G) Subtype.val_injective]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨hxG, hxb⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_image.mpr
        ⟨⟨x, hxb⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxG⟩, rfl⟩
    · intro hx
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨hax ▸ (Finset.mem_filter.mp ha).2, hax ▸ a.2⟩
  refine holeBudget_of_goodSubset (fun a : {a : ι // batch a = b} ↦ holes a.1)
    (Finset.univ.filter fun a : {a : ι // batch a = b} ↦ (a : ι) ∈ G) L hpos hbound ?_ ?_
  · intro t ht
    exact hgood t.1 (Finset.mem_filter.mp ht).2
  · rw [← hcardEq]
    exact hcopies

end GoodSubset

end AsymmetricGlobal

/-! ## A batching that fills every batch from a controlled subset -/

section GoodBatch

variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **The batching of the second retention pass.**  `uniformBatch` run on the subset `G` alone;
every copy outside `G` is dumped into batch `0`, where it is harmless because
`AsymmetricGlobal.holeBudget_of_goodSubset` never uses it. -/
noncomputable def goodBatch (G : Finset ι) (k : ℕ) {batches : ℕ} (hbatches : 0 < batches) :
    ι → Fin batches := fun a ↦
  if h : a ∈ G then uniformBatch (ι := {x // x ∈ G}) k hbatches ⟨a, h⟩ else
    ⟨0, hbatches⟩

omit [Fintype ι] in
theorem goodBatch_of_mem {G : Finset ι} {k batches : ℕ} (hbatches : 0 < batches)
    {a : ι} (ha : a ∈ G) :
    goodBatch G k hbatches a = uniformBatch (ι := {x // x ∈ G}) k hbatches ⟨a, ha⟩ := by
  unfold goodBatch
  exact dif_pos ha

omit [Fintype ι] in
/-- **`hbatch` for the good batching**: every batch is hit once `batches · k` fits inside `G`. -/
theorem goodBatch_surjective {G : Finset ι} {k batches : ℕ} (hk : 0 < k)
    (hbatches : 0 < batches) (hfit : batches * k ≤ G.card) :
    Function.Surjective (goodBatch G k hbatches) := by
  intro b
  have hcard : batches * k ≤ Fintype.card {x // x ∈ G} := by
    rw [Fintype.card_coe]
    exact hfit
  obtain ⟨i, hi⟩ := uniformBatch_surjective (ι := {x // x ∈ G}) hk hbatches hcard b
  refine ⟨i.1, ?_⟩
  rw [goodBatch_of_mem hbatches i.2]
  exact hi

omit [Fintype ι] in
/-- **Every batch holds at least `k` copies of `G`.** -/
theorem le_card_goodBatch_fiber {G : Finset ι} {k batches : ℕ} (hk : 0 < k)
    (hbatches : 0 < batches) (hfit : batches * k ≤ G.card) (b : Fin batches) :
    k ≤ (G.filter fun a ↦ goodBatch G k hbatches a = b).card := by
  classical
  have hcard : batches * k ≤ Fintype.card {x // x ∈ G} := by
    rw [Fintype.card_coe]
    exact hfit
  have hbase := le_card_uniformBatch_fiber (ι := {x // x ∈ G}) hk hbatches hcard b
  refine hbase.trans ?_
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun i ↦ (i.1 : ι)) ?_ ?_
  · intro i _
    refine Finset.mem_filter.mpr ⟨i.1.2, ?_⟩
    rw [goodBatch_of_mem hbatches i.1.2]
    exact i.2
  · intro i _ j _ h
    exact Subtype.ext (Subtype.ext h)

end GoodBatch

end AlgebraicComplexity
