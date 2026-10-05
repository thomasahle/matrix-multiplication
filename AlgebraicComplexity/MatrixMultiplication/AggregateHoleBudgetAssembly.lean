/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AggregateHoleBudget

set_option autoImplicit false

/-!
# The second retention pass, assembled

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `Combinatorics/AggregateHoleFraction.lean`
supplies the Markov step and `MatrixMultiplication/AggregateHoleBudget.lean` the budget and the
batching; this module puts the three together into the two statements a hole-repair stage actually
carries in its binder, `hbudget` and `hbatch`:

* `AsymmetricGlobal.holeBudget_goodBatch_fiber` — every fibre of `goodBatch (goodCopies holes) k`
  satisfies the Hole-Lemma budget, given only `8 (L + 1) ≤ 7 k` and
  `batches · k ≤ #goodCopies`.
  This is `holeBudget_fiber_of_goodSubset` with `G := goodCopies holes`, where `mem_goodCopies`
  discharges the per-copy hypothesis and `le_card_goodBatch_fiber` the per-batch count.
* `goodBatch_surjective_of_aggregateHoleFraction` and
  `AsymmetricGlobal.holeBudget_goodBatch_fiber_of_aggregateHoleFraction` — the same two facts from
  the *aggregate* bound alone.  Markov turns `AggregateHoleFraction holes` into
  `#retained ≤ 2 · #goodCopies`, so a batching with `2 (batches · k) ≤ #retained` fits
  inside the
  good subset: the copy count is `batches = #retained / (2k)`, i.e. exactly a factor `2` below an
  all-good batching.  That factor is the entire cost of the second retention pass.

Nothing here is specific to a paper: the alphabet `A`, the copy index `ι` and the retained family
`retained : Finset τ` are arbitrary finite data.  The `[DuanWuZhou2022]` level-two instances
`dwz63_hbudget_of_aggregateHoleFraction`, `dwz63GoodBatch_surjective_of_aggregateHoleFraction` and
`dwz63_hbudget_of_aggregateHoleFraction_of_card`
(`Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean:310, 336, 360`) are the specializations at
`A := SegmentedAvailableWord seg α` and `ι := ↥retained`, each a single application.

The split of the aggregate statements over a `Finset` rather than over a bare `Fintype` index is
deliberate: a retained family is carried as a `Finset` by every stage binder in the tree, and
stating `hfit` against `retained.card` keeps `Fintype.card_coe` out of the client.  A client whose
copies are not a `Finset` uses `holeBudget_goodBatch_fiber` together with
`card_le_two_mul_card_goodCopies` directly.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §5 (`hole_lemma.tex`) and §6.2 (`global_value.tex`)
(`[DuanWuZhou2022]`).
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v

section Fibre

variable {A : Type u} [Fintype A] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **`hbudget` from a good subset that is large enough to batch.**

`AsymmetricGlobal.holeBudget_fiber_of_goodSubset` at `G := goodCopies holes`: the per-copy
hypothesis is `mem_goodCopies`, and `le_card_goodBatch_fiber` puts `k` good copies in every batch,
which is `8 (L + 1) ≤ 7 k` away from the threshold. -/
theorem AsymmetricGlobal.holeBudget_goodBatch_fiber (holes : ι → Finset A) (L : ℕ)
    (hpos : 0 < Fintype.card A) (hbound : Fintype.card A ≤ 2 ^ L)
    {k batches : ℕ} (hk : 0 < k) (hbatches : 0 < batches)
    (hcopies : 8 * (L + 1) ≤ 7 * k)
    (hfit : batches * k ≤ (goodCopies holes).card) :
    ∀ b : Fin batches,
      Fintype.card A *
          ∏ a : {a : ι // goodBatch (goodCopies holes) k hbatches a = b}, (holes a.1).card <
        Fintype.card A ^
          Fintype.card {a : ι // goodBatch (goodCopies holes) k hbatches a = b} := by
  intro b
  refine AsymmetricGlobal.holeBudget_fiber_of_goodSubset holes (goodCopies holes) L
    (goodBatch (goodCopies holes) k hbatches) b hpos hbound ?_ ?_
  · intro t ht
    exact mem_goodCopies.mp ht
  · have hfibre := le_card_goodBatch_fiber hk hbatches hfit b
    omega

end Fibre

section Aggregate

variable {A : Type u} [Fintype A] {τ : Type v} [DecidableEq τ]

/-- **`hbatch` from the aggregate bound alone.**

Markov halves the retained family, so a batching sized for `2 (batches · k) ≤ #retained` still
fits inside `goodCopies holes`. -/
theorem goodBatch_surjective_of_aggregateHoleFraction (retained : Finset τ)
    (holes : retained → Finset A) (hpos : 0 < Fintype.card A)
    (haggregate : AggregateHoleFraction holes)
    {k batches : ℕ} (hk : 0 < k) (hbatches : 0 < batches)
    (hfit : 2 * (batches * k) ≤ retained.card) :
    Function.Surjective (goodBatch (goodCopies holes) k hbatches) := by
  refine goodBatch_surjective hk hbatches ?_
  have hmarkov := card_le_two_mul_card_goodCopies_of_aggregateHoleFraction retained holes hpos
    haggregate
  omega

/-- **`hbudget` from the aggregate bound alone.**

The assembled second retention pass: the aggregate hole bound gives, by Markov, a good subset of
at least half the retained family, and the good batching then fills every batch with `k` good
copies.  The copy count is `batches = #retained / (2k)`. -/
theorem AsymmetricGlobal.holeBudget_goodBatch_fiber_of_aggregateHoleFraction (retained : Finset τ)
    (holes : retained → Finset A) (L : ℕ)
    (hpos : 0 < Fintype.card A) (hbound : Fintype.card A ≤ 2 ^ L)
    (haggregate : AggregateHoleFraction holes)
    {k batches : ℕ} (hk : 0 < k) (hbatches : 0 < batches)
    (hcopies : 8 * (L + 1) ≤ 7 * k)
    (hfit : 2 * (batches * k) ≤ retained.card) :
    ∀ b : Fin batches,
      Fintype.card A *
          ∏ a : {a : retained // goodBatch (goodCopies holes) k hbatches a = b},
            (holes a.1).card <
        Fintype.card A ^
          Fintype.card {a : retained // goodBatch (goodCopies holes) k hbatches a = b} := by
  refine AsymmetricGlobal.holeBudget_goodBatch_fiber holes L hpos hbound hk hbatches hcopies ?_
  have hmarkov := card_le_two_mul_card_goodCopies_of_aggregateHoleFraction retained holes hpos
    haggregate
  omega

end Aggregate

end AlgebraicComplexity
