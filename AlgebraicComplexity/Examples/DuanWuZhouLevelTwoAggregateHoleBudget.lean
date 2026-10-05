/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleFractionRefutation
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizedHashing

set_option autoImplicit false

/-!
# The Hole-Lemma budget from an *aggregate* hole bound, by the second retention pass

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoHoleFractionRefutation.lean`
shows that the residual `Dwz63HoleFractionInputs` cannot be discharged on any nonempty retained
family, so the reduction of `hbudget` has to change shape.  This module gives the shape that
works, and proves everything except one named inequality.

## Why the per-copy bound is the wrong target

`[DuanWuZhou2022]`'s `claim:hole_frac_low` (`global_value.tex:250`) is a statement about a
**random hash seed**: for a fixed retained triple and a fixed useful small block, the *probability*
of being a hole is at most `1/8`.  The paper never turns that into a per-copy deterministic bound.
It sums instead: `fracnonhole ≥ 7/8` enters only through
`m' = ⌊(∑_{(X_I,Y_J,Z_K)} η_{IJK}) / (nℓ + 2)⌋` and the expectation `E[m']`
(`global_value.tex:270-284`), so what the argument really produces is a bound on the **total**
hole mass over the retained family, at one seed chosen by the probabilistic method.

`Dwz63AggregateHoleFraction` below is exactly that total, in exact integer form:

`16 · ∑_{a ∈ retained} |holes a| ≤ #retained · |avail|`.

It is the average hole fraction being at most `1/16`, i.e. `claim:hole_frac_low` with
`M₀ = 16 · max(N_triple/N_X, N_α · p_comp / N_Z)` in place of the paper's `8 · max(...)`.  Doubling
the modulus halves the retained count, a constant factor, which the endpoint's `loss` absorbs.

## The second retention pass, formalized

From the aggregate bound alone, Markov gives a retained subset of at least **half** the family on
which the per-copy `1/8` bound holds:

* `dwz63GoodCopies holes` — the copies with `8 |holes a| ≤ |avail|`;
* `card_le_two_mul_card_dwz63GoodCopies` — `#retained ≤ 2 · #good`.

This is `[DuanWuZhou2022]`'s "discard the copies whose hole fraction is too large" made finite and
exact, and it is the step the hash cannot replace: a seed controlling *every* retained triple at
once is a different (and stronger) statement.

The discarded copies then do **not** have to leave the retained family, which matters because
`Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s stage fixes the retained family in its binder.
Two lemmas do that:

* `dwz63_holeBudget_of_goodSubset` — the copy budget when only a subset of the copies is under
  control.  A bad copy contributes `η = 0` rather than `η = 7/8` to
  `AsymmetricGlobal.holeBudget_of_etaSum`, and its hole count is bounded by `|avail|` for free;
  so `8(L+1) ≤ 7 · #good` already suffices, with the *same* constant as the all-good
  `holeBudget_of_eight_mul_card_le`.
* `dwz63GoodBatch` — a batching that puts `k` good copies in every batch and dumps all the bad
  copies into batch `0`.  It is `uniformBatch` run on the good subset alone, so
  `uniformBatch_surjective` and `le_card_uniformBatch_fiber` are reused verbatim.

`dwz63_hbudget_of_aggregateHoleFraction_of_card` is the assembled statement, in the exact binder
`dwz63_localizedGroupedStage_of_segmentedRepair` and
`dwz63_localizedGroupedSymSixStage_of_segmentedRepair` carry `hbudget`, with `hbatch` supplied by
`dwz63GoodBatch_surjective`.  Against `Examples/DuanWuZhouLevelTwoPlainUniformBatch.lean`'s
all-good batching the only change is `batches = #retained / (2k)` instead of `#retained / k`: the
second retention pass costs a factor `2`, nothing more.

## The guard

`card_eq_zero_of_dwz63AggregateHoleFraction` records that the aggregate form is **not** a way
around the refutation: instantiated back at `dwz63HoleSet` with a single binary compatibility
relation it is refutable for the same reason.  The hole family has to be genuinely a family —
`holes : retained → Finset (SegmentedAvailableWord seg α)`, one hole set per copy in that copy's
own coordinates — which is how the stage carries it and how `[DuanWuZhou2022]` mean it.

## What is left open

`Dwz63AggregateHoleFraction` itself, and only it.  Its proof in `[DuanWuZhou2022]` is
`claim:hole_frac_low` (`global_value.tex:250-268`): a union bound over the competitor triples
`I' ≠ I` matchable to `K`, each contributing the conditional collision mass
`Pr[h_X(I') = h_Z(K) | h_X(I) = h_Z(K)] = 1/M` of `lemma:hash_independence`, followed by the
identity `∑_{I'} 1[Z_K̂ compatible with X_{I'}] = (N_α/N_Z) · p_comp` and the modulus condition
`M ≥ 16 · N_α · p_comp / N_Z`.  The tree already holds both halves as *separate* facts —
`Combinatorics/HashingConditionalIndependence.lean`'s `uniformSeed_inCommonTriple_sharedZ_mass`
(the per-pair `1/M`) and `Analysis/CompatibilityRate.lean`'s
`card_matchableCompatible_eq_mul_compatibleFraction` together with `holeFraction_le` (the
competitor count and the modulus arithmetic) — and `CompatibilityRate`'s own "Non-goals"
paragraph records that joining them is assembly work not done there.  Nothing in this module
assumes it.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`) and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v w

/-! ## The copy budget when only part of the batch is under control -/

section GoodSubset

variable {A : Type u} [Fintype A] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **The Hole-Lemma budget from a good subset of the copies.**

`AsymmetricGlobal.holeBudget_of_eight_mul_card_le` asks the `1/8` bound of every copy.  Here only
the copies in `G` are controlled; the others contribute the trivial survival fraction `η = 0`, and
their hole count is at most `|avail|` because a hole set is a `Finset` of the available words.
The threshold `8 (L + 1) ≤ 7 · #G` is `[DuanWuZhou2022]`'s own `∑_t η_t ≥ Nℓ + 1`. -/
theorem dwz63_holeBudget_of_goodSubset (holes : ι → Finset A) (G : Finset ι) (L : ℕ)
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
  · have hsum : (∑ _t : ι, (if _t ∈ G then (7 : ℝ) / 8 else 0)) = (G.card : ℝ) * (7 / 8) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    have hcast : (8 : ℝ) * ((L : ℝ) + 1) ≤ 7 * (G.card : ℝ) := by
      have h : ((8 * (L + 1) : ℕ) : ℝ) ≤ ((7 * G.card : ℕ) : ℝ) := by exact_mod_cast hcopies
      push_cast at h
      linarith
    linarith

/-- **The same budget on one batch.**  The good copies of the batch are the ones of `G` that
`batch` sends to `b`. -/
theorem dwz63_holeBudget_fiber_of_goodSubset {β : Type w} [DecidableEq β]
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
  refine dwz63_holeBudget_of_goodSubset (fun a : {a : ι // batch a = b} ↦ holes a.1)
    (Finset.univ.filter fun a : {a : ι // batch a = b} ↦ (a : ι) ∈ G) L hpos hbound ?_ ?_
  · intro t ht
    exact hgood t.1 (Finset.mem_filter.mp ht).2
  · rw [← hcardEq]
    exact hcopies

end GoodSubset

/-! ## The second retention pass: Markov on the hole counts -/

section Markov

variable {A : Type u} [Fintype A] {ι : Type v} [Fintype ι]

/-- **The copies that survive the second retention pass**: those whose hole fraction is at most
`1/8` (`[DuanWuZhou2022]`, `claim:hole_frac_low`). -/
def dwz63GoodCopies (holes : ι → Finset A) : Finset ι :=
  Finset.univ.filter fun t ↦ 8 * (holes t).card ≤ Fintype.card A

@[simp] theorem mem_dwz63GoodCopies {holes : ι → Finset A} {t : ι} :
    t ∈ dwz63GoodCopies holes ↔ 8 * (holes t).card ≤ Fintype.card A := by
  simp [dwz63GoodCopies]

/-- **Markov: at least half the copies survive.**

If the *average* hole fraction over the whole retained family is at most `1/16`, then at least
half of the copies have hole fraction at most `1/8`.  This is the entire content of
`[DuanWuZhou2022]`'s second retention pass; the factor `2` is the only loss. -/
theorem card_le_two_mul_card_dwz63GoodCopies [DecidableEq ι] (holes : ι → Finset A)
    (hpos : 0 < Fintype.card A)
    (haggregate : 16 * ∑ t, (holes t).card ≤ Fintype.card ι * Fintype.card A) :
    Fintype.card ι ≤ 2 * (dwz63GoodCopies holes).card := by
  classical
  set bad : Finset ι := Finset.univ \ dwz63GoodCopies holes with hbaddef
  have hmembad : ∀ t ∈ bad, Fintype.card A ≤ 8 * (holes t).card := by
    intro t ht
    rw [hbaddef, Finset.mem_sdiff] at ht
    have hnot : ¬ (8 * (holes t).card ≤ Fintype.card A) := fun h ↦
      ht.2 (mem_dwz63GoodCopies.mpr h)
    omega
  have hgle : (dwz63GoodCopies holes).card ≤ Fintype.card ι :=
    Finset.card_le_univ _
  have hsplit : bad.card = Fintype.card ι - (dwz63GoodCopies holes).card := by
    rw [hbaddef, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  have hstep : bad.card * Fintype.card A ≤ 8 * ∑ t ∈ bad, (holes t).card := by
    calc bad.card * Fintype.card A = ∑ _t ∈ bad, Fintype.card A := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ t ∈ bad, 8 * (holes t).card := Finset.sum_le_sum hmembad
      _ = 8 * ∑ t ∈ bad, (holes t).card := by rw [Finset.mul_sum]
  have hsub : ∑ t ∈ bad, (holes t).card ≤ ∑ t, (holes t).card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ bad)
  have hkey : 2 * bad.card * Fintype.card A ≤ Fintype.card ι * Fintype.card A := by
    calc 2 * bad.card * Fintype.card A = 2 * (bad.card * Fintype.card A) := by ring
      _ ≤ 2 * (8 * ∑ t ∈ bad, (holes t).card) := by omega
      _ = 16 * ∑ t ∈ bad, (holes t).card := by ring
      _ ≤ 16 * ∑ t, (holes t).card := by omega
      _ ≤ Fintype.card ι * Fintype.card A := haggregate
  have h2b : 2 * bad.card ≤ Fintype.card ι := Nat.le_of_mul_le_mul_right hkey hpos
  omega

end Markov

/-! ## A batching that fills every batch with good copies -/

section GoodBatch

variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **The batching of the second retention pass.**  `uniformBatch` run on the good subset alone;
every copy outside `G` is dumped into batch `0`, where it is harmless because
`dwz63_holeBudget_of_goodSubset` never uses it. -/
noncomputable def dwz63GoodBatch (G : Finset ι) (k : ℕ) {batches : ℕ} (hbatches : 0 < batches) :
    ι → Fin batches := fun a ↦
  if h : a ∈ G then uniformBatch (ι := {x // x ∈ G}) k hbatches ⟨a, h⟩ else ⟨0, hbatches⟩

omit [Fintype ι] in
theorem dwz63GoodBatch_of_mem {G : Finset ι} {k batches : ℕ} (hbatches : 0 < batches)
    {a : ι} (ha : a ∈ G) :
    dwz63GoodBatch G k hbatches a = uniformBatch (ι := {x // x ∈ G}) k hbatches ⟨a, ha⟩ := by
  unfold dwz63GoodBatch
  exact dif_pos ha

omit [Fintype ι] in
/-- **`hbatch` for the good batching.** -/
theorem dwz63GoodBatch_surjective {G : Finset ι} {k batches : ℕ} (hk : 0 < k)
    (hbatches : 0 < batches) (hfit : batches * k ≤ G.card) :
    Function.Surjective (dwz63GoodBatch G k hbatches) := by
  intro b
  have hcard : batches * k ≤ Fintype.card {x // x ∈ G} := by
    rw [Fintype.card_coe]
    exact hfit
  obtain ⟨i, hi⟩ := uniformBatch_surjective (ι := {x // x ∈ G}) hk hbatches hcard b
  refine ⟨i.1, ?_⟩
  rw [dwz63GoodBatch_of_mem hbatches i.2]
  exact hi

omit [Fintype ι] in
/-- **Every batch holds at least `k` good copies.** -/
theorem le_card_dwz63GoodBatch_fiber {G : Finset ι} {k batches : ℕ} (hk : 0 < k)
    (hbatches : 0 < batches) (hfit : batches * k ≤ G.card) (b : Fin batches) :
    k ≤ (G.filter fun a ↦ dwz63GoodBatch G k hbatches a = b).card := by
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
    rw [dwz63GoodBatch_of_mem hbatches i.1.2]
    exact i.2
  · intro i _ j _ h
    exact Subtype.ext (Subtype.ext h)

end GoodBatch

/-! ## The residual, and `hbudget` from it -/

section Aggregate

variable {I : Type u} [Fintype I] [DecidableEq I] {n m : ℕ}
variable {τ : Type v} [Fintype τ] [DecidableEq τ]

/-- **The one statement left open.**

`[DuanWuZhou2022]`'s `claim:hole_frac_low` summed over the retained family: the average hole
fraction of the broken copies is at most `1/16`.  See the module docstring for the paper's proof
and for the two committed halves of it. -/
def Dwz63AggregateHoleFraction (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ) (holes : retained → Finset (SegmentedAvailableWord seg α)) : Prop :=
  16 * ∑ a : retained, (holes a).card ≤
    retained.card * Fintype.card (SegmentedAvailableWord seg α)

omit [Fintype τ] in
/-- **`hbudget` from the good subset**, in the binder
`dwz63_localizedGroupedStage_of_segmentedRepair` carries it. -/
theorem dwz63_hbudget_of_aggregateHoleFraction
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (retained : Finset τ)
    (holes : retained → Finset (SegmentedAvailableWord seg α)) (L : ℕ)
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (hbound : Fintype.card (SegmentedAvailableWord seg α) ≤ 2 ^ L)
    {k batches : ℕ} (hk : 0 < k) (hbatches : 0 < batches)
    (hcopies : 8 * (L + 1) ≤ 7 * k)
    (hfit : batches * k ≤ (dwz63GoodCopies holes).card) :
    ∀ b : Fin batches,
      Fintype.card (SegmentedAvailableWord seg α) *
          ∏ a : {a : retained // dwz63GoodBatch (dwz63GoodCopies holes) k hbatches a = b},
            (holes a.1).card <
        Fintype.card (SegmentedAvailableWord seg α) ^
          Fintype.card {a : retained //
            dwz63GoodBatch (dwz63GoodCopies holes) k hbatches a = b} := by
  intro b
  refine dwz63_holeBudget_fiber_of_goodSubset holes (dwz63GoodCopies holes) L
    (dwz63GoodBatch (dwz63GoodCopies holes) k hbatches) b hpos hbound ?_ ?_
  · intro t ht
    exact mem_dwz63GoodCopies.mp ht
  · have hfibre := le_card_dwz63GoodBatch_fiber hk hbatches hfit b
    omega

omit [Fintype τ] in
/-- **`hbatch` from the residual alone.**  The Markov step of the second retention pass, in the
shape `dwz63_localizedGroupedStage_of_segmentedRepair` carries `hbatch`. -/
theorem dwz63GoodBatch_surjective_of_aggregateHoleFraction
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (retained : Finset τ)
    (holes : retained → Finset (SegmentedAvailableWord seg α))
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (haggregate : Dwz63AggregateHoleFraction seg α retained holes)
    {k batches : ℕ} (hk : 0 < k) (hbatches : 0 < batches)
    (hfit : 2 * (batches * k) ≤ retained.card) :
    Function.Surjective (dwz63GoodBatch (dwz63GoodCopies holes) k hbatches) := by
  refine dwz63GoodBatch_surjective hk hbatches ?_
  have haggr : 16 * ∑ a : retained, (holes a).card ≤
      Fintype.card retained * Fintype.card (SegmentedAvailableWord seg α) := by
    rw [Fintype.card_coe]
    exact haggregate
  have hmarkov := card_le_two_mul_card_dwz63GoodCopies holes hpos haggr
  rw [Fintype.card_coe] at hmarkov
  omega

omit [Fintype τ] in
/-- **`hbudget` from the residual alone.**

The assembled second retention pass: the aggregate hole bound gives, by Markov, a good subset of
at least half the retained family, and the good batching then fills every batch with `k` good
copies.  The copy count is `batches = #retained / (2k)`, i.e. exactly a factor `2` below the
all-good batching of `Examples/DuanWuZhouLevelTwoPlainUniformBatch.lean`. -/
theorem dwz63_hbudget_of_aggregateHoleFraction_of_card
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (retained : Finset τ)
    (holes : retained → Finset (SegmentedAvailableWord seg α)) (L : ℕ)
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (hbound : Fintype.card (SegmentedAvailableWord seg α) ≤ 2 ^ L)
    (haggregate : Dwz63AggregateHoleFraction seg α retained holes)
    {k batches : ℕ} (hk : 0 < k) (hbatches : 0 < batches)
    (hcopies : 8 * (L + 1) ≤ 7 * k)
    (hfit : 2 * (batches * k) ≤ retained.card) :
    ∀ b : Fin batches,
      Fintype.card (SegmentedAvailableWord seg α) *
          ∏ a : {a : retained // dwz63GoodBatch (dwz63GoodCopies holes) k hbatches a = b},
            (holes a.1).card <
        Fintype.card (SegmentedAvailableWord seg α) ^
          Fintype.card {a : retained //
            dwz63GoodBatch (dwz63GoodCopies holes) k hbatches a = b} := by
  refine dwz63_hbudget_of_aggregateHoleFraction seg α retained holes L hpos hbound hk hbatches
    hcopies ?_
  have haggr : 16 * ∑ a : retained, (holes a).card ≤
      Fintype.card retained * Fintype.card (SegmentedAvailableWord seg α) := by
    rw [Fintype.card_coe]
    exact haggregate
  have hmarkov := card_le_two_mul_card_dwz63GoodCopies holes hpos haggr
  rw [Fintype.card_coe] at hmarkov
  omega

/-! ## The guard: aggregating the binary shape does not rescue it -/

/-- **The aggregate form is refutable at `dwz63HoleSet` too.**

Instantiated back at the binary hole set of
`Examples/DuanWuZhouLevelTwoPlainHoleBudget.lean` with two retained triples and rule (ii)'s
density, `Dwz63AggregateHoleFraction` forces `|avail| = 0`, exactly as the per-copy residual does
(`Examples/DuanWuZhouLevelTwoHoleFractionRefutation.lean`).  So the aggregate statement earns its
keep only because the hole family is carried per copy, as the stage carries it. -/
theorem card_eq_zero_of_dwz63AggregateHoleFraction
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (retained : Finset τ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop)
    (hrefines : ∀ (w : SegmentedAvailableWord seg α) (b : τ), usefulFor w b → compatibleWith w b)
    (hcard : 1 < retained.card)
    (huseless : ∀ b : τ, 16 * (dwz63UselessZWords seg α usefulFor b).card ≤
      Fintype.card (SegmentedAvailableWord seg α))
    (haggregate : Dwz63AggregateHoleFraction seg α retained
      fun a : retained ↦ dwz63HoleSet seg α retained compatibleWith usefulFor a.1) :
    Fintype.card (SegmentedAvailableWord seg α) = 0 := by
  classical
  have hpt : ∀ a : retained,
      15 * Fintype.card (SegmentedAvailableWord seg α) ≤
        16 * (dwz63HoleSet seg α retained compatibleWith usefulFor a.1).card := by
    intro a
    have hcarderase : 0 < (retained.erase a.1).card := by
      rw [Finset.card_erase_of_mem a.2]
      omega
    obtain ⟨b, hbmem⟩ := Finset.card_pos.mp hcarderase
    exact fifteen_mul_card_le_sixteen_mul_card_dwz63HoleSet seg α retained
      compatibleWith usefulFor hrefines (Finset.mem_of_mem_erase hbmem)
      (Finset.ne_of_mem_erase hbmem) (huseless b)
  have hsum : Fintype.card retained * (15 * Fintype.card (SegmentedAvailableWord seg α)) ≤
      ∑ a : retained, 16 * (dwz63HoleSet seg α retained compatibleWith usefulFor a.1).card := by
    calc Fintype.card retained * (15 * Fintype.card (SegmentedAvailableWord seg α))
        = ∑ _a : retained, 15 * Fintype.card (SegmentedAvailableWord seg α) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ a : retained, 16 * (dwz63HoleSet seg α retained compatibleWith usefulFor a.1).card :=
          Finset.sum_le_sum fun a _ ↦ hpt a
  rw [← Finset.mul_sum, Fintype.card_coe] at hsum
  have hkey : 15 * (retained.card * Fintype.card (SegmentedAvailableWord seg α)) ≤
      retained.card * Fintype.card (SegmentedAvailableWord seg α) := by
    calc 15 * (retained.card * Fintype.card (SegmentedAvailableWord seg α))
        = retained.card * (15 * Fintype.card (SegmentedAvailableWord seg α)) := by ring
      _ ≤ 16 * ∑ a : retained,
            (dwz63HoleSet seg α retained compatibleWith usefulFor a.1).card := hsum
      _ ≤ retained.card * Fintype.card (SegmentedAvailableWord seg α) := haggregate
  have hzero : retained.card * Fintype.card (SegmentedAvailableWord seg α) = 0 := by omega
  rcases Nat.mul_eq_zero.mp hzero with h | h
  · omega
  · exact h

end Aggregate

end AlgebraicComplexity.Examples
