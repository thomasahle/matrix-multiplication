/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedHoleMass
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAggregateHoleBudget
import AlgebraicComplexity.Combinatorics.HashingIsolationIncidenceAveraging
import AlgebraicComplexity.Combinatorics.SharedLegSeedHoleMass

set_option autoImplicit false

/-!
# One seed that is good for the count *and* for the holes

Layer 4 (`AlgebraicComplexity/Examples/`).  `Combinatorics/MarkedTwoLegHashingExtraction.lean`'s
`exists_seed_many_markedXYIsolatedTargets_of_modulus` chooses a seed by maximizing the isolated
incidence reward; it says nothing about the `Z` side.
`Examples/DuanWuZhouLevelTwoSeedHoleMass.lean` bounds the seed-summed hole mass but chooses no
seed.  This module performs the **joint** selection that
`Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean` reported missing, and hands the result to
`dwz63_hbudget_of_aggregateHoleFraction_of_card`.

## The averaging

Both inputs are pre-maximization sums over *all* seeds, so they can be added:

* count — `Seed.three_mul_targets_mul_buckets_mul_seeds_le_four_mul_square_mul_sum_isolatedIncidences`
  (`Combinatorics/HashingIsolationIncidenceAveraging.lean`):
  `3 · #marked · #buckets · #Seed ≤ 4 |R|² ∑_seed I(seed)`;
* holes — `sum_dwz63SeedHoleMass_mul_cube_le`:
  `(∑_seed H(seed)) |R|³ ≤ #marked · #buckets · |A| · V · #Seed`.

`dwz63_holeMass_averaging_arith` is the resulting integer arithmetic: with
`256 V ≤ 3 |R|` (`[DuanWuZhou2022]`'s `M₀` with a larger constant — see below) and any `count`
with `8 |R|² · count ≤ 3 · #marked · #buckets`, one gets

`32 ∑_seed H(seed) + #Seed · (|A| · count) ≤ |A| ∑_seed I(seed)`,

and a single seed beating the average therefore satisfies **both** `count ≤ I(seed)` and
`32 H(seed) ≤ |A| I(seed)`.  That is `dwz63_exists_seed_retained_and_holeMass`.

## The constant

`[DuanWuZhou2022]` take `M₀ = 8 · max(N_triple/N_X, N_α p_comp/N_Z)`.  Three constant-factor
losses are charged here, all explicit: `16` instead of `8` for the Markov step of the second
retention pass (`Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean`), another `2` for splitting
the aggregate budget between rule (i) and rule (ii), and the `4/3` of the exact isolation
survival.  The result is the hypothesis `256 V ≤ 3 |R|`, i.e. `M ≥ 86 V`; the retained count is
divided by the same constant, which the endpoint's subexponential `loss` absorbs.

## From the seed to the residual

`dwz63AggregateHoleFraction_of_bound` turns a bound on the individual hole sets into
`Dwz63AggregateHoleFraction`, and `dwz63_exists_seed_aggregateHoleFraction` is the assembled
statement: from the hashing hypotheses alone there is a seed whose retained family is large and
carries the residual, for **any** hole family dominated by rule (i)'s seed holes plus a rule (ii)
uselessness allowance of `1/32`.  Composed with
`dwz63_hbudget_of_aggregateHoleFraction_of_card` and `dwz63GoodBatch_surjective_of_aggregateHoleFraction`
this discharges the section 6.3 stage's `hbudget` and `hbatch` from the hash seed's existence.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`, `claim:hole_frac_low`) and §2.9
(`hashing.tex`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity ProgressionHash
open scoped BigOperators

universe u v w x

/-! ## Two elementary steps -/

/-- **Some element beats the average.** -/
theorem dwz63_exists_le_of_sum_le {σ : Type x} [Fintype σ] [Nonempty σ] (f g : σ → ℕ)
    (h : ∑ s, f s ≤ ∑ s, g s) : ∃ s : σ, f s ≤ g s := by
  by_contra hcon
  have hcon' : ∀ s : σ, g s < f s := by
    intro s
    by_contra hs
    exact hcon ⟨s, Nat.le_of_not_lt hs⟩
  have hlt : ∑ s, g s < ∑ s, f s :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun s _ ↦ hcon' s
  omega

/-- **The averaging arithmetic of the joint selection.**

`P` is the seed-summed hole mass, `Q` the seed-summed isolated incidence reward, `Sd` the number
of seeds, `q = |R|`.  The two hypotheses `F1`, `F2` are the pre-maximization sums; `F3` is the
modulus condition and `F4` fixes the count threshold. -/
theorem dwz63_holeMass_averaging_arith {P Q Sd Tm Bc Nn Vv cnt q : ℕ} (hq : 0 < q)
    (F1 : P * (q * q * q) ≤ Tm * Bc * Nn * Vv * Sd)
    (F2 : 3 * Tm * Bc * Sd ≤ 4 * (q * q) * Q)
    (F3 : 256 * Vv ≤ 3 * q)
    (F4 : 8 * (q * q) * cnt ≤ 3 * (Tm * Bc)) :
    32 * P + Sd * (Nn * cnt) ≤ Nn * Q := by
  have hq2 : 0 < q * q := Nat.mul_pos hq hq
  have hq3 : 0 < q * q * q := Nat.mul_pos hq2 hq
  have hA1 : (256 * P) * (q * q * q) ≤ (4 * (Nn * Q)) * (q * q * q) := by
    calc (256 * P) * (q * q * q) = 256 * (P * (q * q * q)) := by ring
      _ ≤ 256 * (Tm * Bc * Nn * Vv * Sd) := Nat.mul_le_mul (le_refl _) F1
      _ = (256 * Vv) * (Tm * Bc * Nn * Sd) := by ring
      _ ≤ (3 * q) * (Tm * Bc * Nn * Sd) := Nat.mul_le_mul F3 (le_refl _)
      _ = (q * Nn) * (3 * Tm * Bc * Sd) := by ring
      _ ≤ (q * Nn) * (4 * (q * q) * Q) := Nat.mul_le_mul (le_refl _) F2
      _ = (4 * (Nn * Q)) * (q * q * q) := by ring
  have hA : 256 * P ≤ 4 * (Nn * Q) := Nat.le_of_mul_le_mul_right hA1 hq3
  have hB1 : (8 * (Sd * (Nn * cnt))) * (q * q) ≤ (4 * (Nn * Q)) * (q * q) := by
    calc (8 * (Sd * (Nn * cnt))) * (q * q) = (8 * (q * q) * cnt) * (Nn * Sd) := by ring
      _ ≤ (3 * (Tm * Bc)) * (Nn * Sd) := Nat.mul_le_mul F4 (le_refl _)
      _ = Nn * (3 * Tm * Bc * Sd) := by ring
      _ ≤ Nn * (4 * (q * q) * Q) := Nat.mul_le_mul (le_refl _) F2
      _ = (4 * (Nn * Q)) * (q * q) := by ring
  have hB : 8 * (Sd * (Nn * cnt)) ≤ 4 * (Nn * Q) := Nat.le_of_mul_le_mul_right hB1 hq2
  omega

/-! ## The joint selection -/

section Selection

variable {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
variable {ι : Type v} [Fintype ι]
variable {target : R}
variable {A : Type w} [Fintype A]

/-- **One seed, good for both sides.**

From the hashing hypotheses alone — the quarter competitor bound that
`exists_seed_many_markedXYIsolatedTargets` already asks for, the shared-`Z` property of the
compatibility relation, the competitor count `V`, and the modulus condition — there is a seed
whose retained family has at least `count` members *and* whose total rule-(i) hole mass is at most
a `1/32` fraction of `|A| ·` (retained count). -/
theorem dwz63_exists_seed_retained_and_holeMass
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop) (V count : ℕ)
    (hquarter : ∀ t ∈ marked,
      4 * (LegalTriple.xyCompetitorYIndices ambient t).card ≤ Fintype.card R)
    (hzIndex : ∀ a ∈ marked, ∀ w : A,
      ∀ c ∈ dwz63FineCompetitors ambient compat a w, c.zIndex = a.zIndex)
    (hcompetitors : ∀ a ∈ marked, ∀ w : A,
      (dwz63FineCompetitors ambient compat a w).card ≤ V)
    (hmodulus : 256 * V ≤ 3 * Fintype.card R)
    (hcount : 8 * (Fintype.card R * Fintype.card R) * count ≤
      3 * (marked.card * buckets.card))
    (hA : 0 < Fintype.card A) :
    ∃ seed : Seed R ι,
      count ≤ (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card ∧
        32 * dwz63SeedHoleMass ambient marked buckets compat seed ≤
          Fintype.card A *
            (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card := by
  classical
  have hdistinct : ∀ a ∈ marked,
      ∀ alternative ∈ LegalTriple.xyCompetitorYIndices ambient a,
        alternative ≠ a.yIndex := fun a _ _ hmem ↦
    LegalTriple.yIndex_ne_of_mem_xyCompetitorYIndices ambient a hmem
  have hshared : ∀ a ∈ marked, ∀ w : A,
      ∀ c ∈ LegalTriple.fineCompetitors ambient compat a w,
        c.legIndex Tensor.Leg.Z = a.legIndex Tensor.Leg.Z := by
    intro a ha w c hc
    change c.zIndex = a.zIndex
    exact hzIndex a ha w c hc
  have hgeneric := LegalTriple.exists_seed_isolation_and_sharedLegHoleMass
    ambient marked buckets compat (LegalTriple.xyCompetitorYIndices ambient)
    (fun _ _ _ ↦ Tensor.Leg.Z) V count 32 hdistinct hquarter hshared
    hcompetitors (by simpa only [show 8 * 32 = (256 : ℕ) from rfl] using hmodulus)
    hcount hA
  -- All three DWZ hole definitions and the selected-family definition unfold identically.
  exact hgeneric

/-! ## The bucket of a retained triple, and the index bridge -/

/-- The bucket a retained triple sits in. -/
noncomputable def dwz63IsolatedBucket
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (seed : Seed R ι) (a : LegalTriple R ι target) : R := by
  classical
  exact if h : ∃ b : R, (a, b) ∈ Seed.isolatedIncidences marked buckets
      LegalTriple.xIndex LegalTriple.yIndex (LegalTriple.xyCompetitorYIndices ambient) seed then
    h.choose else 0

omit [NeZero (2 : R)] in
theorem mem_dwz63IsolatedBucket
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (seed : Seed R ι) {a : LegalTriple R ι target}
    (ha : a ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed) :
    (a, dwz63IsolatedBucket ambient marked buckets seed a) ∈
      Seed.isolatedIncidences marked buckets LegalTriple.xIndex LegalTriple.yIndex
        (LegalTriple.xyCompetitorYIndices ambient) seed := by
  classical
  have hex : ∃ b : R, (a, b) ∈ Seed.isolatedIncidences marked buckets
      LegalTriple.xIndex LegalTriple.yIndex (LegalTriple.xyCompetitorYIndices ambient) seed := by
    obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp ha
    exact ⟨p.2, by rwa [← hpa]⟩
  rw [dwz63IsolatedBucket, dif_pos hex]
  exact hex.choose_spec

omit [NeZero (2 : R)] in
/-- **The hole mass, re-indexed by the retained triples.** -/
theorem sum_card_dwz63SeedSharedHoles_le_holeMass
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) :
    ∑ a ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed,
        (dwz63SeedSharedHoles ambient compat seed a
          (dwz63IsolatedBucket ambient marked buckets seed a)).card ≤
      dwz63SeedHoleMass ambient marked buckets compat seed := by
  classical
  have hinj : ∀ x ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed,
      ∀ y ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed,
      (x, dwz63IsolatedBucket ambient marked buckets seed x) =
        (y, dwz63IsolatedBucket ambient marked buckets seed y) → x = y := by
    intro x _ y _ h
    exact congrArg Prod.fst h
  have himage :
      ((LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).image
        fun a ↦ (a, dwz63IsolatedBucket ambient marked buckets seed a)) ⊆
      Seed.isolatedIncidences marked buckets LegalTriple.xIndex LegalTriple.yIndex
        (LegalTriple.xyCompetitorYIndices ambient) seed := by
    intro p hp
    obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp hp
    rw [← hpa]
    exact mem_dwz63IsolatedBucket ambient marked buckets seed ha
  have hreindex : (∑ p ∈ (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).image
        (fun a ↦ (a, dwz63IsolatedBucket ambient marked buckets seed a)),
      (dwz63SeedSharedHoles ambient compat seed p.1 p.2).card) =
      ∑ a ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed,
        (dwz63SeedSharedHoles ambient compat seed a
          (dwz63IsolatedBucket ambient marked buckets seed a)).card :=
    Finset.sum_image hinj
  rw [dwz63SeedHoleMass, ← hreindex]
  exact Finset.sum_le_sum_of_subset_of_nonneg himage fun _ _ _ ↦ Nat.zero_le _

end Selection

/-! ## From the seed to `Dwz63AggregateHoleFraction` -/

section Bridge

variable {J : Type u} [Fintype J] [DecidableEq J] {n m : ℕ}
variable {τ : Type v} [Fintype τ] [DecidableEq τ]

omit [Fintype τ] [DecidableEq τ] in
/-- **The residual from a pointwise bound on the hole sets.** -/
theorem dwz63AggregateHoleFraction_of_bound (seg : Fin (n + 1) → Fin m) (α : Fin m → J → ℕ)
    (retained : Finset τ) (holes : retained → Finset (SegmentedAvailableWord seg α))
    (g : τ → ℕ) (hle : ∀ a : retained, (holes a).card ≤ g a.1)
    (hsum : 16 * ∑ a ∈ retained, g a ≤
      retained.card * Fintype.card (SegmentedAvailableWord seg α)) :
    Dwz63AggregateHoleFraction seg α retained holes := by
  classical
  have hstep : ∑ a : retained, (holes a).card ≤ ∑ a ∈ retained, g a := by
    calc ∑ a : retained, (holes a).card ≤ ∑ a : retained, g a.1 :=
          Finset.sum_le_sum fun a _ ↦ hle a
      _ = ∑ a ∈ retained, g a := Finset.sum_coe_sort retained g
  rw [Dwz63AggregateHoleFraction]
  omega

omit [Fintype τ] [DecidableEq τ] in
/-- **The residual transports along an injective relabeling of the retained family.**

`Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s retained family is the *modeled* one,
`PartitionHashEncoding.modeledAddresses n (markedXYIsolatedTargets …)`, i.e. the image of the
hashing layer's legal-triple family under `PartitionHashEncoding.modeledAddress n`.  This lemma
carries `Dwz63AggregateHoleFraction` across that image; `pre` is any choice of preimage and
`hpre` its defining property. -/
theorem dwz63AggregateHoleFraction_image {τ' : Type w} [DecidableEq τ']
    (seg : Fin (n + 1) → Fin m)
    (α : Fin m → J → ℕ) (f : τ → τ') (retained : Finset τ)
    (hf : ∀ x ∈ retained, ∀ y ∈ retained, f x = f y → x = y)
    (holes : (retained.image f) → Finset (SegmentedAvailableWord seg α))
    (pre : τ' → τ) (hpre : ∀ x ∈ retained, pre (f x) = x)
    (g : τ → ℕ) (hle : ∀ a : (retained.image f), (holes a).card ≤ g (pre a.1))
    (hsum : 16 * ∑ x ∈ retained, g x ≤
      retained.card * Fintype.card (SegmentedAvailableWord seg α)) :
    Dwz63AggregateHoleFraction seg α (retained.image f) holes := by
  classical
  refine dwz63AggregateHoleFraction_of_bound seg α (retained.image f) holes
    (fun y ↦ g (pre y)) hle ?_
  have himage : ∑ y ∈ retained.image f, g (pre y) = ∑ x ∈ retained, g x := by
    rw [Finset.sum_image hf]
    exact Finset.sum_congr rfl fun x hx ↦ by rw [hpre x hx]
  have hcard : (retained.image f).card = retained.card :=
    Finset.card_image_of_injOn fun x hx y hy hxy ↦ hf x hx y hy hxy
  rw [himage, hcard]
  exact hsum

omit [Fintype τ] [DecidableEq τ] in
/-- **The residual from rule (i) plus a rule (ii) allowance.**

`shared` is Additional Zeroing-Out Step 2's rule (i) — the seed-dependent half, controlled by
`dwz63_exists_seed_retained_and_holeMass` — and `useless` is rule (ii), which is seed independent
and is charged a `1/32` allowance. -/
theorem dwz63AggregateHoleFraction_of_split (seg : Fin (n + 1) → Fin m) (α : Fin m → J → ℕ)
    (retained : Finset τ) (holes : retained → Finset (SegmentedAvailableWord seg α))
    (shared useless : τ → ℕ)
    (hle : ∀ a : retained, (holes a).card ≤ shared a.1 + useless a.1)
    (hshared : 32 * ∑ a ∈ retained, shared a ≤
      retained.card * Fintype.card (SegmentedAvailableWord seg α))
    (huseless : ∀ a ∈ retained,
      32 * useless a ≤ Fintype.card (SegmentedAvailableWord seg α)) :
    Dwz63AggregateHoleFraction seg α retained holes := by
  classical
  refine dwz63AggregateHoleFraction_of_bound seg α retained holes
    (fun a ↦ shared a + useless a) hle ?_
  have huse : 32 * ∑ a ∈ retained, useless a ≤
      retained.card * Fintype.card (SegmentedAvailableWord seg α) := by
    calc 32 * ∑ a ∈ retained, useless a = ∑ a ∈ retained, 32 * useless a := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _a ∈ retained, Fintype.card (SegmentedAvailableWord seg α) :=
          Finset.sum_le_sum huseless
      _ = retained.card * Fintype.card (SegmentedAvailableWord seg α) := by
          rw [Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_add_distrib]
  omega

end Bridge

/-! ## The assembled statement -/

section Assembled

variable {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
variable {ι : Type v} [Fintype ι]
variable {target : R}
variable {J : Type w} [Fintype J] [DecidableEq J] {n m : ℕ}

/-- **The residual, from the hash seed's existence alone.**

There is one affine seed whose retained family has at least `count` members and on which
`Dwz63AggregateHoleFraction` holds for *every* hole family dominated by Additional Zeroing-Out
Step 2's two rules: rule (i)'s seed holes `dwz63SeedSharedHoles` and a rule (ii) uselessness
allowance of `1/32`.

Composed with `dwz63_hbudget_of_aggregateHoleFraction_of_card` and
`dwz63GoodBatch_surjective_of_aggregateHoleFraction`
(`Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean`) this discharges the section 6.3 stage's
`hbudget` and `hbatch`. -/
theorem dwz63_exists_seed_aggregateHoleFraction
    (seg : Fin (n + 1) → Fin m) (α : Fin m → J → ℕ)
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → SegmentedAvailableWord seg α →
      LegalTriple R ι target → Prop)
    (V count : ℕ)
    (hquarter : ∀ t ∈ marked,
      4 * (LegalTriple.xyCompetitorYIndices ambient t).card ≤ Fintype.card R)
    (hzIndex : ∀ a ∈ marked, ∀ w : SegmentedAvailableWord seg α,
      ∀ c ∈ dwz63FineCompetitors ambient compat a w, c.zIndex = a.zIndex)
    (hcompetitors : ∀ a ∈ marked, ∀ w : SegmentedAvailableWord seg α,
      (dwz63FineCompetitors ambient compat a w).card ≤ V)
    (hmodulus : 256 * V ≤ 3 * Fintype.card R)
    (hcount : 8 * (Fintype.card R * Fintype.card R) * count ≤
      3 * (marked.card * buckets.card))
    (hA : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (useless : LegalTriple R ι target → ℕ)
    (huseless : ∀ a : LegalTriple R ι target,
      32 * useless a ≤ Fintype.card (SegmentedAvailableWord seg α)) :
    ∃ seed : Seed R ι,
      count ≤ (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card ∧
        ∀ holes : (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed) →
            Finset (SegmentedAvailableWord seg α),
          (∀ a, (holes a).card ≤
              (dwz63SeedSharedHoles ambient compat seed a.1
                (dwz63IsolatedBucket ambient marked buckets seed a.1)).card + useless a.1) →
            Dwz63AggregateHoleFraction seg α
              (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed) holes := by
  classical
  obtain ⟨seed, hcountSeed, hmass⟩ := dwz63_exists_seed_retained_and_holeMass
    ambient marked buckets compat V count hquarter hzIndex hcompetitors hmodulus hcount hA
  refine ⟨seed, hcountSeed, ?_⟩
  intro holes hholes
  refine dwz63AggregateHoleFraction_of_split seg α _ holes
    (fun a ↦ (dwz63SeedSharedHoles ambient compat seed a
      (dwz63IsolatedBucket ambient marked buckets seed a)).card)
    useless hholes ?_ (fun a _ ↦ huseless a)
  have hreindex := sum_card_dwz63SeedSharedHoles_le_holeMass ambient marked buckets compat seed
  have hcomm : Fintype.card (SegmentedAvailableWord seg α) *
      (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card =
      (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card *
        Fintype.card (SegmentedAvailableWord seg α) := Nat.mul_comm _ _
  omega

end Assembled

end AlgebraicComplexity.Examples
