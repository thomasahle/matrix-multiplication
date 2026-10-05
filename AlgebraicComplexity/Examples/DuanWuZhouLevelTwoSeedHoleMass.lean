/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HashingConditionalIndependence
import AlgebraicComplexity.Combinatorics.MarkedTwoLegHashingExtraction

set_option autoImplicit false

/-!
# The expected hole mass of an affine seed

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean`
reduces the section 6.3 stage's `hbudget` to one open inequality,
`Dwz63AggregateHoleFraction` — the average hole fraction of the broken copies is at most `1/16`.
This module supplies the first half of its proof: the exact seed-summed bound on the hole mass
created by Additional Zeroing-Out Step 2's rule (i).

## What a hole *is* for the hash

`[DuanWuZhou2022]`, `claim:hole_frac_low` (`global_value.tex:250-256`): fixing a retained triple
`(X_I, Y_J, Z_K)` and a small block `Z_K̂ ∈ Z_K` useful for it, `Z_K̂` is a hole exactly when it is
compatible with a **different** remaining triple `(X_{I'}, Y_{J'}, Z_K)`, and the paper's necessary
condition for that is

> there exists `I' ≠ I` matchable to `K` with (1) `Z_K̂` compatible with `X_{I'}`, and
> (2) `hash_X(I') = hash_Z(K)`.

Condition (2) is `Seed.InCommonTriple` at the *same bucket* as the retained triple: for a legal
triple sharing `Z_K`, `hash_X(I') = hash_Z(K)` already forces `hash_Y(J') = hash_Z(K)` — that is
`Seed.zHash_eq_of_commonBucket` / `inCommonTriple_iff_commonBucket`, the committed reading of
`lemma:hash_independence`'s hypothesis.  `dwz63SeedSharedHoles` is exactly that set of fine words,
and `dwz63SeedHoleMass` sums it over the retained incidences of one seed.

## Owner-relative compatibility

The compatibility relation is `compat : LegalTriple → A → LegalTriple → Prop`, ternary:
`compat a w c` reads "the fine word `w`, read in the copy `a`, is compatible with the competing
triple `c`".  `Examples/DuanWuZhouLevelTwoHoleFractionRefutation.lean` shows why a *binary*
relation on a shared reference alphabet is inconsistent with rule (ii): each copy is identified
with the reference leaf by its own position relabeling, so rule (i)'s test is owner relative.  The
diagonal is never tested here — `dwz63FineCompetitors` erases `a` — which is precisely what makes
this shape satisfiable.

## The two hypotheses on the relation, and where they come from

* `hzIndex` — a competitor counted at `a` shares `a`'s `Z`-index.  This is
  `lemma:triple_implies_compatible` (`global_value.tex:63-72`): a small block of `Z_K` can only be
  compatible with triples through `Z_K`.  It is what licenses the *shared-`Z`* conditional mass.
* `hcompetitors` — a uniform bound `V` on the number of competitors of one fine word.  This is
  `[DuanWuZhou2022]`'s competitor count `N_α · p_comp / N_Z`, which
  `Analysis/CompatibilityRate.lean` computes exactly as
  `card_matchableCompatible_eq_mul_compatibleFraction`.

## The bound

`sum_dwz63SeedHoleMass_mul_cube_le` is, division-free,

`(∑_seed holeMass seed) · |R|³ ≤ #marked · #buckets · |A| · V · #Seed`,

i.e. `E_seed[holeMass] ≤ #marked · #buckets · |A| · V / |R|³`.  The `|R|³` is
`lemma:hash_independence` in its committed division-free form
`LegalTriple.card_inCommonTriple_sharedZ_mul_cube`: two hash equations pin the retained triple in
its bucket and a third pins the competitor there, and the three are independent.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`) and §2.9 (`hashing.tex`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity ProgressionHash
open scoped BigOperators

universe u v w

section SeedHoleMass

variable {R : Type u} [Field R] [Fintype R]
variable {ι : Type v} [Fintype ι]
variable {target : R}
variable {A : Type w} [Fintype A]

/-! ## The competitor family of a fine word -/

/-- **The competitors of the copy `a` at the fine word `w`.**

Ambient triples other than `a` that `w` — read in `a`'s own coordinates — is compatible with.
The diagonal is erased, so nothing here constrains `compat a w a`. -/
noncomputable def dwz63FineCompetitors
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (a : LegalTriple R ι target) (w : A) : Finset (LegalTriple R ι target) := by
  classical
  exact (ambient.erase a).filter (compat a w)

omit [Fintype R] [Fintype ι] [Fintype A] in
theorem mem_dwz63FineCompetitors
    {ambient : Finset (LegalTriple R ι target)}
    {compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop}
    {a : LegalTriple R ι target} {w : A} {c : LegalTriple R ι target} :
    c ∈ dwz63FineCompetitors ambient compat a w ↔
      (c ≠ a ∧ c ∈ ambient) ∧ compat a w c := by
  classical
  simp [dwz63FineCompetitors]

/-! ## The holes of one seed -/

/-- **Rule (i) of Additional Zeroing-Out Step 2, at one seed.**

The fine words of the copy `a`, sitting in bucket `bkt`, that some *other* ambient triple lands on
in the same bucket.  See the module docstring for the reading of `claim:hole_frac_low`'s necessary
condition. -/
noncomputable def dwz63SeedSharedHoles
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) (a : LegalTriple R ι target) (bkt : R) : Finset A := by
  classical
  exact Finset.univ.filter fun w ↦
    ∃ c ∈ dwz63FineCompetitors ambient compat a w,
      Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed

/-- The competitors that actually witness a hole: those landing in the copy's own bucket. -/
noncomputable def dwz63BucketWitnesses
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) (a : LegalTriple R ι target) (bkt : R) (w : A) :
    Finset (LegalTriple R ι target) := by
  classical
  exact (dwz63FineCompetitors ambient compat a w).filter fun c ↦
    Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
      Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed

/-- **The total rule-(i) hole mass of one seed**: the holes of every retained incidence. -/
noncomputable def dwz63SeedHoleMass
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) : ℕ := by
  classical
  exact ∑ p ∈ Seed.isolatedIncidences marked buckets
      LegalTriple.xIndex LegalTriple.yIndex (LegalTriple.xyCompetitorYIndices ambient) seed,
    (dwz63SeedSharedHoles ambient compat seed p.1 p.2).card

/-! ## The pointwise bound -/

omit [Fintype R] in
/-- **One retained copy's holes, counted by witnesses.**

Every hole word carries at least one witnessing competitor in the copy's own bucket. -/
theorem card_dwz63SeedSharedHoles_le
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) (a : LegalTriple R ι target) (bkt : R)
    (ha : Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed) :
    (dwz63SeedSharedHoles ambient compat seed a bkt).card ≤
      ∑ w : A, (dwz63BucketWitnesses ambient compat seed a bkt w).card := by
  classical
  rw [dwz63SeedSharedHoles, Finset.card_filter]
  refine Finset.sum_le_sum ?_
  intro w _
  by_cases hw : ∃ c ∈ dwz63FineCompetitors ambient compat a w,
      Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed
  · rw [if_pos hw]
    obtain ⟨c, hc, hcbucket⟩ := hw
    refine Finset.card_pos.mpr ⟨c, ?_⟩
    simp only [dwz63BucketWitnesses, Finset.mem_filter]
    exact ⟨hc, ha, hcbucket⟩
  · rw [if_neg hw]
    exact Nat.zero_le _

/-! ## The seed sum: `lemma:hash_independence`, summed over competitors -/

omit [Fintype A] in
/-- **The witness count of one `(copy, bucket, word)`, summed over all seeds.**

Exactly `#competitors · #Seed / |R|³`: the two hash equations pinning `a` in `bkt` and the third
pinning the competitor there are independent, which is
`LegalTriple.card_inCommonTriple_sharedZ_mul_cube`. -/
theorem sum_card_dwz63BucketWitnesses_mul_cube [NeZero (2 : R)]
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (a : LegalTriple R ι target) (bkt : R) (w : A)
    (hzIndex : ∀ c ∈ dwz63FineCompetitors ambient compat a w, c.zIndex = a.zIndex) :
    (∑ seed : Seed R ι, (dwz63BucketWitnesses ambient compat seed a bkt w).card) *
        (Fintype.card R * Fintype.card R * Fintype.card R) =
      (dwz63FineCompetitors ambient compat a w).card * Fintype.card (Seed R ι) := by
  classical
  have hswap : (∑ seed : Seed R ι, (dwz63BucketWitnesses ambient compat seed a bkt w).card) =
      ∑ c ∈ dwz63FineCompetitors ambient compat a w,
        (Finset.univ.filter fun seed : Seed R ι ↦
          Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
            Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed).card := by
    have hleft : ∀ seed : Seed R ι,
        (dwz63BucketWitnesses ambient compat seed a bkt w).card =
          ∑ c ∈ dwz63FineCompetitors ambient compat a w,
            (if Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
                Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed then 1 else 0) := by
      intro seed
      rw [dwz63BucketWitnesses, Finset.card_filter]
    have hright : ∀ c : LegalTriple R ι target,
        (Finset.univ.filter fun seed : Seed R ι ↦
            Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
              Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed).card =
          ∑ seed : Seed R ι,
            (if Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
                Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed then 1 else 0) := by
      intro c
      rw [Finset.card_filter]
    simp only [hleft, hright]
    exact Finset.sum_comm
  rw [hswap, Finset.sum_mul]
  have hterm : ∀ c ∈ dwz63FineCompetitors ambient compat a w,
      (Finset.univ.filter fun seed : Seed R ι ↦
          Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
            Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed).card *
        (Fintype.card R * Fintype.card R * Fintype.card R) =
      Fintype.card (Seed R ι) := by
    intro c hc
    have hne : c ≠ a := (mem_dwz63FineCompetitors.mp hc).1.1
    have hbridge :
        (Finset.univ.filter fun seed : Seed R ι ↦
            Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
              Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed).card =
          Nat.card {seed : Seed R ι //
            Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
              Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed} := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hbridge]
    exact LegalTriple.card_inCommonTriple_sharedZ_mul_cube hne (hzIndex c hc) bkt
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]

/-! ## The seed-summed hole mass -/

/-- **The expectation bound on the hole mass**, division-free.

`(∑_seed holeMass seed) · |R|³ ≤ #marked · #buckets · |A| · V · #Seed`.

This is `claim:hole_frac_low` before any seed is chosen: the union bound over the competitors of
each fine word, with the per-pair conditional collision mass `1/|R|` of `lemma:hash_independence`
in its committed division-free form. -/
theorem sum_dwz63SeedHoleMass_mul_cube_le [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop) (V : ℕ)
    (hzIndex : ∀ a ∈ marked, ∀ w : A,
      ∀ c ∈ dwz63FineCompetitors ambient compat a w, c.zIndex = a.zIndex)
    (hcompetitors : ∀ a ∈ marked, ∀ w : A,
      (dwz63FineCompetitors ambient compat a w).card ≤ V) :
    (∑ seed : Seed R ι, dwz63SeedHoleMass ambient marked buckets compat seed) *
        (Fintype.card R * Fintype.card R * Fintype.card R) ≤
      marked.card * buckets.card * Fintype.card A * V * Fintype.card (Seed R ι) := by
  classical
  -- Step 1: bound each seed's hole mass by the witness count over the whole target/bucket product.
  have hseed : ∀ seed : Seed R ι,
      dwz63SeedHoleMass ambient marked buckets compat seed ≤
        ∑ p ∈ marked.product buckets,
          ∑ w : A, (dwz63BucketWitnesses ambient compat seed p.1 p.2 w).card := by
    intro seed
    have hsub : Seed.isolatedIncidences marked buckets
        LegalTriple.xIndex LegalTriple.yIndex
        (LegalTriple.xyCompetitorYIndices ambient) seed ⊆ marked.product buckets := by
      rw [Seed.isolatedIncidences]
      exact Finset.filter_subset _ _
    refine le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
    · intro p hp
      have hevent := (Finset.mem_filter.mp hp).2
      have hbucket : Seed.InCommonBucket p.1.xIndex p.1.yIndex p.2 seed := hevent.1
      exact card_dwz63SeedSharedHoles_le ambient compat seed p.1 p.2
        ((Seed.inCommonTriple_iff_commonBucket seed p.1.xIndex p.1.yIndex p.1.zIndex
          target p.2 p.1.legal).mpr hbucket)
    · intro p _ _
      exact Nat.zero_le _
  -- Step 2: sum over seeds and exchange the summations.
  have hsum : (∑ seed : Seed R ι, dwz63SeedHoleMass ambient marked buckets compat seed) ≤
      ∑ p ∈ marked.product buckets, ∑ w : A,
        ∑ seed : Seed R ι, (dwz63BucketWitnesses ambient compat seed p.1 p.2 w).card := by
    calc (∑ seed : Seed R ι, dwz63SeedHoleMass ambient marked buckets compat seed)
        ≤ ∑ seed : Seed R ι, ∑ p ∈ marked.product buckets,
            ∑ w : A, (dwz63BucketWitnesses ambient compat seed p.1 p.2 w).card :=
          Finset.sum_le_sum fun seed _ ↦ hseed seed
      _ = ∑ p ∈ marked.product buckets, ∑ seed : Seed R ι,
            ∑ w : A, (dwz63BucketWitnesses ambient compat seed p.1 p.2 w).card :=
          Finset.sum_comm
      _ = ∑ p ∈ marked.product buckets, ∑ w : A,
            ∑ seed : Seed R ι, (dwz63BucketWitnesses ambient compat seed p.1 p.2 w).card :=
          Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm
  -- Step 3: evaluate the seed sum and bound the competitor count.
  have hcube : 0 < Fintype.card R * Fintype.card R * Fintype.card R := by
    have hq : 0 < Fintype.card R := Fintype.card_pos
    exact Nat.mul_pos (Nat.mul_pos hq hq) hq
  calc (∑ seed : Seed R ι, dwz63SeedHoleMass ambient marked buckets compat seed) *
        (Fintype.card R * Fintype.card R * Fintype.card R)
      ≤ (∑ p ∈ marked.product buckets, ∑ w : A,
          ∑ seed : Seed R ι, (dwz63BucketWitnesses ambient compat seed p.1 p.2 w).card) *
            (Fintype.card R * Fintype.card R * Fintype.card R) :=
        Nat.mul_le_mul hsum (le_refl _)
    _ = ∑ p ∈ marked.product buckets, ∑ w : A,
          ((∑ seed : Seed R ι, (dwz63BucketWitnesses ambient compat seed p.1 p.2 w).card) *
            (Fintype.card R * Fintype.card R * Fintype.card R)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_mul _ _ _
    _ = ∑ p ∈ marked.product buckets, ∑ _w : A,
          ((dwz63FineCompetitors ambient compat p.1 _w).card * Fintype.card (Seed R ι)) := by
        refine Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun w _ ↦ ?_
        have hmem := (Finset.mem_product.mp hp).1
        exact sum_card_dwz63BucketWitnesses_mul_cube ambient compat p.1 p.2 w
          (hzIndex p.1 hmem w)
    _ ≤ ∑ _p ∈ marked.product buckets, ∑ _w : A, (V * Fintype.card (Seed R ι)) := by
        refine Finset.sum_le_sum fun p hp ↦ Finset.sum_le_sum fun w _ ↦ ?_
        have hmem := (Finset.mem_product.mp hp).1
        exact Nat.mul_le_mul (hcompetitors p.1 hmem w) (le_refl _)
    _ = marked.card * buckets.card * Fintype.card A * V * Fintype.card (Seed R ι) := by
        simp [Finset.sum_const, Finset.card_product, mul_comm, mul_assoc, mul_left_comm]

end SeedHoleMass

end AlgebraicComplexity.Examples
