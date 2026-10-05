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

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  Beside
`Combinatorics/HashingIsolationIncidenceAveraging.lean`, which sums the *isolated incidence*
reward over every affine seed before any seed is chosen, this module sums the *hole mass* over
every affine seed, in the same division-free style.  Together they let a client pick one seed that
is good for the retained count and for the holes at once.

## The setting

`marked ⊆ ambient` are families of legal triples, `buckets` the hash buckets, and `A` a finite
alphabet of *fine* blocks sitting inside the block a triple names.  A ternary relation

`compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop`

reads `compat a w c` as "the fine block `w`, read in the copy `a`, is compatible with the competing
triple `c`".  The relation is deliberately **owner relative**: the copies are identified with one
reference copy by their own relabelings, so the competitor test depends on which copy the fine
block is being read in.  The diagonal is never tested — `fineCompetitors` erases the owner.

## What a hole is

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§6.2 (`global_value.tex`)**, `claim:hole_frac_low` (`[DuanWuZhou2022]`).

Fixing a retained triple `(X_I, Y_J, Z_K)` and a small block `Z_K̂ ∈ Z_K` useful for it, `Z_K̂` is a
hole exactly when some *different* remaining triple `(X_{I'}, Y_{J'}, Z_K)` is also compatible with
it, and the paper's necessary condition for that is `Z_K̂` compatible with `X_{I'}` together with
`hash_X(I') = hash_Z(K)`.  For a legal triple sharing `Z_K` the latter already forces
`hash_Y(J') = hash_Z(K)` (`Seed.zHash_eq_of_commonBucket`, `Seed.inCommonTriple_iff_commonBucket`),
so the condition is `Seed.InCommonTriple` at the retained copy's own bucket.  `seedSharedHoles` is
that set of fine blocks and `seedHoleMass` sums it over the isolated incidences of one seed.

## The bound

`sum_seedHoleMass_mul_cube_le`:

`(∑_seed seedHoleMass seed) · |R|³ ≤ #marked · #buckets · |A| · V · #Seed`,

i.e. `E_seed[hole mass] ≤ #marked · #buckets · |A| · V / |R|³`.  The `|R|³` is
`lemma:hash_independence` in its committed division-free form,
`card_inCommonTriple_sharedZ_mul_cube`: two hash equations pin the retained triple in its bucket
and a third pins the competitor there, and the three are independent.  Two hypotheses on the
relation carry the paper's side conditions and nothing else:

* `hzIndex` — a counted competitor shares the owner's `Z`-index.  This is
  `lemma:triple_implies_compatible` (`global_value.tex:63-72`), and it is what licenses the
  *shared-`Z`* conditional mass;
* `hcompetitors` — a uniform bound `V` on the number of competitors of one fine block, the paper's
  `N_α · p_comp / N_Z`.

`holeMass_averaging_arith` is the integer arithmetic that combines this bound with the isolated
incidence sum: with `256 V ≤ 3 |R|` and any `cnt` satisfying `8 |R|² cnt ≤ 3 · #marked · #buckets`,

`32 ∑_seed H(seed) + #Seed · (|A| · cnt) ≤ |A| ∑_seed I(seed)`,

so a seed beating the average satisfies both `cnt ≤ I(seed)` and `32 H(seed) ≤ |A| I(seed)`.

Everything here is finite and exact.  There is no tensor, entropy, asymptotic passage,
compatibility-rate estimate, or matrix-multiplication assumption.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R] [Fintype R]
variable {ι : Type v} [Fintype ι]
variable {target : R}
variable {A : Type w} [Fintype A]

/-! ## The competitor family of a fine block -/

/-- **The competitors of the copy `a` at the fine block `w`.**

Ambient triples other than `a` that `w` — read in `a`'s own coordinates — is compatible with.
The owner is erased, so nothing here constrains `compat a w a`. -/
noncomputable def fineCompetitors
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (a : LegalTriple R ι target) (w : A) : Finset (LegalTriple R ι target) := by
  classical
  exact (ambient.erase a).filter (compat a w)

omit [Fintype R] [Fintype ι] [Fintype A] in
theorem mem_fineCompetitors
    {ambient : Finset (LegalTriple R ι target)}
    {compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop}
    {a : LegalTriple R ι target} {w : A} {c : LegalTriple R ι target} :
    c ∈ fineCompetitors ambient compat a w ↔ (c ≠ a ∧ c ∈ ambient) ∧ compat a w c := by
  classical
  simp [fineCompetitors]

/-! ## The holes of one seed -/

/-- **`claim:hole_frac_low`'s hole condition, at one seed.**

The fine blocks of the copy `a`, sitting in bucket `bkt`, that some *other* ambient triple lands
on in the same bucket. -/
noncomputable def seedSharedHoles
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) (a : LegalTriple R ι target) (bkt : R) : Finset A := by
  classical
  exact Finset.univ.filter fun w ↦
    ∃ c ∈ fineCompetitors ambient compat a w,
      Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed

/-- The competitors that actually witness a hole: those landing in the copy's own bucket. -/
noncomputable def bucketWitnesses
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) (a : LegalTriple R ι target) (bkt : R) (w : A) :
    Finset (LegalTriple R ι target) := by
  classical
  exact (fineCompetitors ambient compat a w).filter fun c ↦
    Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
      Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed

/-- **The total hole mass of one seed**: the holes of every retained incidence. -/
noncomputable def seedHoleMass
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) : ℕ := by
  classical
  exact ∑ p ∈ Seed.isolatedIncidences marked buckets
      LegalTriple.xIndex LegalTriple.yIndex (xyCompetitorYIndices ambient) seed,
    (seedSharedHoles ambient compat seed p.1 p.2).card

/-! ## The pointwise bound -/

omit [Fintype R] in
/-- **One retained copy's holes, counted by witnesses.**

Every hole block carries at least one witnessing competitor in the copy's own bucket. -/
theorem card_seedSharedHoles_le
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) (a : LegalTriple R ι target) (bkt : R)
    (ha : Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed) :
    (seedSharedHoles ambient compat seed a bkt).card ≤
      ∑ w : A, (bucketWitnesses ambient compat seed a bkt w).card := by
  classical
  rw [seedSharedHoles, Finset.card_filter]
  refine Finset.sum_le_sum ?_
  intro w _
  by_cases hw : ∃ c ∈ fineCompetitors ambient compat a w,
      Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed
  · rw [if_pos hw]
    obtain ⟨c, hc, hcbucket⟩ := hw
    refine Finset.card_pos.mpr ⟨c, ?_⟩
    simp only [bucketWitnesses, Finset.mem_filter]
    exact ⟨hc, ha, hcbucket⟩
  · rw [if_neg hw]
    exact Nat.zero_le _

/-! ## The seed sum: `lemma:hash_independence`, summed over competitors -/

omit [Fintype A] in
/-- **The witness count of one `(copy, bucket, block)`, summed over all seeds.**

Exactly `#competitors · #Seed / |R|³`: the two hash equations pinning `a` in `bkt` and the third
pinning the competitor there are independent, which is `card_inCommonTriple_sharedZ_mul_cube`. -/
theorem sum_card_bucketWitnesses_mul_cube [NeZero (2 : R)]
    (ambient : Finset (LegalTriple R ι target))
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (a : LegalTriple R ι target) (bkt : R) (w : A)
    (hzIndex : ∀ c ∈ fineCompetitors ambient compat a w, c.zIndex = a.zIndex) :
    (∑ seed : Seed R ι, (bucketWitnesses ambient compat seed a bkt w).card) *
        (Fintype.card R * Fintype.card R * Fintype.card R) =
      (fineCompetitors ambient compat a w).card * Fintype.card (Seed R ι) := by
  classical
  have hswap : (∑ seed : Seed R ι, (bucketWitnesses ambient compat seed a bkt w).card) =
      ∑ c ∈ fineCompetitors ambient compat a w,
        (Finset.univ.filter fun seed : Seed R ι ↦
          Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
            Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed).card := by
    have hleft : ∀ seed : Seed R ι,
        (bucketWitnesses ambient compat seed a bkt w).card =
          ∑ c ∈ fineCompetitors ambient compat a w,
            (if Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
                Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed then 1 else 0) := by
      intro seed
      rw [bucketWitnesses, Finset.card_filter]
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
  have hterm : ∀ c ∈ fineCompetitors ambient compat a w,
      (Finset.univ.filter fun seed : Seed R ι ↦
          Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
            Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed).card *
        (Fintype.card R * Fintype.card R * Fintype.card R) =
      Fintype.card (Seed R ι) := by
    intro c hc
    have hne : c ≠ a := (mem_fineCompetitors.mp hc).1.1
    have hbridge :
        (Finset.univ.filter fun seed : Seed R ι ↦
            Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
              Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed).card =
          Nat.card {seed : Seed R ι //
            Seed.InCommonTriple a.xIndex a.yIndex a.zIndex target bkt seed ∧
              Seed.InCommonTriple c.xIndex c.yIndex c.zIndex target bkt seed} := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hbridge]
    exact card_inCommonTriple_sharedZ_mul_cube hne (hzIndex c hc) bkt
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]

/-! ## The seed-summed hole mass -/

/-- **The expectation bound on the hole mass**, division-free.

`(∑_seed seedHoleMass seed) · |R|³ ≤ #marked · #buckets · |A| · V · #Seed`.

This is `claim:hole_frac_low` before any seed is chosen: the union bound over the competitors of
each fine block, with the per-pair conditional collision mass `1/|R|` of `lemma:hash_independence`
in its committed division-free form. -/
theorem sum_seedHoleMass_mul_cube_le [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop) (V : ℕ)
    (hzIndex : ∀ a ∈ marked, ∀ w : A,
      ∀ c ∈ fineCompetitors ambient compat a w, c.zIndex = a.zIndex)
    (hcompetitors : ∀ a ∈ marked, ∀ w : A,
      (fineCompetitors ambient compat a w).card ≤ V) :
    (∑ seed : Seed R ι, seedHoleMass ambient marked buckets compat seed) *
        (Fintype.card R * Fintype.card R * Fintype.card R) ≤
      marked.card * buckets.card * Fintype.card A * V * Fintype.card (Seed R ι) := by
  classical
  have hseed : ∀ seed : Seed R ι,
      seedHoleMass ambient marked buckets compat seed ≤
        ∑ p ∈ marked.product buckets,
          ∑ w : A, (bucketWitnesses ambient compat seed p.1 p.2 w).card := by
    intro seed
    have hsub : Seed.isolatedIncidences marked buckets
        LegalTriple.xIndex LegalTriple.yIndex
        (xyCompetitorYIndices ambient) seed ⊆ marked.product buckets := by
      rw [Seed.isolatedIncidences]
      exact Finset.filter_subset _ _
    refine le_trans (Finset.sum_le_sum ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
    · intro p hp
      have hevent := (Finset.mem_filter.mp hp).2
      have hbucket : Seed.InCommonBucket p.1.xIndex p.1.yIndex p.2 seed := hevent.1
      exact card_seedSharedHoles_le ambient compat seed p.1 p.2
        ((Seed.inCommonTriple_iff_commonBucket seed p.1.xIndex p.1.yIndex p.1.zIndex
          target p.2 p.1.legal).mpr hbucket)
    · intro p _ _
      exact Nat.zero_le _
  have hsum : (∑ seed : Seed R ι, seedHoleMass ambient marked buckets compat seed) ≤
      ∑ p ∈ marked.product buckets, ∑ w : A,
        ∑ seed : Seed R ι, (bucketWitnesses ambient compat seed p.1 p.2 w).card := by
    calc (∑ seed : Seed R ι, seedHoleMass ambient marked buckets compat seed)
        ≤ ∑ seed : Seed R ι, ∑ p ∈ marked.product buckets,
            ∑ w : A, (bucketWitnesses ambient compat seed p.1 p.2 w).card :=
          Finset.sum_le_sum fun seed _ ↦ hseed seed
      _ = ∑ p ∈ marked.product buckets, ∑ seed : Seed R ι,
            ∑ w : A, (bucketWitnesses ambient compat seed p.1 p.2 w).card :=
          Finset.sum_comm
      _ = ∑ p ∈ marked.product buckets, ∑ w : A,
            ∑ seed : Seed R ι, (bucketWitnesses ambient compat seed p.1 p.2 w).card :=
          Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm
  calc (∑ seed : Seed R ι, seedHoleMass ambient marked buckets compat seed) *
        (Fintype.card R * Fintype.card R * Fintype.card R)
      ≤ (∑ p ∈ marked.product buckets, ∑ w : A,
          ∑ seed : Seed R ι, (bucketWitnesses ambient compat seed p.1 p.2 w).card) *
            (Fintype.card R * Fintype.card R * Fintype.card R) :=
        Nat.mul_le_mul hsum (le_refl _)
    _ = ∑ p ∈ marked.product buckets, ∑ w : A,
          ((∑ seed : Seed R ι, (bucketWitnesses ambient compat seed p.1 p.2 w).card) *
            (Fintype.card R * Fintype.card R * Fintype.card R)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_mul _ _ _
    _ = ∑ p ∈ marked.product buckets, ∑ _w : A,
          ((fineCompetitors ambient compat p.1 _w).card * Fintype.card (Seed R ι)) := by
        refine Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun w _ ↦ ?_
        have hmem := (Finset.mem_product.mp hp).1
        exact sum_card_bucketWitnesses_mul_cube ambient compat p.1 p.2 w (hzIndex p.1 hmem w)
    _ ≤ ∑ _p ∈ marked.product buckets, ∑ _w : A, (V * Fintype.card (Seed R ι)) := by
        refine Finset.sum_le_sum fun p hp ↦ Finset.sum_le_sum fun w _ ↦ ?_
        have hmem := (Finset.mem_product.mp hp).1
        exact Nat.mul_le_mul (hcompetitors p.1 hmem w) (le_refl _)
    _ = marked.card * buckets.card * Fintype.card A * V * Fintype.card (Seed R ι) := by
        simp [Finset.sum_const, Finset.card_product, mul_comm, mul_assoc, mul_left_comm]

/-! ## The averaging arithmetic -/

/-- **The averaging arithmetic of the joint seed selection.**

`P` is the seed-summed hole mass, `Q` the seed-summed isolated incidence reward, `Sd` the number
of seeds, `q = |R|`.  `F1` is `sum_seedHoleMass_mul_cube_le` and `F2` is
`Seed.three_mul_targets_mul_buckets_mul_seeds_le_four_mul_square_mul_sum_isolatedIncidences`;
`F3` is the modulus condition and `F4` fixes the count threshold.  The conclusion is what a
seed beating the average has to satisfy for both sides at once. -/
theorem holeMass_averaging_arith {P Q Sd Tm Bc Nn Vv cnt q : ℕ} (hq : 0 < q)
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

end ProgressionHash.LegalTriple

end AlgebraicComplexity
