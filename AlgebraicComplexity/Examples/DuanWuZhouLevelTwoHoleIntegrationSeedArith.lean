/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedSelection
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAggregateBatching
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainCopyCount

set_option autoImplicit false

/-!
# The three arithmetic steps of the seed join

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoHoleIntegrationSeedJoin.
lean` joins the section 6.3 hole side and count side at one seed.  This module carries the three
steps of that join that are arithmetic rather than hashing, so that the join itself is short.

## The transport to block addresses

The retained family the stage indexes is
`dwz63PlainJointRetainedSupport = modeledAddresses n (markedXYIsolatedTargets …)`, the image of
the hashing layer's legal-triple family.  `dwz63AggregateHoleFraction_image`
(`Examples/DuanWuZhouLevelTwoSeedSelection.lean`) carries `Dwz63AggregateHoleFraction` across such
an image but asks for a `pre`/`hpre` section, which nothing supplies --- and it asks for the image
to be written as `retained.image f`, which a client cannot do: `modeledAddresses` forms its image
under a **classical** `DecidableEq` instance, so a client-written `Rt.image f` is a different term.
`dwz63AggregateHoleFraction_image_of_injOn` takes the image as an arbitrary `Finset`, related to
the source only by "every member has a preimage" and "the cardinalities agree" --- both committed
facts at the call site (`Finset.mem_image` and `card_markedXYIsolatedPowerAddresses`).  Nothing is
chosen, and injectivity of `f` is not used: the cardinality equation carries it.

## The count

`dwz63_exists_seed_retained_and_holeMass` binds `count` by `8 |R|² count ≤ 3 #marked #B`, while
the copy count is proved from `3 #marked #B ≤ 4 |R|² #retained`.  Taking `count` to be the
integer quotient makes the first hold by construction and, once `count` is positive, gives the
second with `16` in place of `4` --- the factor `2` the joint selection charges, once for the
averaging and once for the Markov step.

## The copy count at the joint modulus

`dwz63_rate_le_loss_of_seed` (`Examples/DuanWuZhouLevelTwoSeedCancellation.lean`) is generic in the
modulus `M`, so the variant is the committed chain at `M := 16 |R|²` with `lossHash` replaced by
`4 lossHash`, a constant that `Growth.Subexponential` absorbs.  No committed statement is re-proved.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`
(`global_value.tex`), §6.3 and
`hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash
open scoped BigOperators

universe u v w x

/-! ## The residual across an injective image, with no section to choose -/

section Transport

variable {J : Type w} [Fintype J] [DecidableEq J] {n m : ℕ}
variable {τ : Type v} {τ' : Type x}

/-- **`Dwz63AggregateHoleFraction` transports across an injective image.**

`image` is any `Finset` whose members all have a preimage in `retained` and whose cardinality
agrees --- which is exactly injectivity of `f` on `retained` together with surjectivity onto
`image`.  No section of `f` is chosen, and no `Finset.image` is written, so the lemma applies to
`modeledAddresses` on the nose. -/
theorem dwz63AggregateHoleFraction_image_of_injOn (seg : Fin (n + 1) → Fin m)
    (α : Fin m → J → ℕ) (f : τ → τ') (retained : Finset τ) (image : Finset τ')
    (hsub : ∀ y ∈ image, ∃ x ∈ retained, f x = y) (hcard : image.card = retained.card)
    (holes : image → Finset (SegmentedAvailableWord seg α)) (g : τ → ℕ)
    (hle : ∀ (a : image) (x : τ), x ∈ retained → f x = a.1 → (holes a).card ≤ g x)
    (hsum : 16 * ∑ x ∈ retained, g x ≤
      retained.card * Fintype.card (SegmentedAvailableWord seg α)) :
    Dwz63AggregateHoleFraction seg α image holes := by
  classical
  have hex : ∀ a : {y // y ∈ image}, ∃ x, x ∈ retained ∧ f x = a.1 := by
    intro a
    obtain ⟨x, hx, hxa⟩ := hsub a.1 a.2
    exact ⟨x, hx, hxa⟩
  choose φ hφmem hφeq using hex
  have hφinj : Function.Injective φ := by
    intro a b hab
    refine Subtype.ext ?_
    rw [← hφeq a, ← hφeq b, hab]
  have hstep1 : ∑ a : {y // y ∈ image}, (holes a).card ≤
      ∑ a : {y // y ∈ image}, g (φ a) :=
    Finset.sum_le_sum fun a _ ↦ hle a (φ a) (hφmem a) (hφeq a)
  have hstep2 : ∑ a : {y // y ∈ image}, g (φ a) = ∑ x ∈ Finset.univ.image φ, g x :=
    (Finset.sum_image fun x _ y _ h ↦ hφinj h).symm
  have hstep3 : ∑ x ∈ Finset.univ.image φ, g x ≤ ∑ x ∈ retained, g x := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ Nat.zero_le _
    intro y hy
    obtain ⟨a, -, hay⟩ := Finset.mem_image.mp hy
    rw [← hay]
    exact hφmem a
  have hcardMul : image.card * Fintype.card (SegmentedAvailableWord seg α) =
      retained.card * Fintype.card (SegmentedAvailableWord seg α) := by rw [hcard]
  rw [Dwz63AggregateHoleFraction]
  omega

end Transport

/-! ## The joint count, and its two integer facts -/

/-- **The count the joint seed selection is run at**: the integer quotient
`3 #marked #B / (8 |R|²)`. -/
def dwz63JointSeedCount (marked buckets q : ℕ) : ℕ := 3 * (marked * buckets) / (8 * (q * q))

/-- **`hcount`, by construction.** -/
theorem dwz63_jointSeedCount_hcount (marked buckets q : ℕ) :
    8 * (q * q) * dwz63JointSeedCount marked buckets q ≤ 3 * (marked * buckets) := by
  have h := Nat.div_mul_le_self (3 * (marked * buckets)) (8 * (q * q))
  have hcomm : 8 * (q * q) * dwz63JointSeedCount marked buckets q =
      dwz63JointSeedCount marked buckets q * (8 * (q * q)) := Nat.mul_comm _ _
  unfold dwz63JointSeedCount at hcomm ⊢
  omega

/-- **The retention bound the copy count needs**, with `16` in place of the count-only `4`. -/
theorem dwz63_three_mul_le_sixteen_mul_jointSeedCount {marked buckets q : ℕ} (hq : 0 < q)
    (hpos : 0 < dwz63JointSeedCount marked buckets q) :
    3 * (marked * buckets) ≤ 16 * (q * q) * dwz63JointSeedCount marked buckets q := by
  have hd : 0 < 8 * (q * q) := by positivity
  have hdm : 8 * (q * q) * dwz63JointSeedCount marked buckets q +
      3 * (marked * buckets) % (8 * (q * q)) = 3 * (marked * buckets) :=
    Nat.div_add_mod _ _
  have hmod : 3 * (marked * buckets) % (8 * (q * q)) < 8 * (q * q) := Nat.mod_lt _ hd
  have hDc : 8 * (q * q) ≤ 8 * (q * q) * dwz63JointSeedCount marked buckets q :=
    Nat.le_mul_of_pos_right _ hpos
  have heq : 16 * (q * q) * dwz63JointSeedCount marked buckets q =
      8 * (q * q) * dwz63JointSeedCount marked buckets q +
        8 * (q * q) * dwz63JointSeedCount marked buckets q := by ring
  omega

/-! ## The hole-mass arithmetic on the legal-triple side -/

section Mass

variable {R : Type u} [Field R] [Fintype R]
variable {ι : Type v} [Fintype ι]
variable {target : R}
variable {A : Type w} [Fintype A]

/-- **The rule-(i) plus rule-(ii) mass of the retained family**, in the shape
`dwz63AggregateHoleFraction_image_of_injOn` consumes.  This is the arithmetic of
`dwz63AggregateHoleFraction_of_split`, performed on the legal-triple index set. -/
theorem dwz63_sum_seedSharedHoles_add_useless_le
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (seed : Seed R ι) (useless : LegalTriple R ι target → ℕ)
    (hmass : 32 * dwz63SeedHoleMass ambient marked buckets compat seed ≤
      Fintype.card A * (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card)
    (huseless : ∀ a : LegalTriple R ι target, 32 * useless a ≤ Fintype.card A) :
    16 * ∑ x ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed,
        ((dwz63SeedSharedHoles ambient compat seed x
            (dwz63IsolatedBucket ambient marked buckets seed x)).card + useless x) ≤
      (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card *
        Fintype.card A := by
  classical
  have hshared := sum_card_dwz63SeedSharedHoles_le_holeMass ambient marked buckets compat seed
  have huse : 32 * ∑ x ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed,
      useless x ≤
      (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card *
        Fintype.card A := by
    calc 32 * ∑ x ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed, useless x
        = ∑ x ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed,
            32 * useless x := by rw [Finset.mul_sum]
      _ ≤ ∑ _x ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed,
            Fintype.card A := Finset.sum_le_sum fun x _ ↦ huseless x
      _ = (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card *
            Fintype.card A := by rw [Finset.sum_const, smul_eq_mul]
  have hcomm : Fintype.card A *
      (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card =
      (LegalTriple.markedXYIsolatedTargets ambient marked buckets seed).card *
        Fintype.card A := Nat.mul_comm _ _
  rw [Finset.sum_add_distrib]
  omega

end Mass

/-! ## The copy count at the joint modulus -/

section CopyCount

variable {R : Type v} [Field R] [Fintype R]

/-- **The sixth power of the plain copy count, at the joint selection's retention bound.**

The committed chain with `M := 16 |R|²` instead of `4 |R|²`; the price is the constant `4` in the
loss, which `Growth.Subexponential` absorbs. -/
theorem dwz63_plainCopyCount_pow_six_fintype_of_joint
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {lossHash : ℝ} (hlossHash : 0 ≤ lossHash)
    (hseed : 3 * (markedWords.card * B.card) ≤
      16 * (Fintype.card R * Fintype.card R) *
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card)
    (hbranch : dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash * (3 * (markedWords.card : ℝ) * (B.card : ℝ))) :
    dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      (4 * lossHash) ^ 6 *
        ((Fintype.card
          (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) : ℝ) ^ 6) := by
  have hqpos : (0 : ℝ) < (Fintype.card R : ℝ) := by
    have hpos : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨(0 : R)⟩
    exact_mod_cast hpos
  have hseedR : 3 * (markedWords.card : ℝ) * (B.card : ℝ) ≤
      (16 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) *
        ((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hseed
    push_cast at this
    linarith
  have hbranch' : dwz63HashingBranch ^ (n + 1) *
      (16 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      (4 * lossHash) * (3 * (markedWords.card : ℝ) * (B.card : ℝ)) := by
    have h4 := mul_le_mul_of_nonneg_left hbranch (by norm_num : (0 : ℝ) ≤ 4)
    calc dwz63HashingBranch ^ (n + 1) *
          (16 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ)))
        = 4 * (dwz63HashingBranch ^ (n + 1) *
            (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ)))) := by ring
      _ ≤ 4 * (lossHash * (3 * (markedWords.card : ℝ) * (B.card : ℝ))) := h4
      _ = (4 * lossHash) * (3 * (markedWords.card : ℝ) * (B.card : ℝ)) := by ring
  have hrate : dwz63HashingBranch ^ (n + 1) ≤
      (4 * lossHash) *
        ((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card : ℝ) :=
    dwz63_rate_le_loss_of_seed
      (M := 16 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) (by positivity)
      (by linarith) hseedR hbranch'
  have hcopy : dwz63TrueCopyRate ^ (n + 1) ≤
      (4 * lossHash) *
        ((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card : ℝ) :=
    (dwz63TrueCopyRate_pow_le_hashingBranch_pow _).trans hrate
  have h6 := pow_six_of_copyCount dwz63TrueCopyRate_pos.le hcopy
  rwa [Fintype.card_coe]

end CopyCount

end AlgebraicComplexity.Examples
