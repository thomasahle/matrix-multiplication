/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedDivisionSymSix

set_option autoImplicit false

/-!
# One region of a segmented leaf is a one-segment leaf

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  Two spellings of the same object meet at
`[duan2023faster]`'s section 6.3 factorisation and have to be identified once:

* a **region** of the fifteen-segment leaf, which the division of
  `MatrixMultiplication/SegmentedLocalizedDivisionIterated.lean` peels.  Its segmentation is
  constant --- `segmentationLeft` of the block segmentation is `fun _ ↦ label`
  (`MatrixMultiplication/SegmentedConsecutiveBlocks.lean`) --- and its profile prescribes a type on
  its own segment and the **zero** type on the other fourteen;
* a **one-segment leaf**, `m = 1` with `seg = fun _ ↦ 0`, which is what the per-cell weights are
  proved about.

They are the same partitioned tensor: on a region confined to one segment both keep predicates
collapse to the pooled multiplicity condition
(`SegmentedSplitRestriction.keeps_const_seg_iff`), and a selection depends on its predicate only up
to logical equivalence.  `segmentedLocalizedSplittingPower_constSeg_eq_oneSegment` is that
identification, and it is an **equation**, not a restriction --- so nothing is lost and no second
object enters the development.

`HasTauWeight.symSix_pow_six` is the other half of the plumbing: the per-cell weights are proved
for the leaf, and `[duan2023faster]`'s functional is `V^{(6)}`, so a region's `sym₆`-weight is its
weight to the sixth.  Both factors of six are committed
(`HasTauWeight.symThree_pow_three`, `HasTauWeight.symSix_pow_two`); this only composes them.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.3 (the level-two global-value
example), `papers/sources/2210.10173/global_value.tex:332-348`; the restricted-splitting values
`V^{(6)}` and `V^{(3)}` are defined at `papers/sources/2210.10173/prelim.tex:342-363`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

/-! ## A selection depends on its predicate only up to equivalence -/

section CongrKeeps

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **Equivalent segment conditions give the same localized segmented leaf**, even at different
segment counts.  The coarsening conjunct and the ambient power are untouched, so only the
`Keeps` conjunct has to be compared. -/
theorem Tensor.PartitionedTensor.segmentedLocalizedSplittingPower_congr_keeps
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c) (n m m' : ℕ)
    (seg : Fin (n + 1) → Fin m) (seg' : Fin (n + 1) → Fin m')
    (profile : SegmentedSplitRestriction A m) (profile' : SegmentedSplitRestriction A m')
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (h : ∀ c word, profile.Keeps n seg c word ↔ profile'.Keeps n seg' c word) :
    P.segmentedLocalizedSplittingPower f n m seg profile target =
      P.segmentedLocalizedSplittingPower f n m' seg' profile' target := by
  classical
  apply PartitionedTensor.ext
  · ext address
    rw [PartitionedTensor.mem_segmentedLocalizedSplittingPower_support,
      PartitionedTensor.mem_segmentedLocalizedSplittingPower_support]
    exact and_congr_right fun _ ↦
      forall_congr' fun c ↦ and_congr_right fun _ ↦ h c (address c)
  · rfl

end CongrKeeps

/-! ## A region confined to one segment is a one-segment leaf -/

section OneSegment

variable {A : Leg → Type w} [∀ c, DecidableEq (A c)]

/-- On a region confined to segment `t₀`, the `M`-segment keep predicate of a single restricted
leg is the pooled multiplicity condition on that leg. -/
theorem SegmentedSplitRestriction.keeps_ofLeg_ite_const_iff {M n : ℕ} (c₀ : Leg) (t₀ : Fin M)
    (α : A c₀ → ℕ) (word : PositiveWord (A c₀) n) :
    (SegmentedSplitRestriction.ofLeg (A := A) c₀
        (fun t ↦ if t = t₀ then α else 0)).Keeps n (fun _ ↦ t₀) c₀ word ↔
      WordType.multiplicity (positiveWordEquiv (A c₀) n word) = α := by
  rw [SegmentedSplitRestriction.keeps_const_seg_iff _ _ t₀ c₀ (fun t _ ↦ by
    right
    rw [SegmentedSplitRestriction.ofLeg_self]
    split <;> simp_all)]
  constructor
  · intro h
    exact h α (by rw [SegmentedSplitRestriction.ofLeg_self]; simp)
  · intro h β hβ
    rw [SegmentedSplitRestriction.ofLeg_self] at hβ
    simp only at hβ
    rw [← Option.some.inj hβ]
    exact h

/-- The same for the one-segment spelling. -/
theorem SegmentedSplitRestriction.keeps_ofLeg_one_iff {n : ℕ} (c₀ : Leg) (α : A c₀ → ℕ)
    (word : PositiveWord (A c₀) n) :
    (SegmentedSplitRestriction.ofLeg (A := A) c₀
        (fun _ : Fin 1 ↦ α)).Keeps n (fun _ ↦ 0) c₀ word ↔
      WordType.multiplicity (positiveWordEquiv (A c₀) n word) = α := by
  rw [SegmentedSplitRestriction.keeps_const_seg_iff _ _ 0 c₀
    (fun t ht ↦ absurd (Subsingleton.elim t 0) ht)]
  constructor
  · intro h
    exact h α (by rw [SegmentedSplitRestriction.ofLeg_self])
  · intro h β hβ
    rw [SegmentedSplitRestriction.ofLeg_self] at hβ
    rw [← Option.some.inj hβ]
    exact h

end OneSegment

section OneSegmentLeaf

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **A region of the fifteen-segment leaf IS a one-segment leaf.**

The left-hand side is what the regional division peels --- constant segmentation `t₀`, the type
`α` on segment `t₀` and the zero type elsewhere.  The right-hand side is what the per-cell
weights are proved about.  They are equal, so a per-cell weight transports with no bridge object
and no restriction.

Proof sketch: the two localized splitting powers differ only in their `Keeps` conjunct --- same
ambient power, same coarsening, same target --- so
`segmentedLocalizedSplittingPower_congr_keeps` reduces the equation to a pointwise equivalence of
keep predicates, leg by leg.  On the restricted leg `c₀` both sides collapse to the same pooled
multiplicity condition `WordType.multiplicity (positiveWordEquiv _ _ word) = α`, by
`keeps_ofLeg_ite_const_iff` on the left (the constant segmentation sees only segment `t₀`, whose
prescribed type is `α`, the other segments carrying the zero type) and by `keeps_ofLeg_one_iff` on
the right (a single segment, so `Subsingleton.elim` discharges the side condition); both are
instances of the committed `SegmentedSplitRestriction.keeps_const_seg_iff`.  On the other two legs
`SegmentedSplitRestriction.ofLeg_of_ne` makes every segment's prescription `none`, so
`keeps_of_all_none` proves both sides outright. -/
theorem segmentedLocalizedSplittingPower_constSeg_eq_oneSegment
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c) (n M : ℕ)
    (c₀ : Leg) (t₀ : Fin M) (α : A c₀ → ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n)) :
    P.segmentedLocalizedSplittingPower f n M (fun _ ↦ t₀)
        (SegmentedSplitRestriction.ofLeg c₀ (fun t ↦ if t = t₀ then α else 0)) target =
      P.segmentedLocalizedSplittingPower f n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg c₀ (fun _ ↦ α)) target := by
  refine Tensor.PartitionedTensor.segmentedLocalizedSplittingPower_congr_keeps P f n M 1
    (fun _ ↦ t₀) (fun _ ↦ 0) _ _ target ?_
  intro c word
  by_cases hc : c₀ = c
  · subst hc
    rw [SegmentedSplitRestriction.keeps_ofLeg_ite_const_iff,
      SegmentedSplitRestriction.keeps_ofLeg_one_iff]
  · constructor <;> intro _ <;>
      exact SegmentedSplitRestriction.keeps_of_all_none
        (fun t ↦ SegmentedSplitRestriction.ofLeg_of_ne _ hc t) word

end OneSegmentLeaf

/-! ## From a weight to a `sym₆`-weight -/

section SymSixPow

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **A weight `v` is a `sym₆`-weight `v ^ 6`.**  The two committed halves
`HasTauWeight.symThree_pow_three` and `HasTauWeight.symSix_pow_two`, composed; this is what turns
a per-cell weight into the `V^{(6)}` weight the section 6.3 endpoint asks for. -/
theorem HasTauWeight.symSix_pow_six {X : Tensor3 K V} {τ value : ℝ}
    (h : HasTauWeight K X τ value) (hvalue : 0 ≤ value) :
    HasTauWeight K (symSix K X) τ (value ^ 6) := by
  have h6 := (h.symThree_pow_three hvalue).symSix_pow_two (by positivity)
  rwa [← pow_mul] at h6

end SymSixPow

/-! ## A one-segment weight is a region's `sym₆` entry -/

section RegionEntry

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **A per-cell weight, in the one-segment spelling, is a region's `sym₆` entry.**

This is the whole join between the two lanes: the per-cell weights are proved for the
one-segment leaf and weigh the leaf itself, while `SegmentedRegionalSymSixWeights` asks for a
`sym₆`-weight of a region of the `M`-segment leaf.  The first is an equation
(`segmentedLocalizedSplittingPower_constSeg_eq_oneSegment`), the second a sixth power
(`HasTauWeight.symSix_pow_six`); neither loses anything. -/
theorem hasTauWeight_symSix_region_of_oneSegment
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c) (n M : ℕ)
    (c₀ : Leg) (t₀ : Fin M) (α : A c₀ → ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n)) {τ value : ℝ}
    (h : HasTauWeight K
      (P.segmentedLocalizedSplittingPower f n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg c₀ (fun _ ↦ α)) target).realize τ value)
    (hvalue : 0 ≤ value) :
    HasTauWeight K
      (symSix K (P.segmentedLocalizedSplittingPower f n M (fun _ ↦ t₀)
        (SegmentedSplitRestriction.ofLeg c₀ (fun t ↦ if t = t₀ then α else 0))
        target).realize) τ (value ^ 6) := by
  rw [segmentedLocalizedSplittingPower_constSeg_eq_oneSegment]
  exact h.symSix_pow_six hvalue

end RegionEntry

end AlgebraicComplexity
