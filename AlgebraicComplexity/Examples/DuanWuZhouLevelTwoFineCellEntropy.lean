/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellSurjective
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellWeight
import AlgebraicComplexity.Combinatorics.TypeClassCounting

set_option autoImplicit false

/-!
# The entropy rate of the `(0,2,2)` fine cell, eventually

Layer 4 (`AlgebraicComplexity/Examples/`).  This closes the fine-cell counting chain of
`[duan2023faster]` section 6.3 for a zero-`X` cell:

* `Examples/DuanWuZhouLevelTwoFineCellFusion.lean` --- the fibre fuses onto
  `⟨1, |fibre| q^k, 1⟩`;
* `Examples/DuanWuZhouLevelTwoFineCellWeight.lean` --- that is a `tau`-weight, `|fibre|` symbolic;
* `Examples/DuanWuZhouLevelTwoFineCellSurjective.lean` --- `|typeClass| <= |fibre|`;
* here --- `|typeClass|` is eventually above any base strictly below the entropy rate.

## Why the conclusion is eventual, and in the shape it is

`WordType.card_typeClass_eq_multinomial` gives the fibre cardinality *exactly*, as a multinomial
coefficient, but a multinomial coefficient only **approaches** `2^(mass * H)`; it is never above it.
So the value cannot be stated as an exact per-letter rate.  The committed shape for that situation
is `TypeClassCounting.exists_cutoff_forall_pow_le_card_proportionalTypeClass`: fix any
`lowerBase` *strictly* below `2^(mass * H)` and the exact integral cardinality dominates
`lowerBase ^ k` from some cutoff on, with no residual loss factor.  That is the strict-base reserve
idiom of `log_dwz112LeafTerm_eq` (`Examples/DuanWuZhouLevelTwoLeafTauWeight.lean`), where the
achieved term's logarithm is recorded as the published value less an explicit reserve rather than
chased to a supremum.

The conclusion is therefore `∃ N, ∀ k ≥ N, …`, the same shape as the committed
`dwz63_exists_orbitCertificates` (`Examples/DuanWuZhouLevelTwoPlainLeafValueDischarge.lean:121`),
which is what a leaf-value client already knows how to consume: it takes the cutoff, scales the
period, and forgets it.

## The profile is `alphatilde`

`a` here is a profile on **fine letters** `PositiveWord CWBlock 1` --- a row of `dwz63AlphaTilde`,
the split profile, not a coarse cell distribution.  Its proportional refinement
`WordType.proportionalCounts a k` is the actual letter-count profile of a word of length
`profileMass a * k`, which is why the period `n + 1 = profileMass a * k` appears as a hypothesis
rather than being fixed here.

## Not attempted

The comparison of `2^(profileMass a * profileEntropyBits a) * q^(Σ a p · middles p)` with
`dwz63Val022 ^ (profileMass a)` at the paper's `a = dwz63A` is arithmetic over the committed atoms
and is left to the client; `dwz63LogVal022` is already the logarithm of exactly that quantity.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## `huniform` on the one-segment localized power, for a zero coordinate on `X` -/

/-- **`huniform` when the split profile sits on the *second* live leg.**

`dwz63CellOnes zero` counts middles at `firstLiveLeg zero`, while `alphatilde` is carried on `Z`;
for `zero = .X` those differ (`firstLiveLeg .X = .Y`, `secondLiveLeg .X = .Z`) and the committed
`dwz63_cellOnes_eq_alphaTilde_sum` crosses them through `dwz63_middleCount_liveLegs_eq`.  This is
that lemma read at an **address** rather than at a word, which is the form the fusion consumes.
The counterpart for `zero = .Y` is `dwz63_cellPower_cellOnes_eq_alphaSum_of_firstLive`
(`Examples/DuanWuZhouLevelTwoFineCellHypotheses.lean`). -/
theorem dwz63_cellPower_cellOnes_eq_alphaSum_of_secondLive (n : ℕ) (zero : Leg)
    (hlive : secondLiveLeg zero = Leg.Z)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target zero = positiveWordConst (0 : Fin 5) n)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support) :
    dwz63CellOnes zero n s = ∑ p : PositiveWord CWBlock 1, α p * cwWordMiddleCount 1 p := by
  classical
  obtain ⟨hmem, hcoarse, htype⟩ := (dwz63_mem_cellPower_support_iff K q n α target s).mp hs
  obtain ⟨w, hw⟩ :=
    ((cwPartitionedTensor K q).positivePower
      1).exists_positiveSupportWord_of_mem_positivePower_support n hmem
  subst hw
  refine dwz63_cellOnes_eq_alphaTilde_sum K q zero n α w ?_ ?_
  · refine dwz63_finePower_letter_eq_const_of_address K q zero n w ?_
    refine dwz63_zeroLegWord_eq_const zero n _ ?_
    rw [hcoarse zero]
    exact htarget
  · rw [hlive]
    exact htype

/-! ## The eventual entropy bound -/

/-- **The `(0,2,2)` fine cell attains the entropy rate of its split profile, eventually.**

For every base `lowerBase` strictly below `2 ^ (mass * H(a))`, there is a cutoff beyond which the
localized one-segment power over the coarse cell `(0,2,2)` --- the fine leaf's `(0,2,2)` segment,
cut to the proportional refinement of the split profile `a` --- carries the `tau`-weight
`(lowerBase ^ k * q ^ (Σ_p a_k(p) · middles p)) ^ tau`.

The cardinality is exact at every stage: the two inequalities used are
`WordType.typeClass ↪ fibre` (`dwz63_card_typeClass_le_zeroXFineCellSupport`) and the strict-base
eventual bound; neither introduces a loss factor. -/
theorem dwz63_exists_zeroXFineCellWeight (hq : 0 < q)
    (a : PositiveWord CWBlock 1 → ℕ)
    (hmass : 0 < WordType.profileMass a)
    (ha : ∀ p : PositiveWord CWBlock 1, a p ≠ 0 → cwSquareBlockDegree p = 2)
    (τ : ℝ) (hτ : 0 ≤ τ)
    {lowerBase : ℝ} (hlower : 0 < lowerBase)
    (hlt : lowerBase <
      (2 : ℝ) ^ ((WordType.profileMass a : ℝ) * WordType.profileEntropyBits a)) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ n : ℕ, n + 1 = WordType.profileMass a * k →
      HasTauWeight K
        ((((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts a k))
          (ofLegs (V := fun _ : Leg ↦ PositiveWord (Fin 5) n)
            (positiveWordConst (0 : Fin 5) n) (positiveWordConst (2 : Fin 5) n)
            (positiveWordConst (2 : Fin 5) n))).realize) τ
        ((lowerBase ^ k *
          ((q ^ (∑ p : PositiveWord CWBlock 1,
            WordType.proportionalCounts a k p * cwWordMiddleCount 1 p) : ℕ) : ℝ)) ^ τ) := by
  classical
  obtain ⟨cutoff, hcutoff⟩ :=
    WordType.exists_cutoff_forall_pow_le_card_proportionalTypeClass a hmass hlower hlt
  refine ⟨cutoff, fun k hk n hn ↦ ?_⟩
  -- abbreviations
  set αk : PositiveWord CWBlock 1 → ℕ := WordType.proportionalCounts a k with hαk
  set target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n) :=
    ofLegs (V := fun _ : Leg ↦ PositiveWord (Fin 5) n)
      (positiveWordConst (0 : Fin 5) n) (positiveWordConst (2 : Fin 5) n)
      (positiveWordConst (2 : Fin 5) n) with htargetDef
  set cell := ((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
    cwSquareDegreeMap n 1 (fun _ ↦ 0)
    (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ αk)) target with hcellDef
  set ones := ∑ p : PositiveWord CWBlock 1, αk p * cwWordMiddleCount 1 p with honesDef
  -- the degree hypothesis passes to the proportional refinement
  have hαkdeg : ∀ p : PositiveWord CWBlock 1, αk p ≠ 0 → cwSquareBlockDegree p = 2 := by
    intro p hp
    refine ha p ?_
    intro hzero
    rw [hαk, WordType.proportionalCounts, hzero, Nat.zero_mul] at hp
    exact hp rfl
  -- the two cardinality steps
  have hclass : lowerBase ^ k ≤
      (((WordType.typeClass (WordType.profileMass a * k) αk).card : ℕ) : ℝ) := hcutoff k hk
  have hinj : (WordType.typeClass (n + 1) αk).card ≤ cell.support.card := by
    rw [hcellDef, htargetDef]
    exact dwz63_card_typeClass_le_zeroXFineCellSupport K q n αk hαkdeg
  have hfibre : lowerBase ^ k ≤ ((cell.support.card : ℕ) : ℝ) := by
    refine hclass.trans ?_
    have : (WordType.typeClass (WordType.profileMass a * k) αk).card ≤ cell.support.card := by
      rw [← hn]; exact hinj
    exact Nat.cast_le.mpr this
  -- the fibre is inhabited
  have hpos : 0 < ((cell.support.card : ℕ) : ℝ) :=
    lt_of_lt_of_le (pow_pos hlower k) hfibre
  have hne : cell.support.Nonempty := by
    refine Finset.card_pos.mp ?_
    exact Nat.cast_pos.mp hpos
  -- the two fusion hypotheses
  have hzero : ∀ s ∈ cell.support,
      s Leg.X = positiveWordConst (positiveWordConst CWBlock.zero 1) n := by
    intro s hs
    refine dwz63_cellPower_zeroLeg_eq_const K q n Leg.X αk target ?_ s ?_
    · rw [htargetDef, ofLegs_X]
    · rw [hcellDef] at hs; exact hs
  have hones : ∀ s ∈ cell.support, dwz63CellOnes Leg.X n s = ones := by
    intro s hs
    refine dwz63_cellPower_cellOnes_eq_alphaSum_of_secondLive K q n Leg.X rfl αk target ?_ s ?_
    · rw [htargetDef, ofLegs_X]
    · rw [hcellDef] at hs; exact hs
  -- the weight, with the fibre cardinality still symbolic
  have hweight := dwz63_hasTauWeight_fineCellPower K q Leg.X n ones τ
    (segmentedLocalizedKeep cwSquareDegreeMap (fun _ : Fin (n + 1) ↦ (0 : Fin 1))
      (SegmentedSplitRestriction.ofLeg
        (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ αk)) target)
    hq hne hzero hones
  -- and the comparison
  refine hweight.mono ?_
  refine Real.rpow_le_rpow (by positivity) ?_ hτ
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right hfibre (by positivity)

end AlgebraicComplexity.Examples
