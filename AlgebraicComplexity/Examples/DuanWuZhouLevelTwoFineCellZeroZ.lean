/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellRegional

set_option autoImplicit false

/-!
# The two cells whose zero coordinate is the split leg: `(1,3,0)` and `(3,1,0)`

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoFineCellGeneral.lean`
handles every cell whose zero coordinate lies **off** the split leg `Z`.  Two of the remaining
three, `(1,3,0)` (index `8`) and `(3,1,0)` (index `13`), have their zero coordinate **on** `Z`, and
they are easier rather than harder: their `alphatilde` row is concentrated on the zero pair, so the
split constraint is vacuous and the fibre is *free*.

## Why the count is exact and no deficit is needed

With `Z` forced to the constant zero pair, each position's `X` letter is a pair of degree `4 - k`
and its `Y` letter is the forced complement.  For `(1,3,0)` the `X` degree is `1`, so the `X` letter
is `(zero, middle)` or `(middle, zero)`; for `(3,1,0)` it is `3`, so `(middle, last)` or
`(last, middle)`.  Either way there are exactly **two** choices per position and each carries
exactly **one** middle digit.  Hence

* `2 ^ (n+1) ≤ |fibre|` --- an explicit injection from `Fin (n+1) → Bool`, not a type class, so
  no
  multinomial and no entropy appear; and
* the one-slice exponent is the constant `n + 1`, by the committed
  `cwWordMiddleCount_of_degree_ne_two` (degrees `1` and `3` force exactly one middle).

The fused dimension is therefore `2 ^ (n+1) * q ^ (n+1) = 12 ^ (n+1)` at `q = 6`, and
`tau * log (2q) = dwz63LogVal013` **exactly** --- the identity already proved as
`dwz63_tau_mul_rate_eq_alphaTilde_one` (`Examples/DuanWuZhouLevelTwoFineCellRows.lean`), which is
why these two cells need no `eps`.  An `eps`-form instance is supplied all the same, so that every
cell of the leaf presents one shape to a regional client.

## The target spelling

`dwz63ZeroCellTarget Leg.Z k n` is `ofLegs (const (4-k)) (const k) (const 0)`, so `(1,3,0)` is
`k = 3` and `(3,1,0)` is `k = 1`.  The `Leg.Z` branch of that definition --- written when the
zero-`Z` case looked irrelevant --- is exactly right here.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3, `lem:non-rot-values` (b).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## The witness, read on the two live legs -/

/-- In the zero-`Z` frame the free word sits on `Y`. -/
theorem dwz63_zeroFineWitness_Y_of_Z (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) :
    positiveWordEquiv (PositiveWord CWBlock 1) n
      (dwz63ZeroFineWitness K q Leg.Z n zw Leg.Y) = zw := by
  rw [dwz63_zeroFineWitness_equiv]
  rfl

/-- The zero-`Z` witness coarsens to the cell's target. -/
theorem dwz63_zeroFineWitness_coarsens_Z (k : Fin 5) (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1)
    (hdeg : ∀ i, cwSquareBlockDegree (zw i) = k) (c : Leg) :
    positiveWordMap (cwSquareDegreeMap c) n (dwz63ZeroFineWitness K q Leg.Z n zw c) =
      dwz63ZeroCellTarget Leg.Z k n c := by
  have hzeroPair : cwSquareBlockDegree (positiveWordConst CWBlock.zero 1) = (0 : Fin 5) := by
    decide
  have hcomp : ∀ i, cwSquareBlockDegree (dwz63PairComplement (zw i)) = 4 - k := by
    intro i
    have h := dwz63_squareBlockDegree_pairComplement (zw i).1 (zw i).2
    rw [show (((zw i).1, (zw i).2) : PositiveWord CWBlock 1) = zw i from rfl] at h
    rw [h, hdeg i]
  refine (positiveWordEquiv (Fin 5) n).injective ?_
  rw [positiveWordEquiv_map, dwz63_zeroFineWitness_equiv]
  cases c
  · rw [show dwz63ZeroCellTarget Leg.Z k n Leg.X = positiveWordConst (4 - k) n from rfl,
      positiveWordEquiv_const]
    funext i; exact hcomp i
  · rw [show dwz63ZeroCellTarget Leg.Z k n Leg.Y = positiveWordConst k n from rfl,
      positiveWordEquiv_const]
    funext i; exact hdeg i
  · rw [show dwz63ZeroCellTarget Leg.Z k n Leg.Z = positiveWordConst (0 : Fin 5) n from rfl,
      positiveWordEquiv_const]
    funext i; exact hzeroPair

/-! ## The free fibre has at least `2 ^ (n+1)` elements -/

/-- **The two-letter injection.**  Every word over a two-element set of degree-`k` letters is the
`Y` leg of a supported address of the cell, so the fibre has at least `2 ^ (n+1)` elements.  No
type class and no multinomial: the fibre is free. -/
theorem dwz63_two_pow_le_zeroZFineCellSupport (k : Fin 5) (n : ℕ)
    (p₀ p₁ : PositiveWord CWBlock 1) (hne : p₀ ≠ p₁)
    (hd0 : cwSquareBlockDegree p₀ = k) (hd1 : cwSquareBlockDegree p₁ = k)
    (α : PositiveWord CWBlock 1 → ℕ)
    (hα : α = fun p ↦ if p = ((CWBlock.zero, CWBlock.zero) : PositiveWord CWBlock 1)
      then n + 1 else 0) :
    2 ^ (n + 1) ≤
      (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
        (dwz63ZeroCellTarget Leg.Z k n)).support.card := by
  classical
  have hcard : (Finset.univ : Finset (Fin (n + 1) → Bool)).card = 2 ^ (n + 1) := by
    simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun b ↦ dwz63ZeroFineWitness K q Leg.Z n (fun i ↦ if b i then p₁ else p₀)) ?_ ?_
  · intro b _
    have hdeg : ∀ i, cwSquareBlockDegree (if b i then p₁ else p₀) = k := by
      intro i
      by_cases h : b i
      · rw [if_pos h]; exact hd1
      · rw [if_neg h]; exact hd0
    have htype : WordType.multiplicity (positiveWordEquiv (PositiveWord CWBlock 1) n
        (dwz63ZeroFineWitness K q Leg.Z n (fun i ↦ if b i then p₁ else p₀) Leg.Z)) = α := by
      rw [dwz63_zeroFineWitness_zero, positiveWordEquiv_const, hα]
      funext p
      exact WordType.multiplicity_const (n + 1) _ p
    have hmem : dwz63ZeroFineWitness K q Leg.Z n (fun i ↦ if b i then p₁ else p₀) ∈
        (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
          (dwz63ZeroCellTarget Leg.Z k n)).support := by
      rw [dwz63_mem_cellPower_support_iff]
      exact ⟨dwz63_zeroFineWitness_mem K q Leg.Z n _,
        fun c ↦ dwz63_zeroFineWitness_coarsens_Z K q k n _ hdeg c, htype⟩
    simpa using hmem
  · intro b _ b' _ heq
    have h := congrArg
      (fun s ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (s Leg.Y)) heq
    rw [dwz63_zeroFineWitness_Y_of_Z, dwz63_zeroFineWitness_Y_of_Z] at h
    funext i
    have hi := congrFun h i
    by_cases hb : b i <;> by_cases hb' : b' i
    · rw [hb, hb']
    · rw [if_pos hb, if_neg hb'] at hi; exact absurd hi.symm hne
    · rw [if_neg hb, if_pos hb'] at hi; exact absurd hi hne
    · simp [hb, hb']


/-! ## The one-slice exponent is the constant `n + 1` -/

/-- **`huniform` in the zero-`Z` frame.**  Every `X` letter has coarse degree `4 - k`, and degrees
`1` and `3` force exactly one middle digit (`cwWordMiddleCount_of_degree_ne_two`), so the exponent
is `1 * (n+1)`. -/
theorem dwz63_cellPower_cellOnes_of_zeroZ (k : Fin 5) (n : ℕ)
    (hxdeg : (4 : Fin 5) - k = 1 ∨ (4 : Fin 5) - k = 3)
    (α : PositiveWord CWBlock 1 → ℕ)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
        (dwz63ZeroCellTarget Leg.Z k n)).support) :
    dwz63CellOnes Leg.Z n s = n + 1 := by
  classical
  obtain ⟨hmem, hcoarse, _htype⟩ :=
    (dwz63_mem_cellPower_support_iff K q n α (dwz63ZeroCellTarget Leg.Z k n) s).mp hs
  obtain ⟨w, hw⟩ :=
    ((cwPartitionedTensor K q).positivePower
      1).exists_positiveSupportWord_of_mem_positivePower_support n hmem
  subst hw
  have hne2 : (4 : Fin 5) - k ≠ 2 := by rcases hxdeg with h | h <;> rw [h] <;> decide
  have hXdeg : ∀ position, cwSquareBlockDegree
      ((positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support n w position).1
        Leg.X) = 4 - k := by
    intro position
    have h := congrArg (positiveWordEquiv (Fin 5) n) (hcoarse Leg.X)
    rw [positiveWordEquiv_map,
      show dwz63ZeroCellTarget Leg.Z k n Leg.X = positiveWordConst (4 - k) n from rfl,
      positiveWordEquiv_const] at h
    have hp := congrFun h position
    rw [Function.comp_apply,
      show positiveWordEquiv (PositiveWord CWBlock 1) n
          (positiveSupportWordBlockAddress
            ((cwPartitionedTensor K q).positivePower 1).support n w Leg.X) position =
        (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support n w position).1
          Leg.X from
        congrFun (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
          ((cwPartitionedTensor K q).positivePower 1).support n w Leg.X) position] at hp
    exact hp
  have hone : ∀ position, cwWordMiddleCount 1
      ((positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support n w position).1
        (firstLiveLeg Leg.Z)) = 1 := by
    intro position
    have hd : cwSquareBlockDegree
        ((positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support n w position).1
          (firstLiveLeg Leg.Z)) = 4 - k := hXdeg position
    rw [cwWordMiddleCount_of_degree_ne_two _ (by rw [hd]; exact hne2), if_pos]
    rw [hd]
    exact hxdeg
  rw [dwz63_cellOnes_of_letterwise_const K q Leg.Z n 1 w hone, one_mul]

/-! ## The fused weight -/

/-- **The zero-`Z` cell's weight at the exact fused dimension `2 ^ (n+1) * q ^ (n+1)`.** -/
theorem dwz63_hasTauWeight_zeroZFineCell (k : Fin 5) (n : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
  (hq : 0 < q)
    (hxdeg : (4 : Fin 5) - k = 1 ∨ (4 : Fin 5) - k = 3)
    (p₀ p₁ : PositiveWord CWBlock 1) (hne : p₀ ≠ p₁)
    (hd0 : cwSquareBlockDegree p₀ = k) (hd1 : cwSquareBlockDegree p₁ = k)
    (α : PositiveWord CWBlock 1 → ℕ)
    (hα : α = fun p ↦ if p = ((CWBlock.zero, CWBlock.zero) : PositiveWord CWBlock 1)
      then n + 1 else 0) :
    HasTauWeight K
      ((((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
        (dwz63ZeroCellTarget Leg.Z k n)).realize) τ
      (((2 ^ (n + 1) * q ^ (n + 1) : ℕ) : ℝ) ^ τ) := by
  classical
  have hbound := dwz63_two_pow_le_zeroZFineCellSupport K q k n p₀ p₁ hne hd0 hd1 α hα
  have hpos : 0 < (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
      cwSquareDegreeMap n 1 (fun _ ↦ 0)
      (SegmentedSplitRestriction.ofLeg
        (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
      (dwz63ZeroCellTarget Leg.Z k n)).support.card :=
    lt_of_lt_of_le (Nat.pow_pos (by norm_num : 0 < 2)) hbound
  have hnonempty := Finset.card_pos.mp hpos
  have hzeroLeg := fun s hs ↦ dwz63_cellPower_zeroLeg_eq_const K q n Leg.Z α
    (dwz63ZeroCellTarget Leg.Z k n) (dwz63ZeroCellTarget_self Leg.Z k n) s hs
  have hones := fun s hs ↦ dwz63_cellPower_cellOnes_of_zeroZ K q k n hxdeg α s hs
  have hweight := dwz63_hasTauWeight_fineCellPower K q Leg.Z n (n + 1) τ
    (segmentedLocalizedKeep cwSquareDegreeMap (fun _ : Fin (n + 1) ↦ (0 : Fin 1))
      (SegmentedSplitRestriction.ofLeg
        (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
      (dwz63ZeroCellTarget Leg.Z k n))
    hq hnonempty hzeroLeg hones
  refine hweight.mono ?_
  refine Real.rpow_le_rpow (by positivity) ?_ hτ
  exact_mod_cast Nat.mul_le_mul_right _ hbound


/-! ## The two cells -/

/-- The `(1,3,0)` and `(3,1,0)` split rows are the point mass at the zero pair, so at period
`n + 1 = 2 * 10 ^ 8 * j` their proportional refinement is the point mass of total weight `n + 1`. -/
theorem dwz63_proportionalCounts_zeroPair (t : Fin 15)
    (hrow : ∀ x y : CWBlock, dwz63AlphaTilde t ((x, y) : PositiveWord CWBlock 1) =
      if ((x, y) : PositiveWord CWBlock 1) =
        ((CWBlock.zero, CWBlock.zero) : PositiveWord CWBlock 1) then 200000000 else 0)
    (n j : ℕ) (hn : n + 1 = 200000000 * j) :
    WordType.proportionalCounts (dwz63AlphaTilde t) j =
      fun p ↦ if p = ((CWBlock.zero, CWBlock.zero) : PositiveWord CWBlock 1) then n + 1 else 0 :=
        by
  funext p
  rcases p with ⟨x, y⟩
  show dwz63AlphaTilde t ((x, y) : PositiveWord CWBlock 1) * j = _
  rw [hrow x y]
  split <;> simp [hn]

/-- The `(1,3,0)` row is the point mass at the zero pair. -/
theorem dwz63_alphaTildeRow_eight (x y : CWBlock) :
    dwz63AlphaTilde 8 ((x, y) : PositiveWord CWBlock 1) =
      if ((x, y) : PositiveWord CWBlock 1) =
        ((CWBlock.zero, CWBlock.zero) : PositiveWord CWBlock 1) then 200000000 else 0 := by
  cases x <;> cases y <;> rfl

/-- The `(3,1,0)` row is the point mass at the zero pair. -/
theorem dwz63_alphaTildeRow_thirteen (x y : CWBlock) :
    dwz63AlphaTilde 13 ((x, y) : PositiveWord CWBlock 1) =
      if ((x, y) : PositiveWord CWBlock 1) =
        ((CWBlock.zero, CWBlock.zero) : PositiveWord CWBlock 1) then 200000000 else 0 := by
  cases x <;> cases y <;> rfl

/-- **The exact value of the fused zero-`Z` dimension**: `2 ^ (n+1) * q ^ (n+1) = 12 ^ (n+1)` at
`q = 6`, and `tau * log 12 = dwz63LogVal013`.  No deficit. -/
theorem dwz63_zeroZFineCell_value_eq (n : ℕ) :
    (((2 ^ (n + 1) * dwz63Q ^ (n + 1) : ℕ) : ℝ) ^ dwz63Tau) =
      Real.exp (((n + 1 : ℕ) : ℝ) * dwz63LogVal013) := by
  have h12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 * (2 * 3) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hnat : ((2 ^ (n + 1) * dwz63Q ^ (n + 1) : ℕ) : ℝ) = (12 : ℝ) ^ (n + 1) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      show ((dwz63Q : ℕ) : ℝ) = 6 by norm_num [dwz63Q], ← mul_pow]
    norm_num
  have hexp : (12 : ℝ) ^ (n + 1) = Real.exp (((n + 1 : ℕ) : ℝ) * Real.log 12) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [hnat, hexp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, dwz63LogVal013, h12]
  congr 1
  ring

/-- **The `(1,3,0)` cell**, at exactly `exp ((n+1) * dwz63LogVal013)`. -/
theorem dwz63_hasTauWeight_fineCell130 (n j : ℕ) (hn : n + 1 = 200000000 * j) :
    HasTauWeight K
      ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
          (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 8) j))
        (dwz63ZeroCellTarget Leg.Z 3 n)).realize) dwz63Tau
      (Real.exp (((n + 1 : ℕ) : ℝ) * dwz63LogVal013)) := by
  rw [← dwz63_zeroZFineCell_value_eq]
  exact dwz63_hasTauWeight_zeroZFineCell K dwz63Q 3 n dwz63Tau
    (by norm_num [dwz63Tau]) (by norm_num [dwz63Q]) (by decide)
    ((CWBlock.middle, CWBlock.last) : PositiveWord CWBlock 1)
    ((CWBlock.last, CWBlock.middle) : PositiveWord CWBlock 1)
    (fun h ↦ absurd (congrArg Prod.fst h) (by decide)) (by decide) (by decide) _
    (dwz63_proportionalCounts_zeroPair 8 dwz63_alphaTildeRow_eight n j hn)

/-- **The `(3,1,0)` cell**, at exactly `exp ((n+1) * dwz63LogVal013)`. -/
theorem dwz63_hasTauWeight_fineCell310 (n j : ℕ) (hn : n + 1 = 200000000 * j) :
    HasTauWeight K
      ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
          (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 13) j))
        (dwz63ZeroCellTarget Leg.Z 1 n)).realize) dwz63Tau
      (Real.exp (((n + 1 : ℕ) : ℝ) * dwz63LogVal013)) := by
  rw [← dwz63_zeroZFineCell_value_eq]
  exact dwz63_hasTauWeight_zeroZFineCell K dwz63Q 1 n dwz63Tau
    (by norm_num [dwz63Tau]) (by norm_num [dwz63Q]) (by decide)
    ((CWBlock.zero, CWBlock.middle) : PositiveWord CWBlock 1)
    ((CWBlock.middle, CWBlock.zero) : PositiveWord CWBlock 1)
    (fun h ↦ absurd (congrArg Prod.fst h) (by decide)) (by decide) (by decide) _
    (dwz63_proportionalCounts_zeroPair 13 dwz63_alphaTildeRow_thirteen n j hn)

/-- The `eps`-form, so that every cell of the leaf presents one shape to a regional client.  The
count here is exact, so the deficit is pure slack. -/
theorem dwz63_exists_fineCellWeight_eight (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 8) j))
          (dwz63ZeroCellTarget Leg.Z 3 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal013 - ε))) := by
  refine ⟨0, fun j _ n hn ↦ (dwz63_hasTauWeight_fineCell130 K n j hn).mono ?_⟩
  refine Real.exp_le_exp.mpr ?_
  have hcast : ((n + 1 : ℕ) : ℝ) = (200000000 : ℝ) * (j : ℝ) := by
    rw [hn]; push_cast; ring
  rw [hcast]
  have hslack : (0 : ℝ) ≤ 200000000 * (j : ℝ) * ε := by positivity
  nlinarith [hslack]

/-- The `eps`-form for `(3,1,0)`. -/
theorem dwz63_exists_fineCellWeight_thirteen (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = 200000000 * j →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 13) j))
          (dwz63ZeroCellTarget Leg.Z 1 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * (j : ℝ) * (dwz63LogVal013 - ε))) := by
  refine ⟨0, fun j _ n hn ↦ (dwz63_hasTauWeight_fineCell310 K n j hn).mono ?_⟩
  refine Real.exp_le_exp.mpr ?_
  have hcast : ((n + 1 : ℕ) : ℝ) = (200000000 : ℝ) * (j : ℝ) := by
    rw [hn]; push_cast; ring
  rw [hcast]
  have hslack : (0 : ℝ) ≤ 200000000 * (j : ℝ) * ε := by positivity
  nlinarith [hslack]

end AlgebraicComplexity.Examples
