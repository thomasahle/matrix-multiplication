/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellZeroZ
import AlgebraicComplexity.Tensor.PositiveWordAppendConst

set_option autoImplicit false

/-!
# The eleven cell weights at one common period

Layer 4 (`AlgebraicComplexity/Examples/`).  Each cell weight of
`Examples/DuanWuZhouLevelTwoFineCellRegional.lean` and
`Examples/DuanWuZhouLevelTwoFineCellZeroZ.lean` holds at its own period `2 * 10 ^ 8 * j`.  A
regional client needs them all at **one** global period, because region `t` of the section 6.3 leaf
holds exactly `dwz63Alpha t * scale` positions when the reference coarse word has length
`10 ^ 8 * scale` (`card_fiber_dwz63Seg`, `Examples/DuanWuZhouLevelTwoSegmentationData.lean:88`:
the size of segment `t` is the multiplicity of cell `t` in the word).

## The scaling, and why `2 * 10 ^ 8` is minimal

Region `t` must be a whole number of periods of the row mass `2 * 10 ^ 8`, i.e.
`2 * 10 ^ 8 ∣ dwz63Alpha t * scale` for every `t`.  The greatest common divisor of the fifteen
entries of `dwz63Alpha` is `1` --- `gcd(20860, 1211153) = 1` already, since `1211153` is odd and
`20860 = 2 ^ 2 * 5 * 7 * 149` --- so no common factor helps and the minimal choice is

`scale = 2 * 10 ^ 8 * s`.

Then region `t` holds `dwz63Alpha t * 2 * 10 ^ 8 * s` positions, which is `2 * 10 ^ 8` times the
per-cell repetition count

`j_t = dwz63Alpha t * s`,

and that is what the eleven restatements below are indexed by.  A region spec for cell `t` is then
`size = n` with `n + 1 = 2 * 10 ^ 8 * (dwz63Alpha t * s)`.

## What the leaf assigns to segment `t`

`SegmentedSplitRestriction.Keeps` (`MatrixMultiplication/SegmentedSplitRestriction.lean:117`) reads
`segmentMultiplicity seg word t = alphaTilde t`, so the leaf's per-segment datum is an **absolute**
integral profile whose mass must equal the segment's size --- not a rate.  At the joined period the
segment-`t` profile is therefore

`WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s)`,

of mass `2 * 10 ^ 8 * dwz63Alpha t * s`, matching the region size exactly.  That is the term the
statements below carry, so a client instantiating `dwz63SegmentedFineFiber`'s `alphaTilde`
argument uses `fun t ↦ WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s)` and
nothing else.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3, `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

variable (K : Type u) [CommRing K]

/-- The `(0,0,4)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 0 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 0 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 0) (dwz63Alpha 0 * s)))
          (dwz63ZeroCellTarget Leg.X 4 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 0 * s : ℕ) : ℝ) *
          (dwz63LogVal004 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_zero (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 0 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 0 = 20860 from rfl]; norm_num))

/-- The `(0,1,3)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 1 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_one (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 1 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 1) (dwz63Alpha 1 * s)))
          (dwz63ZeroCellTarget Leg.X 3 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 1 * s : ℕ) : ℝ) *
          (dwz63LogVal013 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_one (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 1 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 1 = 1211153 from rfl]; norm_num))

/-- The `(0,2,2)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 2 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_two (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 2 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 2) (dwz63Alpha 2 * s)))
          (dwz63ZeroCellTarget Leg.X 2 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 2 * s : ℕ) : ℝ) *
          (dwz63LogVal022 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_two (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 2 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 2 = 10366945 from rfl]; norm_num))

/-- The `(0,3,1)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 3 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_three (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 3 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 3) (dwz63Alpha 3 * s)))
          (dwz63ZeroCellTarget Leg.X 1 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 3 * s : ℕ) : ℝ) *
          (dwz63LogVal013 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_three (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 3 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 3 = 1333318 from rfl]; norm_num))

/-- The `(0,4,0)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 4 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_four (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 4 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 4) (dwz63Alpha 4 * s)))
          (dwz63ZeroCellTarget Leg.X 0 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 4 * s : ℕ) : ℝ) *
          (dwz63LogVal004 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_four (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 4 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 4 = 24731 from rfl]; norm_num))

/-- The `(1,0,3)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 5 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_five (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 5 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 5) (dwz63Alpha 5 * s)))
          (dwz63ZeroCellTarget Leg.Y 3 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 5 * s : ℕ) : ℝ) *
          (dwz63LogVal013 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_five (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 5 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 5 = 1211153 from rfl]; norm_num))

/-- The `(1,3,0)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 8 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_eight (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 8 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 8) (dwz63Alpha 8 * s)))
          (dwz63ZeroCellTarget Leg.Z 3 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 8 * s : ℕ) : ℝ) *
          (dwz63LogVal013 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_eight (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 8 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 8 = 1251758 from rfl]; norm_num))

/-- The `(2,0,2)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 9 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_nine (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 9 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 9) (dwz63Alpha 9 * s)))
          (dwz63ZeroCellTarget Leg.Y 2 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 9 * s : ℕ) : ℝ) *
          (dwz63LogVal022 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_nine (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 9 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 9 = 10366945 from rfl]; norm_num))

/-- The `(3,0,1)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 12 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_twelve (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 12 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 12) (dwz63Alpha 12 * s)))
          (dwz63ZeroCellTarget Leg.Y 1 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 12 * s : ℕ) : ℝ) *
          (dwz63LogVal013 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_twelve (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 12 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 12 = 1333318 from rfl]; norm_num))

/-- The `(3,1,0)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 13 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_thirteen (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 13 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 13) (dwz63Alpha 13 * s)))
          (dwz63ZeroCellTarget Leg.Z 1 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 13 * s : ℕ) : ℝ) *
          (dwz63LogVal013 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_thirteen (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 13 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 13 = 1251758 from rfl]; norm_num))

/-- The `(4,0,0)` cell at the joined period `2 * 10 ^ 8 * (dwz63Alpha 14 * s)`. -/
theorem dwz63_exists_joinedFineCellWeight_fourteen (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ n : ℕ, n + 1 = 200000000 * (dwz63Alpha 14 * s) →
      HasTauWeight K
        ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts (dwz63AlphaTilde 14) (dwz63Alpha 14 * s)))
          (dwz63ZeroCellTarget Leg.Y 0 n)).realize) dwz63Tau
        (Real.exp ((200000000 : ℝ) * ((dwz63Alpha 14 * s : ℕ) : ℝ) *
          (dwz63LogVal004 - ε))) := by
  obtain ⟨N, hN⟩ := dwz63_exists_fineCellWeight_fourteen (K := K) ε hε
  refine ⟨N, fun s hs n hn ↦ hN (dwz63Alpha 14 * s) ?_ n hn⟩
  exact le_trans hs
    (Nat.le_mul_of_pos_left s (by rw [show dwz63Alpha 14 = 24731 from rfl]; norm_num))


/-! ## Splitting a cell's coarse target -/

/-- **A cell's coarse target concatenates.**  `dwz63ZeroCellTarget` is `ofLegs` of three constant
words, so the `htarget` obligation of a regional division --- `target c = positiveWordAppend
(targetHead c) _ (targetTail c)` --- is the generic `Tensor.ofLegs_positiveWordAppend_const`. -/
theorem dwz63_zeroCellTarget_append (zero : Leg) (k : Fin 5) (n₁ n₂ : ℕ) (c : Leg) :
    dwz63ZeroCellTarget zero k (n₁ + n₂ + 1) c =
      positiveWordAppend (dwz63ZeroCellTarget zero k n₁ c) n₂
        (dwz63ZeroCellTarget zero k n₂ c) := by
  cases zero <;> exact Tensor.ofLegs_positiveWordAppend_const _ _ _ n₁ n₂ c

end AlgebraicComplexity.Examples
