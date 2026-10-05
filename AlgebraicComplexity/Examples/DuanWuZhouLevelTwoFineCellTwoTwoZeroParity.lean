/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellUniform
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellGeneral

set_option autoImplicit false

/-!
# Degree two: the one-slice exponent of a fine cell is even

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoFineCellUniform.lean`
records that the middle count of a fine letter is a function of its coarse degree **except at
degree two**, and settles `huniform` for the degrees where it is.  This module supplies the missing
row of that table and its consequence for a whole cell word.

At coarse degree `2` the admissible pairs are `(0,2)`, `(1,1)` and `(2,0)`, with middle counts
`0`, `2` and `0`.  The count therefore varies --- that is exactly why `[duan2023faster]` has to
prescribe a split distribution at `k = 2` --- but it varies only over the **even** values `0` and
`2`.  Summing over the `n + 1` positions of a cell word, the one-slice exponent `dwz63CellOnes` of
any address of a cell whose first-live-leg coarse degree is constantly `2` is an even number in
`[0, 2(n+1)]`.

## Why this is the shape the merge needs

`ZeroCoordinateMerge.exists_uniform_fibre_mergedDimension_le` charges a uniform sub-class the
number of values its exponent takes on the class, and its value set is `Finset.range (bound + 1)`.
Handing it the naive `bound = 2(n+1)` costs `2n + 3`; halving the exponent --- legitimate exactly
because it is even --- and running the merge at base `q ^ 2` costs `n + 2` instead.  So the two
facts the merge consumes are

* `dwz63_two_mul_cellOnes_div_two_of_target_two`, which turns `q ^ ones` into `(q ^ 2) ^ (ones / 2)`
  with no rounding, and
* `dwz63_cellOnes_div_two_mem_range_of_target_two`, the halved value set.

Both are stated at a general zero leg with the coarse degree of `firstLiveLeg zero` fixed to `2`,
so they cover `(2,2,0)` (`zero = .Z`, the one cell whose zero coordinate is on the split leg) as
well as the `(0,2,2)` and `(2,0,2)` frames.  The `(2,2,0)` instances are spelled out at the end
against the committed cell target `dwz63ZeroCellTarget Leg.Z 2 n`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `hole_lemma.tex`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/hole_lemma.tex:1-168` (whole file).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-! ## The missing row of the degree table -/

/-- **At coarse degree two the middle count is `0` or `2`.**  The complement of
`cwWordMiddleCount_of_degree_ne_two`: the three admissible pairs `(0,2)`, `(1,1)`, `(2,0)` have
middle counts `0`, `2`, `0`.  A degree-two letter therefore never has an odd middle count, even
though the count is not determined by the degree. -/
theorem cwWordMiddleCount_eq_zero_or_two_of_degree_two (p : PositiveWord CWBlock 1)
    (h : cwSquareBlockDegree p = 2) :
    cwWordMiddleCount 1 p = 0 ∨ cwWordMiddleCount 1 p = 2 := by
  obtain ⟨a, b⟩ := p
  revert h
  cases a <;> cases b <;> decide

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## Letterwise degrees on a cell -/

/-- **Every letter of a kept address has the target's coarse degree.**  The coarsening half of
`segmentedLocalizedKeep`, read one position at a time.  No hypothesis on the split profile `α` is
used: this is the coarse constraint alone. -/
theorem dwz63_cellPower_letter_squareBlockDegree (n : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (c : Leg) (d : Fin 5) (htarget : target c = positiveWordConst d n)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support)
    (position : Fin (n + 1)) :
    cwSquareBlockDegree
      (positiveWordEquiv (PositiveWord CWBlock 1) n (s c) position) = d := by
  obtain ⟨-, hcoarse, -⟩ := (dwz63_mem_cellPower_support_iff K q n α target s).mp hs
  have h := congrFun (congrArg (positiveWordEquiv (Fin 5) n) (hcoarse c)) position
  rw [positiveWordEquiv_map, htarget, positiveWordEquiv_const] at h
  simpa [cwSquareDegreeMap] using h

/-- **Letterwise `0` or `2` on the counted leg.**  The instance of
`cwWordMiddleCount_eq_zero_or_two_of_degree_two` at the letters `dwz63CellOnes` totals. -/
theorem dwz63_cellPower_wordMiddleCount_eq_zero_or_two (zero : Leg) (n : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target (firstLiveLeg zero) = positiveWordConst (2 : Fin 5) n)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support)
    (position : Fin (n + 1)) :
    cwWordMiddleCount 1
        (positiveWordEquiv (PositiveWord CWBlock 1) n (s (firstLiveLeg zero)) position) = 0 ∨
      cwWordMiddleCount 1
        (positiveWordEquiv (PositiveWord CWBlock 1) n (s (firstLiveLeg zero)) position) = 2 :=
  cwWordMiddleCount_eq_zero_or_two_of_degree_two _
    (dwz63_cellPower_letter_squareBlockDegree K q n α target (firstLiveLeg zero) 2 htarget s hs
      position)

/-! ## The exponent of a whole cell word -/

/-- **The one-slice exponent of a degree-two cell is even.**  Every letter contributes `0` or `2`,
so `2` divides the total. -/
theorem dwz63_two_dvd_cellOnes_of_target_two (zero : Leg) (n : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target (firstLiveLeg zero) = positiveWordConst (2 : Fin 5) n)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support) :
    2 ∣ dwz63CellOnes zero n s := by
  refine Finset.dvd_sum ?_
  intro position _
  rcases dwz63_cellPower_wordMiddleCount_eq_zero_or_two K q zero n α target htarget s hs
    position with h | h <;> simp [h]

/-- **The evenness fact.**  `Even (dwz63CellOnes zero n s)` on every address of a cell whose
first-live-leg coarse degree is constantly `2`. -/
theorem dwz63_even_cellOnes_of_target_two (zero : Leg) (n : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target (firstLiveLeg zero) = positiveWordConst (2 : Fin 5) n)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support) :
    Even (dwz63CellOnes zero n s) := by
  obtain ⟨k, hk⟩ := dwz63_two_dvd_cellOnes_of_target_two K q zero n α target htarget s hs
  exact ⟨k, by omega⟩

/-- **The exponent is at most twice the number of positions.**  `PositiveWord … n` carries `n + 1`
letters and each contributes at most `2`. -/
theorem dwz63_cellOnes_le_of_target_two (zero : Leg) (n : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target (firstLiveLeg zero) = positiveWordConst (2 : Fin 5) n)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support) :
    dwz63CellOnes zero n s ≤ 2 * (n + 1) := by
  have hbound : dwz63CellOnes zero n s ≤ ∑ _position : Fin (n + 1), 2 := by
    refine Finset.sum_le_sum ?_
    intro position _
    rcases dwz63_cellPower_wordMiddleCount_eq_zero_or_two K q zero n α target htarget s hs
      position with h | h <;> simp [h]
  simpa [Finset.sum_const, Finset.card_univ, mul_comm] using hbound

/-! ## The two forms the merge consumes -/

/-- **Halving the exponent loses nothing.**  `q ^ ones = (q ^ 2) ^ (ones / 2)` follows from this
by `pow_mul`. -/
theorem dwz63_two_mul_cellOnes_div_two_of_target_two (zero : Leg) (n : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target (firstLiveLeg zero) = positiveWordConst (2 : Fin 5) n)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support) :
    2 * (dwz63CellOnes zero n s / 2) = dwz63CellOnes zero n s :=
  Nat.mul_div_cancel' (dwz63_two_dvd_cellOnes_of_target_two K q zero n α target htarget s hs)

/-- **The halved value set has `n + 2` elements.**  This is the `hmaps` premise of
`ZeroCoordinateMerge.exists_uniform_fibre_mergedDimension_le` at `bound = n + 1`, so the merge loss
is `(Finset.range (n + 2)).card` rather than the naive `2n + 3`. -/
theorem dwz63_cellOnes_div_two_mem_range_of_target_two (zero : Leg) (n : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target (firstLiveLeg zero) = positiveWordConst (2 : Fin 5) n)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support) :
    dwz63CellOnes zero n s / 2 ∈ Finset.range (n + 1 + 1) := by
  have h := dwz63_cellOnes_le_of_target_two K q zero n α target htarget s hs
  exact Finset.mem_range.mpr (by omega)

/-! ## The `(2,2,0)` cell

`dwz63ZeroCellTarget Leg.Z 2 n` is `ofLegs (const 2) (const 2) (const 0)`
(`Examples/DuanWuZhouLevelTwoFineCellGeneral.lean`), and `firstLiveLeg Leg.Z = Leg.X`, so the
degree hypothesis above holds by `rfl`.  This is the one cell of the fifteen whose zero coordinate
sits on the split leg `Z`, hence the one cell the uniform route of image 94 excludes. -/

/-- **The `(2,2,0)` fine cell has an even one-slice exponent.** -/
theorem dwz63_even_cellOnes_twoTwoZero (n : ℕ) (α : PositiveWord CWBlock 1 → ℕ)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
        (dwz63ZeroCellTarget Leg.Z 2 n)).support) :
    Even (dwz63CellOnes Leg.Z n s) :=
  dwz63_even_cellOnes_of_target_two K q Leg.Z n α (dwz63ZeroCellTarget Leg.Z 2 n) rfl s hs

/-- **The `(2,2,0)` halved value set.** -/
theorem dwz63_cellOnes_twoTwoZero_div_two_mem_range (n : ℕ) (α : PositiveWord CWBlock 1 → ℕ)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
        (dwz63ZeroCellTarget Leg.Z 2 n)).support) :
    dwz63CellOnes Leg.Z n s / 2 ∈ Finset.range (n + 1 + 1) :=
  dwz63_cellOnes_div_two_mem_range_of_target_two K q Leg.Z n α (dwz63ZeroCellTarget Leg.Z 2 n) rfl
    s hs

/-- **The `(2,2,0)` halving identity.** -/
theorem dwz63_two_mul_cellOnes_twoTwoZero_div_two (n : ℕ) (α : PositiveWord CWBlock 1 → ℕ)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
        (dwz63ZeroCellTarget Leg.Z 2 n)).support) :
    2 * (dwz63CellOnes Leg.Z n s / 2) = dwz63CellOnes Leg.Z n s :=
  dwz63_two_mul_cellOnes_div_two_of_target_two K q Leg.Z n α (dwz63ZeroCellTarget Leg.Z 2 n) rfl
    s hs

end AlgebraicComplexity.Examples
