/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellPower
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellPowerSupport

set_option autoImplicit false

/-!
# `huniform` away from degree two

Layer 4 (`AlgebraicComplexity/Examples/`).  The one-slice fusion needs the exponent
`dwz63CellOnes` to be **constant** on the fibre, so that `mergedDimension` collapses to
`|fibre| * q ^ k`.  For `[DuanWuZhou2022]` section 6.3 that constancy has three different sources,
and this module supplies the two that need no split profile at all.

## The middle count is pinned by the coarse degree, except at degree two

A fine letter is a pair of level-one blocks, and its coarse degree on a leg is the sum of the two
level-one degrees there.  Counting middle digits on that leg:

| coarse degree | admissible pairs | middles |
|---|---|---|
| `0` | `(0,0)` | `0` |
| `1` | `(0,1) (1,0)` | `1` |
| `2` | `(0,2) (1,1) (2,0)` | `0` or `2` |
| `3` | `(1,2) (2,1)` | `1` |
| `4` | `(2,2)` | `0` |

So the count is a function of the degree **except at degree `2`**, which is exactly where
`[DuanWuZhou2022]` has to prescribe a split distribution `alphatilde` at all.  That is the formal
reason the split parameters `a` and `b` attach to the `k = 2` components and nowhere else
(`hole_lemma.tex:7`: "we are only restricting the `Z`-split distribution of those `T_{i,j,k}`'s
with `k = 2`").

Consequently the six `(0,1,3)`-type cells (degree `1` or `3` on the counted leg) and the three
corners (degree `0` or `4`) get `huniform` for free, with no reference to `alphatilde`.  The
`(0,2,2)`-type cells, where the count genuinely varies, are the ones whose uniformity comes from
the profile pinning the multiplicities.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-- **The middle count of a fine letter, in closed form.**  A fine letter is a pair, so its middle
count is the sum of the two digit indicators. -/
theorem cwWordMiddleCount_pair (a b : CWBlock) :
    cwWordMiddleCount 1 ((a, b) : PositiveWord CWBlock 1) =
      (if cwBlockDigit a = (1 : SplitDigit) then 1 else 0) +
        (if cwBlockDigit b = (1 : SplitDigit) then 1 else 0) := by
  unfold cwWordMiddleCount
  rw [Fin.sum_univ_two]
  rfl

/-- **Away from degree two, the middle count is a function of the coarse degree.**  Degrees `1` and
`3` force exactly one middle digit; degrees `0` and `4` force none. -/
theorem cwWordMiddleCount_of_degree_ne_two (p : PositiveWord CWBlock 1)
    (hne : cwSquareBlockDegree p ≠ 2) :
    cwWordMiddleCount 1 p =
      (if cwSquareBlockDegree p = 1 ∨ cwSquareBlockDegree p = 3 then 1 else 0) := by
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;>
    simp_all [cwWordMiddleCount_pair, cwSquareBlockDegree, cwBlockDegree, cwBlockDigit,
      Fin.ext_iff]

variable (K : Type u) [CommRing K] (q : ℕ)

/-- **`huniform` from a letterwise constant.**  If every letter of a supported word has the same
first-live-leg middle count, the whole word's exponent is that constant times the number of
positions.  `PositiveWord … m` carries `m + 1` letters, so the factor is `m + 1`. -/
theorem dwz63_cellOnes_of_letterwise_const (zero : Leg) (m k₀ : ℕ)
    (w : PositiveWord ((cwPartitionedTensor K q).positivePower 1).support m)
    (hconst : ∀ position,
      cwWordMiddleCount 1
        ((positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support m w position).1
          (firstLiveLeg zero)) = k₀) :
    dwz63CellOnes zero m
        (positiveSupportWordBlockAddress
          ((cwPartitionedTensor K q).positivePower 1).support m w) =
      k₀ * (m + 1) := by
  unfold dwz63CellOnes
  have hrw : ∀ position,
      cwWordMiddleCount 1
          (positiveWordEquiv (PositiveWord CWBlock 1) m
            (positiveSupportWordBlockAddress
              ((cwPartitionedTensor K q).positivePower 1).support m w (firstLiveLeg zero))
            position) = k₀ := by
    intro position
    rw [show positiveWordEquiv (PositiveWord CWBlock 1) m
        (positiveSupportWordBlockAddress
          ((cwPartitionedTensor K q).positivePower 1).support m w (firstLiveLeg zero))
        position =
      (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support m w position).1
        (firstLiveLeg zero) from
      congrFun
        (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
          ((cwPartitionedTensor K q).positivePower 1).support m w (firstLiveLeg zero)) position]
    exact hconst position
  rw [Finset.sum_congr rfl (fun position _ ↦ hrw position)]
  simp [Finset.sum_const, mul_comm]

end AlgebraicComplexity.Examples
