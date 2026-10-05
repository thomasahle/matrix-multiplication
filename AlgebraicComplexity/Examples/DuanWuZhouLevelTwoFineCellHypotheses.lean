/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellPowerSupport
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellBridge

set_option autoImplicit false

/-!
# The two fusion hypotheses, read off the one-segment localized power

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/DuanWuZhouLevelTwoFineCellFusion.lean` fuses one cell of the `[duan2023faster]` section
6.3 fine leaf from exactly two hypotheses about its supported addresses --- trivial on the zero leg
(`hz`), and constant one-slice exponent (`huniform`).  This module discharges both against the
*support characterisation* `dwz63_mem_cellPower_support_iff`, so a client of the fusion supplies
only the cell's coarse data: which leg carries the zero coordinate, and the split profile
`alphatilde`.

## Why the shared-leg reading needs both live legs

`dwz63CellOnes zero` counts middles at `firstLiveLeg zero`, while `alphatilde` is a profile on
**`Z`** --- the leg `SegmentedSplitRestriction.ofLeg` restricts.  Those two legs coincide exactly
when `zero = .Y`, and then the exponent is the profile-weighted middle count with no further work
(`dwz63_cellOnes_eq_multiplicity_sum` below).  When `zero = .X` the profile sits at
`secondLiveLeg .X = .Z` instead, and the committed
`dwz63_cellOnes_eq_alphaTilde_sum` (`Examples/DuanWuZhouLevelTwoFineCellBridge.lean`) is the route,
crossing the two live legs by `dwz63_middleCount_liveLegs_eq`.  The remaining case `zero = .Z` is
`(2,2,0)`, whose profile is trivial and whose exponent is genuinely **not** constant --- which is
why it is the one cell that goes through the pigeonhole
`ZeroCoordinateMerge.exists_uniform_fibre_mergedDimension_le` rather than through this module.

So the split into the two lemmas below is not duplication: it is the statement of exactly where the
section 6.3 table's three orientations of a zero coordinate differ.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## `huniform`, read at the first live leg -/

/-- **The one-slice exponent of an address whose first-live-leg word has type `α`.**

`dwz63CellOnes` is by definition an additive statistic of the word at `firstLiveLeg zero`, so this
is `WordType.sum_word_eq_sum_multiplicity_mul` with no geometry at all.  It is the reading the
cells with `zero = .Y` --- `(1,0,3)`, `(2,0,2)`, `(3,0,1)` --- need, because for them
`firstLiveLeg .Y = .Z` is the very leg `alphatilde` is a profile on. -/
theorem dwz63_cellOnes_eq_multiplicity_sum (zero : Leg) (m : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) m))
    (htype : WordType.multiplicity
      (positiveWordEquiv (PositiveWord CWBlock 1) m (s (firstLiveLeg zero))) = α) :
    dwz63CellOnes zero m s = ∑ p : PositiveWord CWBlock 1, α p * cwWordMiddleCount 1 p := by
  unfold dwz63CellOnes
  rw [WordType.sum_word_eq_sum_multiplicity_mul (cwWordMiddleCount 1)
      (positiveWordEquiv (PositiveWord CWBlock 1) m (s (firstLiveLeg zero))), htype]

/-! ## Both hypotheses, on the one-segment localized power -/

/-- **`hz` on the one-segment localized power.**  A supported address of the cell lies over the
coarse target, and the target's zero-leg word is the constant degree-zero word, so the address's
zero-leg word is the constant zero *pair* word --- which is what `dwz63_zeroLegWord_eq_const`
says. -/
theorem dwz63_cellPower_zeroLeg_eq_const (n : ℕ) (zero : Leg)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target zero = positiveWordConst (0 : Fin 5) n)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support) :
    s zero = positiveWordConst (positiveWordConst CWBlock.zero 1) n := by
  have hcoarse := ((dwz63_mem_cellPower_support_iff K q n α target s).mp hs).2.1 zero
  refine dwz63_zeroLegWord_eq_const zero n (s zero) ?_
  rw [hcoarse]
  exact htarget

/-- **`huniform` on the one-segment localized power, for a zero coordinate on `Y`.**

The `alphatilde` profile is carried on `Z`, and `firstLiveLeg .Y = .Z`, so the support condition
delivers the type on exactly the leg `dwz63CellOnes` reads.  The hypothesis `hlive` is what pins
the orientation; at `zero = .X` the committed `dwz63_cellOnes_eq_alphaTilde_sum` is the
counterpart. -/
theorem dwz63_cellPower_cellOnes_eq_alphaSum_of_firstLive (n : ℕ) (zero : Leg)
    (hlive : firstLiveLeg zero = Leg.Z)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support) :
    dwz63CellOnes zero n s = ∑ p : PositiveWord CWBlock 1, α p * cwWordMiddleCount 1 p := by
  refine dwz63_cellOnes_eq_multiplicity_sum zero n α s ?_
  rw [hlive]
  exact ((dwz63_mem_cellPower_support_iff K q n α target s).mp hs).2.2

end AlgebraicComplexity.Examples
