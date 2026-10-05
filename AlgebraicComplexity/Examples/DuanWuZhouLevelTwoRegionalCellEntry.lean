/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedRegionalAssembly
import AlgebraicComplexity.MatrixMultiplication.SegmentedRegionalOneSegmentBridge
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoRegionalTarget

set_option autoImplicit false

/-!
# One weighed cell, as a region entry

Layer 4 (`AlgebraicComplexity/Examples/`).  The per-cell lanes prove weights for the **one-segment**
leaf at the zero-coordinate coarse target `dwz63ZeroCellTarget zero k n`
(`Examples/DuanWuZhouLevelTwoFineCellJoined.lean` for the joined period,
`Examples/DuanWuZhouLevelTwoFineCellTwoTwoZero.lean` for row `11`).  The assembly
(`MatrixMultiplication/SegmentedRegionalAssembly.lean`) asks for a `sym₆`-weight of a **region**
of the fifteen-segment leaf, at the uniform coarse target `dwz63CellTarget`.

This module is the one adapter between them.  It is deliberately stated on an arbitrary weight
rather than on any particular cell's theorem, so each of the twelve proved cells --- and the three
orbit rows when their interface lands --- is one application, and nothing here has to change when a
cell is restated at a different period or with a different deficit.

Both steps are already proved: `segmentedLocalizedSplittingPower_constSeg_eq_oneSegment` says a
region *is* the one-segment leaf (an equation) and `HasTauWeight.symSix_pow_six` pays for
`V^{(6)}`.  The `htarget` premise identifies the two spellings of the coarse target; Table 2 has
twelve zero-coordinate rows, eleven of them supplied by the `dwz63CellTarget_*` instances of
`Examples/DuanWuZhouLevelTwoRegionalTarget.lean` and the twelfth, row `11`, by
`dwz63CellTarget_eleven` in `Examples/DuanWuZhouLevelTwoRegionalCells.lean`.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.3 (the level-two global-value
example), `papers/sources/2210.10173/global_value.tex:332-348`; Table 2 is
`papers/sources/2210.10173/global_value.tex:354-378`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]

/-- **A one-segment cell weight is a region entry at the uniform coarse spelling.**

`h` is exactly what the per-cell lanes prove; the conclusion is exactly what
`segmentedRegionalSymSixWeights_of_letterwise` consumes for the region labelled `t₀` sitting
inside cell `t`.  The `htarget` premise is one of the twelve zero-coordinate `dwz63CellTarget_*`
identities --- eleven in `Examples/DuanWuZhouLevelTwoRegionalTarget.lean` and
`dwz63CellTarget_eleven` for row `11`; the three orbit rows enter instead through the checked bridge
`dwz63CellTarget_orbit`, not through this adapter.

Proof sketch: two rewrites and nothing else.  `htarget` replaces the uniform coarse spelling
`dwz63CellTarget t n` by the zero-coordinate spelling `dwz63ZeroCellTarget zero k n` that `h` is
stated at, and `hasTauWeight_symSix_region_of_oneSegment` then does the two committed steps: the
region of the `M`-segment leaf at the constant segmentation `t₀` *is* the one-segment leaf
(`segmentedLocalizedSplittingPower_constSeg_eq_oneSegment`, an equation, so no restriction and no
loss), and `HasTauWeight.symSix_pow_six` --- `symThree_pow_three` composed with `symSix_pow_two`
--- raises the weight to the sixth power, which is the `V^{(6)}` the section 6.3 endpoint asks
for.  The nonnegativity `hvalue` is what the sixth-power step needs. -/
theorem dwz63_symSixRegionEntry_of_oneSegmentWeight {M : ℕ} (t₀ : Fin M) (t : Fin 15)
    (zero : Leg) (k : Fin 5) (n : ℕ) (α : PositiveWord CWBlock 1 → ℕ) (value : ℝ)
    (hvalue : 0 ≤ value)
    (htarget : dwz63CellTarget t n = dwz63ZeroCellTarget zero k n)
    (h : HasTauWeight K
      ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α))
        (dwz63ZeroCellTarget zero k n)).realize) dwz63Tau value) :
    HasTauWeight K
      (symSix K ((((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n M (fun _ ↦ t₀)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
          (fun t' ↦ if t' = t₀ then α else 0))
        (dwz63CellTarget t n)).realize)) dwz63Tau (value ^ 6) := by
  rw [htarget]
  exact hasTauWeight_symSix_region_of_oneSegment
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n M Leg.Z t₀ α
    (dwz63ZeroCellTarget zero k n) h hvalue

end AlgebraicComplexity.Examples
