/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedRegionalOneSegmentBridge

/-! # Axiom audit for the region / one-segment-leaf identification

A region of the fifteen-segment leaf is the one-segment leaf the per-cell weights are proved
about, and a weight is a `sym₆`-weight at the sixth power.

Primary source: `[duan2023faster]`, section 6.3 (the level-two global-value example),
`papers/sources/2210.10173/global_value.tex:332-348`; the restricted-splitting values `V^{(6)}`
and `V^{(3)}` are defined at `papers/sources/2210.10173/prelim.tex:342-363`. -/

set_option autoImplicit false

#assert_axioms
  AlgebraicComplexity.Tensor.PartitionedTensor.segmentedLocalizedSplittingPower_congr_keeps
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.keeps_ofLeg_ite_const_iff
#assert_axioms AlgebraicComplexity.SegmentedSplitRestriction.keeps_ofLeg_one_iff
#assert_axioms AlgebraicComplexity.segmentedLocalizedSplittingPower_constSeg_eq_oneSegment
#assert_axioms AlgebraicComplexity.HasTauWeight.symSix_pow_six
#assert_axioms AlgebraicComplexity.hasTauWeight_symSix_region_of_oneSegment
