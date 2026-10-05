/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedFiberIndependenceProof

/-! Focused trust audit for Claim 3 of [duan2023faster] §5 in its segmented form: the segment-wise
factorisation of the shuffle fibre and the resulting target-independent fibre count, which
discharges `SegmentedFiberIndependence`.

Exact source lines: `papers/sources/2210.10173/hole_lemma.tex:1-168` (§5).
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.segmentRestrict
#assert_axioms AlgebraicComplexity.segmentRestrict_apply
#assert_axioms AlgebraicComplexity.card_fiber_segmentRestrict
#assert_axioms AlgebraicComplexity.segmentPermToPerm_apply
#assert_axioms AlgebraicComplexity.comp_segmentPermToPerm_eq_iff
#assert_axioms AlgebraicComplexity.segmentedAvailableWordShuffle_eq_iff
#assert_axioms AlgebraicComplexity.filter_segmentedAvailableWordShuffle_eq_piFinset
#assert_axioms AlgebraicComplexity.card_segmentedAvailableWordShuffle_fiber
#assert_axioms AlgebraicComplexity.segmentedFiberIndependence
