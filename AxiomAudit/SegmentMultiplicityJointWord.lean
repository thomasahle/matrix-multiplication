/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentMultiplicityJointWord

set_option autoImplicit false

/-! # Axiom audit for the joint-word/segment-multiplicity bridge

The spelling bridge consumed by the transcription of `lemma:triple_implies_compatible` of
`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:44-71`. -/

#assert_axioms AlgebraicComplexity.multiplicity_jointWord_eq_segmentMultiplicity
