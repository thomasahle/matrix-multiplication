/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentMultiplicityReflect

set_option autoImplicit false

/-! # Axiom audit for the segment-distribution reflection

`[duan2023faster]`, `global_value.tex:70`. -/

#assert_axioms AlgebraicComplexity.segmentMultiplicity_comp_involutive
