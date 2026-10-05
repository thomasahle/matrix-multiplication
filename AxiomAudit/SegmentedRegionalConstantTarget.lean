/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedRegionalConstantTarget

/-! # Axiom audit for the regional pieces of a coarse target

The concatenation obligation of a regional division, discharged by proof rather than by defining
the parent target as a concatenation.

Primary source: `[duan2023faster]`, section 6.3 (the level-two global-value example),
`papers/sources/2210.10173/global_value.tex:332-348`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.regionIndexLeft
#assert_axioms AlgebraicComplexity.regionIndexRight
#assert_axioms AlgebraicComplexity.segmentationLeft_eq_comp_regionIndexLeft
#assert_axioms AlgebraicComplexity.segmentationRight_eq_comp_regionIndexRight
#assert_axioms AlgebraicComplexity.Tensor.positiveWordAppendEquiv_symm_fst_eq_const
#assert_axioms AlgebraicComplexity.Tensor.positiveWordAppendEquiv_symm_snd_eq_const
#assert_axioms AlgebraicComplexity.blockAddress_eq_append_const_of_regionConst
