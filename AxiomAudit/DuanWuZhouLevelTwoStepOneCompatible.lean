/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCompatible

set_option autoImplicit false

/-! # Axiom audit for the inputs of `lemma:triple_implies_compatible`

`[duan2023faster]`, `global_value.tex:32, 63-71`. -/

#assert_axioms AlgebraicComplexity.Examples.cwBlock_eq_complement_of_zeroX
#assert_axioms AlgebraicComplexity.Examples.cwSquareComplementLetter_involutive
#assert_axioms AlgebraicComplexity.Examples.cwSquare_fineY_eq_complement_of_zeroX
#assert_axioms AlgebraicComplexity.Examples.dwz63_coarseDegree_at_position
