/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SymSixUniformLeaf

set_option autoImplicit false

/-! # Axiom audit for the uniform-leaf stage bridge -/

#assert_axioms AlgebraicComplexity.Tensor.Restricts.symThree_congr
#assert_axioms AlgebraicComplexity.Tensor.Restricts.symSix_congr
#assert_axioms AlgebraicComplexity.restricts_power_symSix_of_plainStage
