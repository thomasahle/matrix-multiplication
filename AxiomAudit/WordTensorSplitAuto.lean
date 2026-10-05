/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.WordTensorSplitAuto

set_option autoImplicit false

/-! # Axiom audit for the word-split multiplicity side condition -/

#assert_axioms AlgebraicComplexity.multiplicity_eq_sum_ite
#assert_axioms AlgebraicComplexity.hasTauWeight_wordTensor_split_of_multiplicity
