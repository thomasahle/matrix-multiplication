/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.WordTensorReindex

set_option autoImplicit false

/-! # Axiom audit for word-tensor splitting and reordering -/

#assert_axioms AlgebraicComplexity.hasTauWeight_wordTensor_append
#assert_axioms AlgebraicComplexity.hasTauWeight_wordTensor_append_three
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.positiveSupportWordTensor_of_same_type
#assert_axioms AlgebraicComplexity.hasTauWeight_wordTensor_of_sameType
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.positiveSupportWordTensor_split
#assert_axioms AlgebraicComplexity.hasTauWeight_wordTensor_split
