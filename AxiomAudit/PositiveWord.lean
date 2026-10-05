/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PositiveWord
import AlgebraicComplexity.Tensor.PositiveWordConst
import AxiomAudit.Command

/-!
# Axiom audit for recursively represented positive words

The definition-only word layer is intentionally independent of tensor algebra and project
axioms.  These checks protect that lightweight dependency boundary.
-/

#assert_axioms AlgebraicComplexity.Tensor.PositiveWord
#assert_axioms AlgebraicComplexity.Tensor.positiveWordConst
#assert_axioms AlgebraicComplexity.Tensor.positiveWordEquiv_zero_apply
#assert_axioms AlgebraicComplexity.Tensor.positiveWordEquiv_succ_apply
#assert_axioms AlgebraicComplexity.Tensor.positiveWordFintype
#assert_axioms AlgebraicComplexity.Tensor.positiveWordNonempty
#assert_axioms AlgebraicComplexity.Tensor.positiveWordDecidableEq
