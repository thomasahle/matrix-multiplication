/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.SliceRankDegeneration

set_option autoImplicit false

/-!
# Axiom audit for slice-rank monotonicity under polynomial degeneration

Focused trust audit for the `Statement` section of
`AlgebraicComplexity/Tensor/SliceRankDegeneration.lean`, which packages Proposition 5.1 of
J. Alman, *Limits on the Universal Method for Matrix Multiplication*, PhD thesis, MIT, 2019
(quoting Corollary 2 of T. Tao and W. Sawin, *Notes on the "slice rank" of tensors*, blog post,
2016) as a proposition and discharges it over every field.

The umbrella audit asserts the certificate-level lemmas of the same module and the
`sliceRank_le_of_polynomialDegeneratesAt_zero` special case.  Asserted here are the three
declarations the `README.md` Results row for the saturation step names from this module: the
discharged proposition itself, and the finite and asymptotic monotonicity statements it yields.
Every barrier endpoint that calls itself unconditional passes through `..._holds`.
-/

namespace AlgebraicComplexity.Tensor

#assert_axioms sliceRankDegenerationMonotone_holds
#assert_axioms sliceRank_polynomialDegenerates_le
#assert_axioms asymptoticSliceRank_polynomialDegenerates_le

end AlgebraicComplexity.Tensor
