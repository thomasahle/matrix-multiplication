/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.UniversalSliceRankBarrier

set_option autoImplicit false

/-!
# Axiom audit for the unconditional asymptotic-slice-rank barrier

Focused trust audit for the `Unconditional` section of
`AlgebraicComplexity/MatrixMultiplication/UniversalSliceRankBarrier.lean`, which restates
Theorem 5.1 of J. Alman, *Limits on the Universal Method for Matrix Multiplication*, PhD thesis,
MIT, 2019 (see also CCC 2019), without the packaged hypothesis
`Tensor.SliceRankDegenerationMonotone`.

The umbrella audit asserts the three `Barrier`-section forms, each of which still takes that
proposition as an explicit binder for source compatibility.  The primed form asserted here is the
one the `README.md` Results row credits for the row's "unconditional over any field" status; it
discharges the binder through `Tensor.sliceRankDegenerationMonotone_holds`, audited in
`AxiomAudit/SliceRankDegeneration.lean`.
-/

namespace AlgebraicComplexity

#assert_axioms two_mul_log_asymptoticRank_div_log_asymptoticSliceRank_le_universalExponent'

end AlgebraicComplexity
