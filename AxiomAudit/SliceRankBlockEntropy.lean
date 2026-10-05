/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.SliceRankBlockEntropy

set_option autoImplicit false

/-!
# Axiom audit for the block-partition entropy bound on `S̃`

Focused trust audit for `AlgebraicComplexity/Tensor/SliceRankBlockEntropy.lean`, which proves
Theorem 5.3 (Section 5.3.2) of J. Alman, *Limits on the Universal Method for Matrix
Multiplication*, PhD thesis, MIT, 2019, for the asymptotic slice rank `S̃`.

The umbrella audit asserts the entropy endpoint
`asymptoticSliceRank_coordinateTensor_le_of_blockEntropy` and both `Ī` twins of the two lemmas
below.  Asserted here are the remaining two declarations the `README.md` Results row for the
`S̃` form of Theorem 5.3 names: the fiber-count bound and the subexponential-loss transfer.
-/

namespace AlgebraicComplexity.Tensor

#assert_axioms asymptoticSliceRank_coordinateTensor_le_sum_blockFiberCard
#assert_axioms asymptoticSliceRank_le_of_subexponential_mul_pow

end AlgebraicComplexity.Tensor
