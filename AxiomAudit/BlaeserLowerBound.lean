/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.BlaeserLowerBound

set_option autoImplicit false

/-!
# Axiom audit for the row-kill substitution lower bound

Focused trust audit for `AlgebraicComplexity/Examples/BlaeserLowerBound.lean`, the substitution
argument giving `rank ⟨m,n,p⟩ ≥ n*p + (m-1)*n` and its square specialization `2n² - n`, the
first rung towards M. Blaeser, *A 5/2 n²-lower bound for the rank of n×n-matrix multiplication
over arbitrary fields*, FOCS 1999.

The umbrella audit asserts the kill-chain form `rank_matrixMultiplication_rowKill`, the `Y`
rotation and the square corollary.  Asserted here are the remaining two rotations and the maximum
over all three, which the `README.md` Results row names as
`matrixMultiplication_rank_lower_rowKill_max`.
-/

#assert_axioms AlgebraicComplexity.matrixMultiplication_rank_lower_rowKill_X
#assert_axioms AlgebraicComplexity.matrixMultiplication_rank_lower_rowKill_Z
#assert_axioms AlgebraicComplexity.matrixMultiplication_rank_lower_rowKill_max
