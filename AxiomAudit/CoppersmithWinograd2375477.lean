/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.CoppersmithWinograd2375477Arithmetic
import AxiomAudit.CoppersmithWinogradSquareTauValue
import AlgebraicComplexity.Examples.CoppersmithWinograd2375477

/-!
# Axiom audit for Coppersmith--Winograd's `ω < 2.375477`

The imported square-value audit checks the full finite extraction and soundness spine.  This file
adds the sharp profile identities, strict stable-value comparison, and final historical endpoint.
-/

#assert_axioms AlgebraicComplexity.Examples.log_cwSquareOuterEntropyBase
#assert_axioms AlgebraicComplexity.Examples.log_cw112SymmetricMarginalEntropyBase
#assert_axioms AlgebraicComplexity.Examples.cwSquare2375477D_eq
#assert_axioms AlgebraicComplexity.Examples.cwSquare2375477Stride_eq
#assert_axioms AlgebraicComplexity.Examples.log_cwSquare2375477OuterEntropyBase
#assert_axioms AlgebraicComplexity.Examples.log_cwSquare2375477InnerEntropyBase
#assert_axioms AlgebraicComplexity.Examples.log_cwSquare2375477OrdinaryVolume
#assert_axioms AlgebraicComplexity.Examples.log_cwSquare2375477InnerDimensionVolume
#assert_axioms AlgebraicComplexity.Examples.scaled_log_cwSquare2375477InnerTerm
#assert_axioms AlgebraicComplexity.Examples.cwSquare2375477_log_sufficient
#assert_axioms AlgebraicComplexity.Examples.cwSquare2375477_stable_value_gt_64
#assert_axioms AlgebraicComplexity.Examples.coppersmithWinograd_square_omega_lt_2375477
