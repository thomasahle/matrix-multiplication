/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.CyclicProductPowerCoherence

/-!
# Axiom audit for tensor-only cyclic-product power coherence

This audit is deliberately below every laser-rate, value, and Schönhage soundness module.
-/

#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.cyclicPowerProduct_congr
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.cyclicPowerProduct_positive
