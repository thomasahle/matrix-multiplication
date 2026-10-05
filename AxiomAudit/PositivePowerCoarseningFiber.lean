/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PositivePowerCoarseningFiber

set_option autoImplicit false

/-!
# Axiom audit for whole positive-power coarsening fibers

This companion enforces the trust boundary for the exact product identity and the canonical
realization isomorphisms in `Tensor.PositivePowerCoarseningFiber`.
-/

#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.coarseningFiber_external
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.positivePower_coarseningFiber_positiveWordTensor_of_word
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.positivePower_coarseningFiber_positiveWordTensor
