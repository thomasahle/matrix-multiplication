/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.DirectSumPowerCoherence

/-!
# Axiom audit for direct-sum-power coherence

This focused audit checks the tensor-only structural laws shared by the asymptotic-rank and finite
value proofs. In particular, it does not import either consumer merely to audit their common
reassociation and distributivity layer.
-/

#assert_axioms AlgebraicComplexity.Tensor.map_external_directSum
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.external_assoc
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.external_assoc_symm
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.external_swapRight
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.external_directSum
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.external_power_succ
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.externalPrefix_absorb_left
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.externalPrefix_absorb_right
