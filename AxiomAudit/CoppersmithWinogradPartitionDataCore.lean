/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradPartitionDataCore
import AxiomAudit.Command

/-! Axiom audit for exact finite CW partition data. -/

open AlgebraicComplexity.Examples

#assert_axioms cwBlockBasis_apply
#assert_axioms cwPartitionConstituent_ofLegs
#assert_axioms cwPartitionedTensor_constituent
