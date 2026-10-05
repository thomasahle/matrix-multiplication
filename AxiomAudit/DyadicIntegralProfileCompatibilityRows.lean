/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DyadicIntegralProfileCompatibilityRows

/-!
# Axiom audit for division-free integral-profile compatibility rows
-/

#assert_axioms
  AlgebraicComplexity.CompatibleSplit.SplitRequirements.sum_boundaryRows_eq
#assert_axioms
  AlgebraicComplexity.CompatibleSplit.SplitRequirements.sum_groupRows_eq
#assert_axioms
  AlgebraicComplexity.CompatibleSplit.SplitRequirements.subtractedEntropy_eq_rowEntropyMass
#assert_axioms
  AlgebraicComplexity.CompatibleSplit.SplitRequirements.canonicalCompatibilityRows_rate
