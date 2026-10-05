/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPairTypedLeafCleanup

/-!
# Focused axiom audit for sorted-pair cleanup to fine typed leaves

This target checks the conditional-joint-type reconstruction, constituent-level fine-leaf
projection, copy-preserving indexed bridge, and the end-to-end quotient cleanup composition.
-/

#assert_axioms AlgebraicComplexity.Examples.cwSortedPairShapeConditionalProfile
#assert_axioms AlgebraicComplexity.Examples.cwSortedPair_mem_positiveTypeClass_of_shapeConditionalProfiles
#assert_axioms AlgebraicComplexity.Examples.cwSortedPair_coarsenedPositivePower_constituent_matrixMultiplication_of_shapeConditionalProfiles
#assert_axioms AlgebraicComplexity.Examples.cwSortedPair_indexedDirectSum_coarsenedPositivePower_constituent_matrixMultiplication_of_shapeConditionalProfiles
#assert_axioms AlgebraicComplexity.Examples.cwSortedPairFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_shapeConditionalProfiles
