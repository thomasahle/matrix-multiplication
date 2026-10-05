/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetRepair
import AxiomAudit.Command

/-!
# Axiom audit: the recursive approximate repair-API instantiation

Every public declaration of
`AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetRepair` is asserted
here to depend on no axiom beyond the ambient logical ones.  In particular the uniform
structure-relabeling family and the sparse cardinality bound remain explicit hypotheses of the
audited statements rather than assumptions of the development.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwRecursiveApproximateSparseRetainedCoarse
#assert_axioms mem_cwRecursiveApproximateSparseRetainedCoarse_iff
#assert_axioms cwRecursiveApproximateSparseRetainedCoarse_eq_sparseIndices
#assert_axioms cwRecursiveApproximateGroupedFibers_restricts_retained
#assert_axioms exists_cwRecursiveApproximateTarget_repairPlans_of_sparse_count
#assert_axioms cwRecursiveApproximateGroupedFibers_restricts_repairedTargetCopies
#assert_axioms cwRecursiveApproximate_orientedGroupedCleanup_withRepairedTargetCopies
