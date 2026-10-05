/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetModel
import AxiomAudit.Command

/-!
# Axiom audit: recursive approximate cleanup fibers as a modeled damaged-box family

Every public declaration of
`AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetModel` is asserted
here to depend on no axiom beyond the ambient logical ones.  The module under audit is mechanical
packaging: it proves no count and constructs no relabeling family.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwRecursiveApproximateRetainedCoarseSupport
#assert_axioms mem_cwRecursiveApproximateRetainedCoarseSupport_iff
#assert_axioms cwRecursiveApproximateRetainedCoarse_mem_coarseKept
#assert_axioms cwRecursiveApproximateRetainedCoarse_mem_relaxedAmbient
#assert_axioms cwRecursiveApproximateRetainedCoarse_sameTaggedMultiplicity
#assert_axioms cwRecursiveApproximateCleanedFiberHoles
#assert_axioms univ_sdiff_cwRecursiveApproximateCleanedFiberHoles
#assert_axioms cwRecursiveApproximateCleanedFiber_restricts_compactHoleBox
#assert_axioms cwRecursiveApproximateTargetCleanedModel
