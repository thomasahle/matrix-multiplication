/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetRepairClient

/-!
# Axiom audit for the recursive approximate-repair relabeling client

The assertion covers the high-level cleanup-and-repair specialization whose recursive target
structure relabelings are constructed from the kernel-checked parent/child chunk-power lift.
-/

#assert_axioms
  AlgebraicComplexity.Examples.cwRecursiveApproximate_orientedGroupedCleanup_withRepairedTargetCopies_of_supportedTargets
