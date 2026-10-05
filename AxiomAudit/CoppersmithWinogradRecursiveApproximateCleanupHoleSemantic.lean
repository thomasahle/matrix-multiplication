/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateCleanupHoleSemantic

set_option autoImplicit false

/-!
# Axiom audit for recursive approximate cleanup-hole semantics

This companion audits the qualitative support and realizability boundary extracted from
[alman2025more, Claim 6.18].  The logical-`Y` and logical-`Z` compatibility/unique-triple stages
are `papers/sources/2404.16349/constituent.tex:253-276,292-326`; the corresponding Total-Weight
statements are Proposition `prop:grouped-cleanup` and the three-class damaged-box discussion in
`better_bound/paper.tex:859-898,948-1048`.
-/

open AlgebraicComplexity.Examples

#assert_axioms CWRecursiveApproximateFineLabel
#assert_axioms CWRecursiveApproximateFineAddress
#assert_axioms CWRecursiveApproximateCleanupSupportData
#assert_axioms cwRecursiveApproximateCleanupSupportData
#assert_axioms cwRecursiveApproximateCompatibilityReadySupport
#assert_axioms cwRecursiveApproximateCleanupFinalSupport_subset_ready
#assert_axioms cwRecursiveApproximateCompatibilityReady_mem_yDeleted_or_zDeleted
#assert_axioms cwRecursiveApproximateMovedReadyParts
#assert_axioms cwRecursiveApproximateReadyAddress
#assert_axioms cwRecursiveApproximateReadyAddress_spec
#assert_axioms cwRecursiveApproximateMovedCleanedFiberParts_subset_movedReady
#assert_axioms cwRecursiveApproximateMovedCleanedFiberParts_subset_movedReady_of_cleanup
#assert_axioms cwRecursiveApproximateCleanup_yAmbient_subset_fineAmbient
#assert_axioms cwRecursiveApproximateCleanup_zAmbient_subset_fineAmbient
#assert_axioms cwRecursiveApproximateSourceNonrealizableHoles
