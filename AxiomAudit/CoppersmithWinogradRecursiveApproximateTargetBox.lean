import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetBox
import AxiomAudit.Command

open AlgebraicComplexity AlgebraicComplexity.Examples

/-! Focused trust audit for
`AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateTargetBox`: the finite
semantic comparison of a cleaned recursive CW quotient fiber with a box of the full parent
positive power -- the cleaned-fiber/parent-box identity, containment of the cleaned fiber parts
in the exact target, the moved fiber parts and their restriction to the compact reference box,
and the resulting cleanup-with-target-box statement. -/

#assert_axioms cwRecursiveApproximateCleanedFiber_eq_fullParentBox_fiberParts
#assert_axioms cwRecursiveApproximateCleanedFiberParts_subset_exactTarget
#assert_axioms cwRecursiveApproximateMovedCleanedFiberParts
#assert_axioms cwRecursiveApproximateMovedCleanedFiberParts_subset_reference
#assert_axioms cwRecursiveApproximateCleanedFiber_restricts_compactFullTargetReferenceBox
#assert_axioms cwRecursiveApproximate_orientedGroupedCleanup_withTargetBox
