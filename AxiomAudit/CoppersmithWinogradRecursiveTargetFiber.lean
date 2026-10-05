import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetFiber
import AxiomAudit.Command

open AlgebraicComplexity AlgebraicComplexity.Examples

/-! Focused trust audit for `AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetFiber`:
transport of the exact recursive CW target alphabet and of the oriented coarse index sequence
under a common parent-position permutation, together with the containment of a cleaned fiber's
parts in that exact target. -/

#assert_axioms cwRecursiveChildCompatibilityModel_coarse_eq_orientedSequence
#assert_axioms positiveWordLabelledChildren_positionRelabel_eq_comp
#assert_axioms cwRecursiveOrientedCoarseIndexSequence_positionRelabel
#assert_axioms cwRecursiveExactTargetFiberParts_positionRelabel
#assert_axioms cwRecursiveCleanedFiberParts_subset_exactTarget
