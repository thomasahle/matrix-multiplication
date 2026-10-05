import AlgebraicComplexity.MatrixMultiplication.OneSliceRestrictionRelation
import AxiomAudit.Command

/-!
# Axiom audit for the explicit one-slice restriction bridge

Checks the forgetful map from exposed certificates to the ordinary restriction relation.
-/

open AlgebraicComplexity AlgebraicComplexity.Tensor

#assert_axioms OneSliceRestriction.restricts
