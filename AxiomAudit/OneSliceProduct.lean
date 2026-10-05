import AlgebraicComplexity.MatrixMultiplication.OneSliceProduct
import AxiomAudit.Command

/-!
# Axiom audit for the lightweight one-slice product law

Checks the explicit coordinate product map and its exact tensor identity.
-/

open AlgebraicComplexity AlgebraicComplexity.Tensor

#assert_axioms OneSliceProduct.coordinateProductMap_single
#assert_axioms OneSliceProduct.map_external_after
#assert_axioms OneSliceProduct.legMap_Z_eq
#assert_axioms OneSliceProduct.map_external_mmTerm
#assert_axioms OneSliceProduct.matrixMultiplication_eq_sum
#assert_axioms OneSliceProduct.map_external_matrixMultiplication
