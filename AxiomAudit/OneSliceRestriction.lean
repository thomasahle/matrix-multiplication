import AlgebraicComplexity.MatrixMultiplication.OneSliceRestriction
import AxiomAudit.Command

/-!
# Axiom audit for explicit one-slice restrictions

Checks the map-level one-slice constructors and shared-`Z` coherence.
-/

open AlgebraicComplexity AlgebraicComplexity.Tensor

#assert_axioms OneSliceRestriction.self
#assert_axioms OneSliceRestriction.castDimension
#assert_axioms OneSliceRestriction.external
#assert_axioms OneSliceRestriction.external_legMap_Z_congr
#assert_axioms OneSliceRestriction.self_external_map_eq
