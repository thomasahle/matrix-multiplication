import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibilityPushforward

/-!
# Axiom audit for finite feature pushforward identities

This module checks the reusable bridges between joint-word, cell-multiplicity, and finite
alphabet-pushforward formulations.
-/

open AlgebraicComplexity MoreAsymmetryCompatibility

#assert_axioms multiplicity_jointWord_eq_cellMultiplicity
#assert_axioms cellMultiplicity_subtype_val
#assert_axioms cellMultiplicity_comp_eq_mappedType
