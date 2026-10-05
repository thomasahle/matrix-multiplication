import AlgebraicComplexity.MatrixMultiplication.OneSliceCTensor
import AxiomAudit.Command

/-!
# Axiom audit for the one-slice C-tensor bridge

Checks retyping of exposed one-slice maps into the canonical C-tensor constituent family.
-/

open AlgebraicComplexity AlgebraicComplexity.Tensor

#assert_axioms OneSliceRestriction.constituentMap_Z_congr
#assert_axioms OneSliceRestriction.map_constituentMap
