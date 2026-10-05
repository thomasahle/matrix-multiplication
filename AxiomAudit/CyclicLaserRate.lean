import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.CyclicLaserRate

/-!
# Axiom audit for the bare cyclic laser-rate interface

This focused audit covers the ordinary-to-cyclic rate normalization without importing the
subexponential volume-sequence client.  Tensor-only power coherence has its own lower audit.
-/

#assert_axioms AlgebraicComplexity.HasLaserExtractionRate.toCyclic
