import AxiomAudit.Command
import MatrixMultiplication.SignedDyadicLogRowAccumulatorDefs

/-! # Axiom audit for compact signed-log row accumulation -/

#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.accumulateEntropyTerms_eq_normalizeTerms_map
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.compactWeightedRow_eq_normalize
