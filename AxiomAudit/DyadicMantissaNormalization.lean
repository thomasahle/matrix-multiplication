import AxiomAudit.Command
import MatrixMultiplication.DyadicMantissaNormalization

/-! Focused trust audit for the odd-mantissa normalization of a signed log-linear form — the
certificate exporter's `normalize_power_of_two_factors` step, proved as an exact identity.  No
generated certificate data is reached from here; the seam onto the simplified certificate's
committed witness is audited by
`AxiomAuditCertificate/SimplifiedRetainedCompressionSeam.lean`. -/

#assert_axioms MatrixMultiplication.LogLinearCompression.sum_fiberSum_mul
#assert_axioms MatrixMultiplication.LogLinearCompression.sum_weighted_logTwo_eq_valuationShift_add_fiberSum
#assert_axioms MatrixMultiplication.LogLinearCompression.exactValue_eq_normalized
#assert_axioms MatrixMultiplication.LogLinearCompression.chordTangentCore_eq_exactValue
#assert_axioms MatrixMultiplication.LogLinearCompression.chordTangentValue_eq_normalized
