/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.TotalQuotientNormalizedCompression

/-!
# Certificate axiom audit for the total-weight quotient's emitter identity

These assertions reach the generated `e7987d7f…` total-weight quotient scalar data (all 34
`Generated/TotalQuotientExponentScalar*` modules), so they live in the opt-in certificate audit
target rather than the ordinary focused one.  They cover the reading of the chunked committed
payload as one signed log-linear form over the global mantissa index, the positivity of every
committed mantissa, the two chunk reindexings, the seam with the emitter identity discharged, the
rational entry point, and the chunked assembly of the two coefficient-family identities.
-/

#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.positiveArgumentNat_pos
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.negativeArgumentNat_pos
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.positiveArgument_pos
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.negativeArgument_pos
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.positiveExactSum_eq_sum
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.negativeExactSum_eq_sum
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.retainedExponentLowerWitness_eq_exactValue
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.retainedCompressionSeam_of_normalizedChordTangentCompression
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.mass_eq_ratCast
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.retainedCompressionSeam_of_rationalNormalizedChordTangentCompression
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.positiveWeight_eq_of_chunks
#assert_axioms MatrixMultiplication.TotalQuotientNormalizedCompression.negativeWeight_eq_of_chunks
