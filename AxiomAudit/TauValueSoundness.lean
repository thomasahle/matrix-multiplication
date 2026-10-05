/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.TauValueSoundness

/-!
# Axiom audit for `τ`-value soundness

This focused audit covers the analytic half of the value API: Schönhage's certificate-level bound,
boundedness in the critical regime, the strict ordinary value-to-exponent implications, and the
Strassen direction regression. Finite certificate construction is audited in
`AxiomAudit/TauValueCore.lean`; the cyclic adapter is audited in
`AxiomAudit/TauValueCyclicSoundness.lean`.
-/

#assert_axioms AlgebraicComplexity.TauValueCertificate.volumePowerSum_le_asymptoticRank_power
#assert_axioms AlgebraicComplexity.TauValueCertificate.term_le_asymptoticRank
#assert_axioms AlgebraicComplexity.tauValueValues_bddAbove
#assert_axioms AlgebraicComplexity.omega_lt_three_mul_of_certificate
#assert_axioms AlgebraicComplexity.omega_le_three_mul_of_certificate
#assert_axioms AlgebraicComplexity.omega_lt_three_mul_of_borderRankLE
#assert_axioms AlgebraicComplexity.omega_lt_three_mul_of_lt_tauValue
#assert_axioms AlgebraicComplexity.omega_lt_three_mul_of_approximate_certificates
#assert_axioms AlgebraicComplexity.omega_le_log_seven_div_log_two_of_tauValue_borderRankLE
