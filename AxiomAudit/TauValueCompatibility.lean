/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.TauValue

/-!
# Compatibility audit for the historical `TauValue` umbrella

The implementation is split into narrow finite, structural, ordinary-soundness, and cyclic-
soundness leaves.  This audit imports the historical public path and names one endpoint from each
major tier, preventing a future import cleanup from silently dropping part of the API.
-/

#assert_axioms AlgebraicComplexity.TauValueCertificate.ofPolynomialDegenerates
#assert_axioms AlgebraicComplexity.mul_tauValue_le_tauValue_external
#assert_axioms AlgebraicComplexity.tauValue_pow_le_tauValue_power
#assert_axioms AlgebraicComplexity.tauValue_add_le_tauValue_directSum
#assert_axioms AlgebraicComplexity.omega_lt_three_mul_of_certificate
#assert_axioms AlgebraicComplexity.omega_lt_three_mul_of_cyclicDegenerationCertificate
