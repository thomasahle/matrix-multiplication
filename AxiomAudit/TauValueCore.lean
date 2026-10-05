/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.TauValueCore

/-!
# Axiom audit for the finite `τ`-value certificate calculus

This focused audit intentionally imports only `TauValueCore`. It checks the finite term, semantic
degeneration adapter, direct-sum embeddings, matrix-multiplication normalization, and divisible
power law without loading Schönhage's inequality or any theorem about `omega`.
-/

#assert_axioms AlgebraicComplexity.matrixMultiplicationVolumePowerSum_pos
#assert_axioms AlgebraicComplexity.tauValueTerm_mono_exponent
#assert_axioms AlgebraicComplexity.TauValueCertificate.ofPolynomialDegenerates
#assert_axioms AlgebraicComplexity.tauValue_le_of_polynomialDegenerates
#assert_axioms AlgebraicComplexity.TauValueCertificate.directSumLeft
#assert_axioms AlgebraicComplexity.TauValueCertificate.directSumRight
#assert_axioms AlgebraicComplexity.TauValueCertificate.matrixMultiplication
#assert_axioms AlgebraicComplexity.TauValueCertificate.term_matrixMultiplication
#assert_axioms AlgebraicComplexity.TauValueCertificate.powerDvd
#assert_axioms AlgebraicComplexity.TauValueCertificate.term_powerDvd
