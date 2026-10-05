/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.TauValueCyclicSoundness

/-!
# Axiom audit for cyclic `τ`-value soundness

This focused audit checks the explicit bridge from a symmetrized three-orientation degeneration
certificate to an ordinary value certificate and the resulting strict bound on `omega`. Ordinary
Schönhage soundness is audited separately in `AxiomAudit/TauValueSoundness.lean`.
-/

#assert_axioms AlgebraicComplexity.CyclicDegenerationCertificate.toTauValueCertificate
#assert_axioms AlgebraicComplexity.omega_lt_three_mul_of_cyclicDegenerationCertificate
