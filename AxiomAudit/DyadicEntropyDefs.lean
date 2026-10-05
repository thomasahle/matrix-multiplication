/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DyadicEntropyDefs

/-! # Axiom audit for the definition-only dyadic entropy leaf -/

#assert_axioms MatrixMultiplication.DyadicEntropy.mass
#assert_axioms MatrixMultiplication.DyadicEntropy.entropyTerm
