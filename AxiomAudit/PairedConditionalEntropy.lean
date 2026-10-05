/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.PairedConditionalEntropy

/-!
# Axiom audit for paired conditional entropy

This focused audit checks the lightweight finite-law inequality
`H(D, E | C, F) ≤ H(D | C) + H(E | F)`.
-/

set_option autoImplicit false

open AlgebraicComplexity

#assert_axioms ProbabilityVector.IsCoupling.pairConditionalEntropyBits_le_add
